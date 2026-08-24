import RequestProject.DVPSqrtTable

/-!
# Station `t = 71` of the extended Hardy ladder (rung-74)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT71 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((71 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-19347/250000 : ℚ) : ℝ))

theorem st71_c1 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((997007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193469/10000000) (δ := 41/100000000) (ψ := -19347/250000) 71 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t1 : ((996957/1000000 : ℚ) : ℝ) ≤ stT71 1 := by
  have hc : ((996957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((996957/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((996957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c2 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((280731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -609153/2500000) (δ := 557/100000000) (ψ := -19347/250000) 71 8
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t2 : ((992445466651/2500000000000 : ℚ) : ℝ) ≤ stT71 2 := by
  have hc : ((140353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((992445466651/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((140353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c3 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-223907/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837699/1250000) (δ := 63/10000000) (ψ := -19347/250000) 71 12
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t3 : ((-2585599810017/5000000000000 : ℚ) : ℝ) ≤ stT71 3 := by
  have hc : ((-447839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2585599810017/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-447839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c4 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-220127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2533347/5000000) (δ := 403/100000000) (ψ := -19347/250000) 71 16
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t4 : ((-137595027519/625000000000 : ℚ) : ℝ) ≤ stT71 4 := by
  have hc : ((-27519/62500 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137595027519/625000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-27519/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c5 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((157593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39067/125000) (δ := 649/100000000) (ψ := -19347/250000) 71 18
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t5 : ((1101039637/7812500000 : ℚ) : ℝ) ≤ stT71 5 := by
  have hc : ((4924/15625 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1101039637/7812500000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((4924/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c6 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-2311/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 407151/1000000) (δ := 119/25000000) (ψ := -19347/250000) 71 20
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t6 : ((-9442783179/400000000000 : ℚ) : ℝ) ≤ stT71 6 := by
  have hc : ((-2313/40000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9442783179/400000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-2313/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c7 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((124997/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17329/10000000) (δ := 193/50000000) (ψ := -19347/250000) 71 22
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t7 : ((472420538293/1250000000000 : ℚ) : ℝ) ≤ stT71 7 := by
  have hc : ((499963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((472420538293/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((499963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c8 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-124753/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -307871/400000) (δ := 53/12500000) (ψ := -19347/250000) 71 24
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t8 : ((-882181140379/2500000000000 : ℚ) : ℝ) ≤ stT71 8 := by
  have hc : ((-499037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-882181140379/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-499037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c9 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((540891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9993/40000) (δ := 519/100000000) (ψ := -19347/250000) 71 25
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t9 : ((1802803153053/10000000000000 : ℚ) : ℝ) ≤ stT71 9 := by
  have hc : ((540841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1802803153053/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((540841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c10 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((24511/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 495279/10000000) (δ := 33/5000000) (ψ := -19347/250000) 71 26
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t10 : ((310026474803/1000000000000 : ℚ) : ℝ) ≤ stT71 10 := by
  have hc : ((98039/100000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310026474803/1000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((98039/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c11 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((388173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213109/1250000) (δ := 491/100000000) (ψ := -19347/250000) 71 27
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t11 : ((292577520181/1250000000000 : ℚ) : ℝ) ≤ stT71 11 := by
  have hc : ((97037/125000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292577520181/1250000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((97037/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c12 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((838337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360357/2500000) (δ := 391/100000000) (ψ := -19347/250000) 71 28
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t12 : ((2419925835537/10000000000000 : ℚ) : ℝ) ≤ stT71 12 := by
  have hc : ((838287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2419925835537/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((838287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c13 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((499861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29477/5000000) (δ := 201/50000000) (ψ := -19347/250000) 71 29
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t13 : ((693147573/2500000000 : ℚ) : ℝ) ≤ stT71 13 := by
  have hc : ((124959/125000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((693147573/2500000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((124959/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c14 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((250907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2612753/10000000) (δ := 27/5000000) (ψ := -19347/250000) 71 30
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t14 : ((83813780473/625000000000 : ℚ) : ℝ) ≤ stT71 14 := by
  have hc : ((125441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83813780473/625000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((125441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c15 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-757187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6074481/10000000) (δ := 719/100000000) (ψ := -19347/250000) 71 31
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t15 : ((-1955177604393/10000000000000 : ℚ) : ℝ) ≤ stT71 15 := by
  have hc : ((-757237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1955177604393/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-757237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c16 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-2747/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2690553/5000000) (δ := 589/100000000) (ψ := -19347/250000) 71 31
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t16 : ((-27472510989/200000000000 : ℚ) : ℝ) ≤ stT71 16 := by
  have hc : ((-10989/20000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27472510989/200000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-10989/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c17 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((123121/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 434013/10000000) (δ := 439/100000000) (ψ := -19347/250000) 71 32
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t17 : ((298597097601/1250000000000 : ℚ) : ℝ) ≤ stT71 17 := by
  have hc : ((492459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298597097601/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((492459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c18 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-92451/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5128331/10000000) (δ := 81/20000000) (ψ := -19347/250000) 71 33
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t18 : ((-217932703603/2000000000000 : ℚ) : ℝ) ≤ stT71 18 := by
  have hc : ((-92461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217932703603/2000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-92461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c19 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-214953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22343/50000) (δ := 21/4000000) (ψ := -19347/250000) 71 33
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t19 : ((-246625426237/5000000000000 : ℚ) : ℝ) ≤ stT71 19 := by
  have hc : ((-215003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246625426237/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-215003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c20 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((82129/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2134803/10000000) (δ := 253/50000000) (ψ := -19347/250000) 71 34
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t20 : ((734527884897/5000000000000 : ℚ) : ℝ) ≤ stT71 20 := by
  have hc : ((328491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734527884897/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((328491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c21 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-215523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6525451/10000000) (δ := 467/100000000) (ψ := -19347/250000) 71 34
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t21 : ((-940674083709/5000000000000 : ℚ) : ℝ) ≤ stT71 21 := by
  have hc : ((-431071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-940674083709/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-431071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c22 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((932297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -925209/10000000) (δ := 377/100000000) (ψ := -19347/250000) 71 35
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t22 : ((1987557129729/10000000000000 : ℚ) : ℝ) ≤ stT71 22 := by
  have hc : ((932247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1987557129729/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((932247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c23 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-937437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3482489/5000000) (δ := 159/25000000) (ψ := -19347/250000) 71 35
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t23 : ((-390959266123/2000000000000 : ℚ) : ℝ) ≤ stT71 23 := by
  have hc : ((-937487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390959266123/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-937487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c24 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((444541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1188653/10000000) (δ := 253/50000000) (ψ := -19347/250000) 71 36
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t24 : ((226841071089/1250000000000 : ℚ) : ℝ) ≤ stT71 24 := by
  have hc : ((111129/125000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226841071089/1250000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((111129/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c25 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-752667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6057251/10000000) (δ := 273/50000000) (ψ := -19347/250000) 71 36
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t25 : ((-1505434752717/10000000000000 : ℚ) : ℝ) ≤ stT71 25 := by
  have hc : ((-752717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1505434752717/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-752717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c26 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((59399/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -672259/2500000) (δ := 93/20000000) (ψ := -19347/250000) 71 37
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t26 : ((465914979931/5000000000000 : ℚ) : ℝ) ≤ stT71 26 := by
  have hc : ((237571/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((465914979931/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((237571/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c27 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-16573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250617/625000) (δ := 219/50000000) (ψ := -19347/250000) 71 37
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t27 : ((-15971433799/2500000000000 : ℚ) : ℝ) ≤ stT71 27 := by
  have hc : ((-8299/250000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15971433799/2500000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-8299/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c28 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-50237/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2621417/5000000) (δ := 327/50000000) (ψ := -19347/250000) 71 38
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t28 : ((-47474243583/500000000000 : ℚ) : ℝ) ≤ stT71 28 := by
  have hc : ((-25121/50000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47474243583/500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-25121/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c29 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((461623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7887/80000) (δ := 131/25000000) (ψ := -19347/250000) 71 38
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t29 : ((428582895447/2500000000000 : ℚ) : ℝ) ≤ stT71 29 := by
  have hc : ((230799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428582895447/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((230799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c30 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-942677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7003401/10000000) (δ := 579/100000000) (ψ := -19347/250000) 71 38
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t30 : ((-860588139217/5000000000000 : ℚ) : ℝ) ≤ stT71 30 := by
  have hc : ((-942727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-860588139217/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-942727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c31 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((50633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2884369/10000000) (δ := 693/100000000) (ψ := -19347/250000) 71 39
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t31 : ((363713304871/5000000000000 : ℚ) : ℝ) ≤ stT71 31 := by
  have hc : ((202507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363713304871/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((202507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c32 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((453231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110041/400000) (δ := 703/100000000) (ψ := -19347/250000) 71 39
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t32 : ((400558981823/5000000000000 : ℚ) : ℝ) ≤ stT71 32 := by
  have hc : ((453181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400558981823/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((453181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c33 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-989707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7494969/10000000) (δ := 21/5000000) (ψ := -19347/250000) 71 40
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t33 : ((-1722946221189/10000000000000 : ℚ) : ℝ) ≤ stT71 33 := by
  have hc : ((-989757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1722946221189/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-989757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c34 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((638363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -549017/2500000) (δ := 553/100000000) (ψ := -19347/250000) 71 40
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t34 : ((218939444061/2000000000000 : ℚ) : ℝ) ≤ stT71 34 := by
  have hc : ((638313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218939444061/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((638313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c35 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((381213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147461/500000) (δ := 43/10000000) (ψ := -19347/250000) 71 40
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t35 : ((161070717051/2500000000000 : ℚ) : ℝ) ≤ stT71 35 := by
  have hc : ((381163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161070717051/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((381163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c36 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-999269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7758413/10000000) (δ := 231/50000000) (ψ := -19347/250000) 71 41
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t36 : ((-1665531999773/10000000000000 : ℚ) : ℝ) ≤ stT71 36 := by
  have hc : ((-999319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1665531999773/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-999319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c37 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((200569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579019/2000000) (δ := 321/50000000) (ψ := -19347/250000) 71 41
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t37 : ((10302879063/156250000000 : ℚ) : ℝ) ≤ stT71 37 := by
  have hc : ((6267/15625 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10302879063/156250000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((6267/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c38 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((741557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1838519/10000000) (δ := 411/100000000) (ψ := -19347/250000) 71 41
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t38 : ((601441518249/5000000000000 : ℚ) : ℝ) ≤ stT71 38 := by
  have hc : ((741507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601441518249/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((741507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c39 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-846231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403073/625000) (δ := 49/12500000) (ψ := -19347/250000) 71 41
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t39 : ((-677567266121/5000000000000 : ℚ) : ℝ) ≤ stT71 39 := by
  have hc : ((-846281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-677567266121/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-846281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c40 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-164459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -952977/2000000) (δ := 361/100000000) (ψ := -19347/250000) 71 42
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t40 : ((-65018016819/1250000000000 : ℚ) : ℝ) ≤ stT71 40 := by
  have hc : ((-41121/125000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65018016819/1250000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-41121/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c41 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((15443/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190973/5000000) (δ := 113/25000000) (ψ := -19347/250000) 71 42
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t41 : ((771733900287/5000000000000 : ℚ) : ℝ) ≤ stT71 41 := by
  have hc : ((494151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((771733900287/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((494151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c42 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((1581/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3895369/10000000) (δ := 621/100000000) (ψ := -19347/250000) 71 42
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t42 : ((9719564867/5000000000000 : ℚ) : ℝ) ≤ stT71 42 := by
  have hc : ((6299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9719564867/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((6299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c43 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-996199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -763593/1000000) (δ := 601/100000000) (ψ := -19347/250000) 71 43
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t43 : ((-759632888757/5000000000000 : ℚ) : ℝ) ≤ stT71 43 := by
  have hc : ((-996249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-759632888757/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-996249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c44 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((148133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3555291/10000000) (δ := 491/100000000) (ψ := -19347/250000) 71 43
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t44 : ((55810853787/2500000000000 : ℚ) : ℝ) ≤ stT71 44 := by
  have hc : ((148083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55810853787/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((148083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c45 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((492497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 433641/10000000) (δ := 311/50000000) (ψ := -19347/250000) 71 43
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t45 : ((91766678449/625000000000 : ℚ) : ℝ) ≤ stT71 45 := by
  have hc : ((61559/62500 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91766678449/625000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((61559/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c46 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-162439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4334897/10000000) (δ := 21/3125000) (ψ := -19347/250000) 71 43
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t46 : ((-11978851569/500000000000 : ℚ) : ℝ) ≤ stT71 46 := by
  have hc : ((-162489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11978851569/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-162489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c47 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-992891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1511143/2000000) (δ := 9/1250000) (ψ := -19347/250000) 71 44
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t47 : ((-28967067793/200000000000 : ℚ) : ℝ) ≤ stT71 47 := by
  have hc : ((-992941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28967067793/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-992941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c48 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((43289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -763747/2000000) (δ := 33/5000000) (ψ := -19347/250000) 71 44
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t48 : ((499280733/80000000000 : ℚ) : ℝ) ≤ stT71 48 := by
  have hc : ((43239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499280733/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((43239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c49 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((997983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158811/10000000) (δ := 693/100000000) (ψ := -19347/250000) 71 44
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t49 : ((1425618143743/10000000000000 : ℚ) : ℝ) ≤ stT71 49 := by
  have hc : ((997933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1425618143743/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((997933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c50 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((198599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3427169/10000000) (δ := 7/1000000) (ψ := -19347/250000) 71 44
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t50 : ((280790576937/10000000000000 : ℚ) : ℝ) ≤ stT71 50 := by
  have hc : ((198549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280790576937/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((198549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c51 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-934217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 867767/1250000) (δ := 3/625000) (ψ := -19347/250000) 71 44
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t51 : ((-1308236329027/10000000000000 : ℚ) : ℝ) ≤ stT71 51 := by
  have hc : ((-934267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1308236329027/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-934267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c52 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-105703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2659559/5000000) (δ := 619/100000000) (ψ := -19347/250000) 71 45
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t52 : ((-146597608463/2000000000000 : ℚ) : ℝ) ≤ stT71 52 := by
  have hc : ((-105713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146597608463/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-105713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c53 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((714263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1938063/10000000) (δ := 639/100000000) (ψ := -19347/250000) 71 45
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t53 : ((196209309573/2000000000000 : ℚ) : ℝ) ≤ stT71 53 := by
  have hc : ((714213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196209309573/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((714213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c54 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((851521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1379791/10000000) (δ := 389/100000000) (ψ := -19347/250000) 71 45
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t54 : ((1158704726517/10000000000000 : ℚ) : ℝ) ≤ stT71 54 := by
  have hc : ((851471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1158704726517/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((851471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c55 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-28011/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4636763/10000000) (δ := 297/50000000) (ψ := -19347/250000) 71 45
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t55 : ((-5902621/156250000 : ℚ) : ℝ) ≤ stT71 55 := by
  have hc : ((-1751/6250 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5902621/156250000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-1751/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c56 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-999971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 979381/1250000) (δ := 161/25000000) (ψ := -19347/250000) 71 45
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t56 : ((-1336335062447/10000000000000 : ℚ) : ℝ) ≤ stT71 56 := by
  have hc : ((-1000021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1336335062447/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-1000021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c57 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-15809/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4731241/10000000) (δ := 91/20000000) (ψ := -19347/250000) 71 46
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t57 : ((-41885707059/1000000000000 : ℚ) : ℝ) ≤ stT71 57 := by
  have hc : ((-31623/100000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41885707059/1000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-31623/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c58 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((791411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -822103/5000000) (δ := 319/50000000) (ψ := -19347/250000) 71 46
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t58 : ((129888455013/1250000000000 : ℚ) : ℝ) ≤ stT71 58 := by
  have hc : ((791361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129888455013/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((791361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c59 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((849361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278011/2000000) (δ := 219/50000000) (ψ := -19347/250000) 71 46
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t59 : ((1105708648479/10000000000000 : ℚ) : ℝ) ≤ stT71 59 := by
  have hc : ((849311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1105708648479/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((849311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c60 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-11099/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4373319/10000000) (δ := 17/4000000) (ψ := -19347/250000) 71 46
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t60 : ((-22932460583/1000000000000 : ℚ) : ℝ) ≤ stT71 60 := by
  have hc : ((-88817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22932460583/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-88817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c61 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-122023/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 730727/1000000) (δ := 87/20000000) (ψ := -19347/250000) 71 46
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t61 : ((-624969875173/5000000000000 : ℚ) : ℝ) ≤ stT71 61 := by
  have hc : ((-488117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-624969875173/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-488117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c62 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-118633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5514451/10000000) (δ := 23/4000000) (ψ := -19347/250000) 71 47
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t62 : ((-75338423643/1000000000000 : ℚ) : ℝ) ≤ stT71 62 := by
  have hc : ((-118643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75338423643/1000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-118643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c63 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((240169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267439/1000000) (δ := 269/50000000) (ψ := -19347/250000) 71 47
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t63 : ((18909553929/312500000000 : ℚ) : ℝ) ≤ stT71 63 := by
  have hc : ((15009/31250 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18909553929/312500000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((15009/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c64 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((99883/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120943/10000000) (δ := 113/20000000) (ψ := -19347/250000) 71 47
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t64 : ((49939/400000 : ℚ) : ℝ) ≤ stT71 64 := by
  have hc : ((49939/50000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49939/400000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((49939/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c65 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((409241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 359117/1250000) (δ := 93/20000000) (ψ := -19347/250000) 71 47
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t65 : ((507538829277/10000000000000 : ℚ) : ℝ) ≤ stT71 65 := by
  have hc : ((409191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507538829277/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((409191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c66 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-614987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5582913/10000000) (δ := 209/50000000) (ψ := -19347/250000) 71 47
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t66 : ((-151411653771/2000000000000 : ℚ) : ℝ) ≤ stT71 66 := by
  have hc : ((-615037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151411653771/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-615037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c67 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-197469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7455827/10000000) (δ := 577/100000000) (ψ := -19347/250000) 71 48
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t67 : ((-48251821381/400000000000 : ℚ) : ℝ) ≤ stT71 67 := by
  have hc : ((-197479/200000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48251821381/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-197479/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c68 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-351959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96523/200000) (δ := 707/100000000) (ψ := -19347/250000) 71 48
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t68 : ((-426873922111/10000000000000 : ℚ) : ℝ) ≤ stT71 68 := by
  have hc : ((-352009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426873922111/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-352009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c69 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((626341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2234863/10000000) (δ := 707/100000000) (ψ := -19347/250000) 71 48
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t69 : ((376982715339/5000000000000 : ℚ) : ℝ) ≤ stT71 69 := by
  have hc : ((626291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376982715339/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((626291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c70 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((991863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159569/5000000) (δ := 437/100000000) (ψ := -19347/250000) 71 48
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t70 : ((296360667091/2500000000000 : ℚ) : ℝ) ≤ stT71 70 := by
  have hc : ((991813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296360667091/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((991813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c71 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((211173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2836911/10000000) (δ := 67/12500000) (ψ := -19347/250000) 71 48
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t71 : ((62646608647/1250000000000 : ℚ) : ℝ) ≤ stT71 71 := by
  have hc : ((52787/125000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62646608647/1250000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((52787/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c72 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-105727/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5319469/10000000) (δ := 587/100000000) (ψ := -19347/250000) 71 48
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t72 : ((-7788270209/125000000000 : ℚ) : ℝ) ≤ stT71 72 := by
  have hc : ((-105737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7788270209/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-105737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c73 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-499703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7767783/10000000) (δ := 457/100000000) (ψ := -19347/250000) 71 48
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t73 : ((-9138869499/78125000000 : ℚ) : ℝ) ≤ stT71 73 := by
  have hc : ((-31233/31250 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9138869499/78125000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-31233/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c74 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-596613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5525177/10000000) (δ := 627/100000000) (ψ := -19347/250000) 71 49
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t74 : ((-693607014251/10000000000000 : ℚ) : ℝ) ≤ stT71 74 := by
  have hc : ((-596663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-693607014251/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-596663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c75 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((154319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314259/1000000) (δ := 77/12500000) (ψ := -19347/250000) 71 49
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t75 : ((890816409/25000000000 : ℚ) : ℝ) ≤ stT71 75 := by
  have hc : ((77147/250000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((890816409/25000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((77147/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c76 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((237573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -791563/10000000) (δ := 57/12500000) (ψ := -19347/250000) 71 49
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t76 : ((272500423219/2500000000000 : ℚ) : ℝ) ≤ stT71 76 := by
  have hc : ((475121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272500423219/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((475121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c77 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((102349/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382183/2500000) (δ := 283/50000000) (ψ := -19347/250000) 71 49
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t77 : ((93304247691/1000000000000 : ℚ) : ℝ) ≤ stT71 77 := by
  have hc : ((409371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93304247691/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((409371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c78 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((43149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909543/5000000) (δ := 273/50000000) (ψ := -19347/250000) 71 49
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t78 : ((48800006423/10000000000000 : ℚ) : ℝ) ≤ stT71 78 := by
  have hc : ((43099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48800006423/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((43099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c79 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-94837/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6080263/10000000) (δ := 183/50000000) (ψ := -19347/250000) 71 49
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t79 : ((-13338375307/156250000000 : ℚ) : ℝ) ≤ stT71 79 := by
  have hc : ((-379373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13338375307/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-379373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c80 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-122899/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3697483/5000000) (δ := 119/25000000) (ψ := -19347/250000) 71 50
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t80 : ((-274824496557/2500000000000 : ℚ) : ℝ) ≤ stT71 80 := by
  have hc : ((-491621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274824496557/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-491621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c81 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-19359/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5189969/10000000) (δ := 367/100000000) (ψ := -19347/250000) 71 50
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t81 : ((-2689029929/50000000000 : ℚ) : ℝ) ≤ stT71 81 := by
  have hc : ((-19361/40000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2689029929/50000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-19361/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c82 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((357869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753007/2500000) (δ := 13/3125000) (ψ := -19347/250000) 71 50
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t82 : ((79028977797/2000000000000 : ℚ) : ℝ) ≤ stT71 82 := by
  have hc : ((357819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79028977797/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((357819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c83 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((235337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430243/5000000) (δ := 169/25000000) (ψ := -19347/250000) 71 50
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t83 : ((258302054829/2500000000000 : ℚ) : ℝ) ≤ stT71 83 := by
  have hc : ((470649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258302054829/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((470649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c84 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((437317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158161/1250000) (δ := 23/3125000) (ψ := -19347/250000) 71 50
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t84 : ((119281122747/1250000000000 : ℚ) : ℝ) ≤ stT71 84 := by
  have hc : ((109323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119281122747/1250000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((109323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c85 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((44511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210369/625000) (δ := 377/100000000) (ψ := -19347/250000) 71 50
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t85 : ((12067024663/500000000000 : ℚ) : ℝ) ≤ stT71 85 := by
  have hc : ((44501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12067024663/500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((44501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c86 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-569571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5441951/10000000) (δ := 657/100000000) (ψ := -19347/250000) 71 50
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t86 : ((-76779784211/1250000000000 : ℚ) : ℝ) ≤ stT71 86 := by
  have hc : ((-569621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76779784211/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-569621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c87 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-989651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7493997/10000000) (δ := 303/50000000) (ψ := -19347/250000) 71 50
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t87 : ((-1061071308213/10000000000000 : ℚ) : ℝ) ≤ stT71 87 := by
  have hc : ((-989701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1061071308213/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-989701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c88 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-785407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6185373/10000000) (δ := 129/20000000) (ψ := -19347/250000) 71 51
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t88 : ((-209325075957/2500000000000 : ℚ) : ℝ) ≤ stT71 88 := by
  have hc : ((-785457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209325075957/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-785457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c89 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-6307/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2089851/5000000) (δ := 229/50000000) (ψ := -19347/250000) 71 51
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t89 : ((-26754879519/2500000000000 : ℚ) : ℝ) ≤ stT71 89 := by
  have hc : ((-50481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26754879519/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-50481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c90 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((79781/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2196441/10000000) (δ := 117/25000000) (ψ := -19347/250000) 71 51
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t90 : ((84089925777/1250000000000 : ℚ) : ℝ) ≤ stT71 90 := by
  have hc : ((319099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84089925777/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((319099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c91 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((497791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47019/2000000) (δ := 91/12500000) (ψ := -19347/250000) 71 51
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t91 : ((65225016693/625000000000 : ℚ) : ℝ) ≤ stT71 91 := by
  have hc : ((248883/250000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65225016693/625000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((248883/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c92 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((19409/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 340963/2000000) (δ := 259/50000000) (ψ := -19347/250000) 71 51
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t92 : ((20233976733/250000000000 : ℚ) : ℝ) ≤ stT71 92 := by
  have hc : ((77631/100000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20233976733/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((77631/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c93 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((60499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3623753/10000000) (δ := 81/12500000) (ψ := -19347/250000) 71 51
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t93 : ((31354287387/2500000000000 : ℚ) : ℝ) ≤ stT71 93 := by
  have hc : ((30237/250000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31354287387/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((30237/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c94 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-595647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5522167/10000000) (δ := 289/50000000) (ψ := -19347/250000) 71 51
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t94 : ((-307207495567/5000000000000 : ℚ) : ℝ) ≤ stT71 94 := by
  have hc : ((-595697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307207495567/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-595697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c95 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-983593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7400491/10000000) (δ := 157/25000000) (ψ := -19347/250000) 71 51
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t95 : ((-1009197061497/10000000000000 : ℚ) : ℝ) ≤ stT71 95 := by
  have hc : ((-983643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1009197061497/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-983643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c96 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-211539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -403051/625000) (δ := 649/100000000) (ψ := -19347/250000) 71 52
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t96 : ((-431827806963/5000000000000 : ℚ) : ℝ) ≤ stT71 96 := by
  have hc : ((-423103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-431827806963/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-423103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c97 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((-53919/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2304711/5000000) (δ := 529/100000000) (ψ := -19347/250000) 71 52
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t97 : ((-54756648363/2000000000000 : ℚ) : ℝ) ≤ stT71 97 := by
  have hc : ((-53929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54756648363/2000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-53929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c98 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((439677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2788893/10000000) (δ := 539/100000000) (ψ := -19347/250000) 71 52
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t98 : ((55511261663/1250000000000 : ℚ) : ℝ) ≤ stT71 98 := by
  have hc : ((439627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55511261663/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((439627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c99 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((923097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -986847/10000000) (δ := 187/50000000) (ψ := -19347/250000) 71 52
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t99 : ((927696387739/10000000000000 : ℚ) : ℝ) ≤ stT71 99 := by
  have hc : ((923047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((927696387739/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((923047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_c100 :
    |Real.cos (((71 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-19347/250000 : ℚ) : ℝ))
      - ((949601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24909/312500) (δ := 609/100000000) (ψ := -19347/250000) 71 52
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st71_t100 : ((949550050449/10000000000000 : ℚ) : ℝ) ≤ stT71 100 := by
  have hc : ((949551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((71 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-19347/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st71_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((949550050449/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((949551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st71_p1 : ((996957/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT71 (i+1) := by
  rw [Finset.sum_range_one]
  exact st71_t1

theorem st71_p2 : ((3484837966651/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT71 (i+1))
      = (∑ i ∈ Finset.range 1, stT71 (i+1)) + stT71 2 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 1
    simpa using h
  have hprev := st71_p1
  have hstep := st71_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p3 : ((876815224657/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT71 (i+1))
      = (∑ i ∈ Finset.range 2, stT71 (i+1)) + stT71 3 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 2
    simpa using h
  have hprev := st71_p2
  have hstep := st71_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p4 : ((3283315903133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT71 (i+1))
      = (∑ i ∈ Finset.range 3, stT71 (i+1)) + stT71 4 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 3
    simpa using h
  have hprev := st71_p3
  have hstep := st71_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p5 : ((3987981270813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT71 (i+1))
      = (∑ i ∈ Finset.range 4, stT71 (i+1)) + stT71 5 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 4
    simpa using h
  have hprev := st71_p4
  have hstep := st71_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p6 : ((7739892962151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT71 (i+1))
      = (∑ i ∈ Finset.range 5, stT71 (i+1)) + stT71 6 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 5
    simpa using h
  have hprev := st71_p5
  have hstep := st71_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p7 : ((2303851453699/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT71 (i+1))
      = (∑ i ∈ Finset.range 6, stT71 (i+1)) + stT71 7 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 6
    simpa using h
  have hprev := st71_p6
  have hstep := st71_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p8 : ((7990532706979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT71 (i+1))
      = (∑ i ∈ Finset.range 7, stT71 (i+1)) + stT71 8 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 7
    simpa using h
  have hprev := st71_p7
  have hstep := st71_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p9 : ((153020872813/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT71 (i+1))
      = (∑ i ∈ Finset.range 8, stT71 (i+1)) + stT71 9 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 8
    simpa using h
  have hprev := st71_p8
  have hstep := st71_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p10 : ((6446800304031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT71 (i+1))
      = (∑ i ∈ Finset.range 9, stT71 (i+1)) + stT71 10 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 9
    simpa using h
  have hprev := st71_p9
  have hstep := st71_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p11 : ((1523422076951/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT71 (i+1))
      = (∑ i ∈ Finset.range 10, stT71 (i+1)) + stT71 11 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 10
    simpa using h
  have hprev := st71_p10
  have hstep := st71_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p12 : ((17654146605047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT71 (i+1))
      = (∑ i ∈ Finset.range 11, stT71 (i+1)) + stT71 12 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 11
    simpa using h
  have hprev := st71_p11
  have hstep := st71_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p13 : ((20426736897047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT71 (i+1))
      = (∑ i ∈ Finset.range 12, stT71 (i+1)) + stT71 13 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 12
    simpa using h
  have hprev := st71_p12
  have hstep := st71_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p14 : ((4353551476923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT71 (i+1))
      = (∑ i ∈ Finset.range 13, stT71 (i+1)) + stT71 14 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 13
    simpa using h
  have hprev := st71_p13
  have hstep := st71_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p15 : ((9906289890111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT71 (i+1))
      = (∑ i ∈ Finset.range 14, stT71 (i+1)) + stT71 15 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 14
    simpa using h
  have hprev := st71_p14
  have hstep := st71_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p16 : ((4609738557693/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT71 (i+1))
      = (∑ i ∈ Finset.range 15, stT71 (i+1)) + stT71 16 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 15
    simpa using h
  have hprev := st71_p15
  have hstep := st71_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p17 : ((1041386550579/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT71 (i+1))
      = (∑ i ∈ Finset.range 16, stT71 (i+1)) + stT71 17 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 16
    simpa using h
  have hprev := st71_p16
  have hstep := st71_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p18 : ((3947613498713/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT71 (i+1))
      = (∑ i ∈ Finset.range 17, stT71 (i+1)) + stT71 18 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 17
    simpa using h
  have hprev := st71_p17
  have hstep := st71_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p19 : ((19244816641091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT71 (i+1))
      = (∑ i ∈ Finset.range 18, stT71 (i+1)) + stT71 19 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 18
    simpa using h
  have hprev := st71_p18
  have hstep := st71_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p20 : ((4142774482177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT71 (i+1))
      = (∑ i ∈ Finset.range 19, stT71 (i+1)) + stT71 20 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 19
    simpa using h
  have hprev := st71_p19
  have hstep := st71_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p21 : ((18832524243467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT71 (i+1))
      = (∑ i ∈ Finset.range 20, stT71 (i+1)) + stT71 21 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 20
    simpa using h
  have hprev := st71_p20
  have hstep := st71_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p22 : ((5205020343299/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT71 (i+1))
      = (∑ i ∈ Finset.range 21, stT71 (i+1)) + stT71 22 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 21
    simpa using h
  have hprev := st71_p21
  have hstep := st71_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p23 : ((18865285042581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT71 (i+1))
      = (∑ i ∈ Finset.range 22, stT71 (i+1)) + stT71 23 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 22
    simpa using h
  have hprev := st71_p22
  have hstep := st71_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p24 : ((20680013611293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT71 (i+1))
      = (∑ i ∈ Finset.range 23, stT71 (i+1)) + stT71 24 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 23
    simpa using h
  have hprev := st71_p23
  have hstep := st71_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p25 : ((1198411178661/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT71 (i+1))
      = (∑ i ∈ Finset.range 24, stT71 (i+1)) + stT71 25 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 24
    simpa using h
  have hprev := st71_p24
  have hstep := st71_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p26 : ((10053204409219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT71 (i+1))
      = (∑ i ∈ Finset.range 25, stT71 (i+1)) + stT71 26 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 25
    simpa using h
  have hprev := st71_p25
  have hstep := st71_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p27 : ((10021261541621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT71 (i+1))
      = (∑ i ∈ Finset.range 26, stT71 (i+1)) + stT71 27 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 26
    simpa using h
  have hprev := st71_p26
  have hstep := st71_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p28 : ((9546519105791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT71 (i+1))
      = (∑ i ∈ Finset.range 27, stT71 (i+1)) + stT71 28 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 27
    simpa using h
  have hprev := st71_p27
  have hstep := st71_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p29 : ((2080736979337/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT71 (i+1))
      = (∑ i ∈ Finset.range 28, stT71 (i+1)) + stT71 29 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 28
    simpa using h
  have hprev := st71_p28
  have hstep := st71_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p30 : ((2385774189367/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT71 (i+1))
      = (∑ i ∈ Finset.range 29, stT71 (i+1)) + stT71 30 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 29
    simpa using h
  have hprev := st71_p29
  have hstep := st71_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p31 : ((9906810062339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT71 (i+1))
      = (∑ i ∈ Finset.range 30, stT71 (i+1)) + stT71 31 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 30
    simpa using h
  have hprev := st71_p30
  have hstep := st71_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p32 : ((5153684522081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT71 (i+1))
      = (∑ i ∈ Finset.range 31, stT71 (i+1)) + stT71 32 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 31
    simpa using h
  have hprev := st71_p31
  have hstep := st71_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p33 : ((3778358373427/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT71 (i+1))
      = (∑ i ∈ Finset.range 32, stT71 (i+1)) + stT71 33 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 32
    simpa using h
  have hprev := st71_p32
  have hstep := st71_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p34 : ((249831113593/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT71 (i+1))
      = (∑ i ∈ Finset.range 33, stT71 (i+1)) + stT71 34 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 33
    simpa using h
  have hprev := st71_p33
  have hstep := st71_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p35 : ((5157692988911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT71 (i+1))
      = (∑ i ∈ Finset.range 34, stT71 (i+1)) + stT71 35 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 34
    simpa using h
  have hprev := st71_p34
  have hstep := st71_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p36 : ((18965239955871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT71 (i+1))
      = (∑ i ∈ Finset.range 35, stT71 (i+1)) + stT71 36 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 35
    simpa using h
  have hprev := st71_p35
  have hstep := st71_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p37 : ((19624624215903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT71 (i+1))
      = (∑ i ∈ Finset.range 36, stT71 (i+1)) + stT71 37 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 36
    simpa using h
  have hprev := st71_p36
  have hstep := st71_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p38 : ((20827507252401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT71 (i+1))
      = (∑ i ∈ Finset.range 37, stT71 (i+1)) + stT71 38 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 37
    simpa using h
  have hprev := st71_p37
  have hstep := st71_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p39 : ((19472372720159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT71 (i+1))
      = (∑ i ∈ Finset.range 38, stT71 (i+1)) + stT71 39 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 38
    simpa using h
  have hprev := st71_p38
  have hstep := st71_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p40 : ((18952228585607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT71 (i+1))
      = (∑ i ∈ Finset.range 39, stT71 (i+1)) + stT71 40 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 39
    simpa using h
  have hprev := st71_p39
  have hstep := st71_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p41 : ((20495696386181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT71 (i+1))
      = (∑ i ∈ Finset.range 40, stT71 (i+1)) + stT71 41 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 40
    simpa using h
  have hprev := st71_p40
  have hstep := st71_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p42 : ((4103027103183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT71 (i+1))
      = (∑ i ∈ Finset.range 41, stT71 (i+1)) + stT71 42 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 41
    simpa using h
  have hprev := st71_p41
  have hstep := st71_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p43 : ((18995869738401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT71 (i+1))
      = (∑ i ∈ Finset.range 42, stT71 (i+1)) + stT71 43 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 42
    simpa using h
  have hprev := st71_p42
  have hstep := st71_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p44 : ((19219113153549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT71 (i+1))
      = (∑ i ∈ Finset.range 43, stT71 (i+1)) + stT71 44 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 43
    simpa using h
  have hprev := st71_p43
  have hstep := st71_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p45 : ((20687380008733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT71 (i+1))
      = (∑ i ∈ Finset.range 44, stT71 (i+1)) + stT71 45 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 44
    simpa using h
  have hprev := st71_p44
  have hstep := st71_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p46 : ((20447802977353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT71 (i+1))
      = (∑ i ∈ Finset.range 45, stT71 (i+1)) + stT71 46 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 45
    simpa using h
  have hprev := st71_p45
  have hstep := st71_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p47 : ((18999449587703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT71 (i+1))
      = (∑ i ∈ Finset.range 46, stT71 (i+1)) + stT71 47 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 46
    simpa using h
  have hprev := st71_p46
  have hstep := st71_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p48 : ((595683114979/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT71 (i+1))
      = (∑ i ∈ Finset.range 47, stT71 (i+1)) + stT71 48 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 47
    simpa using h
  have hprev := st71_p47
  have hstep := st71_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p49 : ((20487477823071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT71 (i+1))
      = (∑ i ∈ Finset.range 48, stT71 (i+1)) + stT71 49 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 48
    simpa using h
  have hprev := st71_p48
  have hstep := st71_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p50 : ((2596033550001/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT71 (i+1))
      = (∑ i ∈ Finset.range 49, stT71 (i+1)) + stT71 50 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 49
    simpa using h
  have hprev := st71_p49
  have hstep := st71_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p51 : ((19460032070981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT71 (i+1))
      = (∑ i ∈ Finset.range 50, stT71 (i+1)) + stT71 51 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 50
    simpa using h
  have hprev := st71_p50
  have hstep := st71_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p52 : ((9363522014333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT71 (i+1))
      = (∑ i ∈ Finset.range 51, stT71 (i+1)) + stT71 52 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 51
    simpa using h
  have hprev := st71_p51
  have hstep := st71_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p53 : ((19708090576531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT71 (i+1))
      = (∑ i ∈ Finset.range 52, stT71 (i+1)) + stT71 53 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 52
    simpa using h
  have hprev := st71_p52
  have hstep := st71_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p54 : ((2608349412881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT71 (i+1))
      = (∑ i ∈ Finset.range 53, stT71 (i+1)) + stT71 54 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 53
    simpa using h
  have hprev := st71_p53
  have hstep := st71_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p55 : ((2561128444881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT71 (i+1))
      = (∑ i ∈ Finset.range 54, stT71 (i+1)) + stT71 55 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 54
    simpa using h
  have hprev := st71_p54
  have hstep := st71_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p56 : ((19152692496601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT71 (i+1))
      = (∑ i ∈ Finset.range 55, stT71 (i+1)) + stT71 56 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 55
    simpa using h
  have hprev := st71_p55
  have hstep := st71_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p57 : ((18733835426011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT71 (i+1))
      = (∑ i ∈ Finset.range 56, stT71 (i+1)) + stT71 57 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 56
    simpa using h
  have hprev := st71_p56
  have hstep := st71_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p58 : ((3954588613223/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT71 (i+1))
      = (∑ i ∈ Finset.range 57, stT71 (i+1)) + stT71 58 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 57
    simpa using h
  have hprev := st71_p57
  have hstep := st71_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p59 : ((10439325857297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT71 (i+1))
      = (∑ i ∈ Finset.range 58, stT71 (i+1)) + stT71 59 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 58
    simpa using h
  have hprev := st71_p58
  have hstep := st71_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p60 : ((5162331777191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT71 (i+1))
      = (∑ i ∈ Finset.range 59, stT71 (i+1)) + stT71 60 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 59
    simpa using h
  have hprev := st71_p59
  have hstep := st71_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p61 : ((9699693679209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT71 (i+1))
      = (∑ i ∈ Finset.range 60, stT71 (i+1)) + stT71 61 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 60
    simpa using h
  have hprev := st71_p60
  have hstep := st71_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p62 : ((4661500780497/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT71 (i+1))
      = (∑ i ∈ Finset.range 61, stT71 (i+1)) + stT71 62 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 61
    simpa using h
  have hprev := st71_p61
  have hstep := st71_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p63 : ((4812777211929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT71 (i+1))
      = (∑ i ∈ Finset.range 62, stT71 (i+1)) + stT71 63 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 62
    simpa using h
  have hprev := st71_p62
  have hstep := st71_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p64 : ((5124895961929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT71 (i+1))
      = (∑ i ∈ Finset.range 63, stT71 (i+1)) + stT71 64 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 63
    simpa using h
  have hprev := st71_p63
  have hstep := st71_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p65 : ((21007122676993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT71 (i+1))
      = (∑ i ∈ Finset.range 64, stT71 (i+1)) + stT71 65 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 64
    simpa using h
  have hprev := st71_p64
  have hstep := st71_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p66 : ((10125032204069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT71 (i+1))
      = (∑ i ∈ Finset.range 65, stT71 (i+1)) + stT71 66 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 65
    simpa using h
  have hprev := st71_p65
  have hstep := st71_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p67 : ((19043768873613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT71 (i+1))
      = (∑ i ∈ Finset.range 66, stT71 (i+1)) + stT71 67 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 66
    simpa using h
  have hprev := st71_p66
  have hstep := st71_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p68 : ((9308447475751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT71 (i+1))
      = (∑ i ∈ Finset.range 67, stT71 (i+1)) + stT71 68 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 67
    simpa using h
  have hprev := st71_p67
  have hstep := st71_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p69 : ((968543019109/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT71 (i+1))
      = (∑ i ∈ Finset.range 68, stT71 (i+1)) + stT71 69 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 68
    simpa using h
  have hprev := st71_p68
  have hstep := st71_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p70 : ((1284768940659/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT71 (i+1))
      = (∑ i ∈ Finset.range 69, stT71 (i+1)) + stT71 70 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 69
    simpa using h
  have hprev := st71_p69
  have hstep := st71_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p71 : ((526436897993/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT71 (i+1))
      = (∑ i ∈ Finset.range 70, stT71 (i+1)) + stT71 71 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 70
    simpa using h
  have hprev := st71_p70
  have hstep := st71_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p72 : ((20434414303/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT71 (i+1))
      = (∑ i ∈ Finset.range 71, stT71 (i+1)) + stT71 72 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 71
    simpa using h
  have hprev := st71_p71
  have hstep := st71_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p73 : ((2408079875891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT71 (i+1))
      = (∑ i ∈ Finset.range 72, stT71 (i+1)) + stT71 73 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 72
    simpa using h
  have hprev := st71_p72
  have hstep := st71_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p74 : ((18571031992877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT71 (i+1))
      = (∑ i ∈ Finset.range 73, stT71 (i+1)) + stT71 74 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 73
    simpa using h
  have hprev := st71_p73
  have hstep := st71_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p75 : ((18927358556477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT71 (i+1))
      = (∑ i ∈ Finset.range 74, stT71 (i+1)) + stT71 75 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 74
    simpa using h
  have hprev := st71_p74
  have hstep := st71_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p76 : ((20017360249353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT71 (i+1))
      = (∑ i ∈ Finset.range 75, stT71 (i+1)) + stT71 76 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 75
    simpa using h
  have hprev := st71_p75
  have hstep := st71_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p77 : ((20950402726263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT71 (i+1))
      = (∑ i ∈ Finset.range 76, stT71 (i+1)) + stT71 77 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 76
    simpa using h
  have hprev := st71_p76
  have hstep := st71_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p78 : ((10499601366343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT71 (i+1))
      = (∑ i ∈ Finset.range 77, stT71 (i+1)) + stT71 78 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 77
    simpa using h
  have hprev := st71_p77
  have hstep := st71_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p79 : ((10072773356519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT71 (i+1))
      = (∑ i ∈ Finset.range 78, stT71 (i+1)) + stT71 79 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 78
    simpa using h
  have hprev := st71_p78
  have hstep := st71_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p80 : ((1904624872681/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT71 (i+1))
      = (∑ i ∈ Finset.range 79, stT71 (i+1)) + stT71 80 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 79
    simpa using h
  have hprev := st71_p79
  have hstep := st71_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p81 : ((1850844274101/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT71 (i+1))
      = (∑ i ∈ Finset.range 80, stT71 (i+1)) + stT71 81 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 80
    simpa using h
  have hprev := st71_p80
  have hstep := st71_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p82 : ((3780717525999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT71 (i+1))
      = (∑ i ∈ Finset.range 81, stT71 (i+1)) + stT71 82 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 81
    simpa using h
  have hprev := st71_p81
  have hstep := st71_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p83 : ((19936795849311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT71 (i+1))
      = (∑ i ∈ Finset.range 82, stT71 (i+1)) + stT71 83 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 82
    simpa using h
  have hprev := st71_p82
  have hstep := st71_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p84 : ((20891044831287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT71 (i+1))
      = (∑ i ∈ Finset.range 83, stT71 (i+1)) + stT71 84 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 83
    simpa using h
  have hprev := st71_p83
  have hstep := st71_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p85 : ((21132385324547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT71 (i+1))
      = (∑ i ∈ Finset.range 84, stT71 (i+1)) + stT71 85 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 84
    simpa using h
  have hprev := st71_p84
  have hstep := st71_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p86 : ((20518147050859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT71 (i+1))
      = (∑ i ∈ Finset.range 85, stT71 (i+1)) + stT71 86 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 85
    simpa using h
  have hprev := st71_p85
  have hstep := st71_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p87 : ((9728537871323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT71 (i+1))
      = (∑ i ∈ Finset.range 86, stT71 (i+1)) + stT71 87 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 86
    simpa using h
  have hprev := st71_p86
  have hstep := st71_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p88 : ((9309887719409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT71 (i+1))
      = (∑ i ∈ Finset.range 87, stT71 (i+1)) + stT71 88 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 87
    simpa using h
  have hprev := st71_p87
  have hstep := st71_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p89 : ((9256377960371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT71 (i+1))
      = (∑ i ∈ Finset.range 88, stT71 (i+1)) + stT71 89 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 88
    simpa using h
  have hprev := st71_p88
  have hstep := st71_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p90 : ((9592737663479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT71 (i+1))
      = (∑ i ∈ Finset.range 89, stT71 (i+1)) + stT71 90 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 89
    simpa using h
  have hprev := st71_p89
  have hstep := st71_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p91 : ((10114537797023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT71 (i+1))
      = (∑ i ∈ Finset.range 90, stT71 (i+1)) + stT71 91 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 90
    simpa using h
  have hprev := st71_p90
  have hstep := st71_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p92 : ((10519217331683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT71 (i+1))
      = (∑ i ∈ Finset.range 91, stT71 (i+1)) + stT71 92 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 91
    simpa using h
  have hprev := st71_p91
  have hstep := st71_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p93 : ((10581925906457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT71 (i+1))
      = (∑ i ∈ Finset.range 92, stT71 (i+1)) + stT71 93 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 92
    simpa using h
  have hprev := st71_p92
  have hstep := st71_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p94 : ((1027471841089/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT71 (i+1))
      = (∑ i ∈ Finset.range 93, stT71 (i+1)) + stT71 94 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 93
    simpa using h
  have hprev := st71_p93
  have hstep := st71_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p95 : ((19540239760283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT71 (i+1))
      = (∑ i ∈ Finset.range 94, stT71 (i+1)) + stT71 95 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 94
    simpa using h
  have hprev := st71_p94
  have hstep := st71_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p96 : ((18676584146357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT71 (i+1))
      = (∑ i ∈ Finset.range 95, stT71 (i+1)) + stT71 96 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 95
    simpa using h
  have hprev := st71_p95
  have hstep := st71_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p97 : ((9201400452271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT71 (i+1))
      = (∑ i ∈ Finset.range 96, stT71 (i+1)) + stT71 97 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 96
    simpa using h
  have hprev := st71_p96
  have hstep := st71_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p98 : ((9423445498923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT71 (i+1))
      = (∑ i ∈ Finset.range 97, stT71 (i+1)) + stT71 98 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 97
    simpa using h
  have hprev := st71_p97
  have hstep := st71_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p99 : ((3954917477117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT71 (i+1))
      = (∑ i ∈ Finset.range 98, stT71 (i+1)) + stT71 99 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 98
    simpa using h
  have hprev := st71_p98
  have hstep := st71_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st71_p100 : ((10362068718017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT71 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT71 (i+1))
      = (∑ i ∈ Finset.range 99, stT71 (i+1)) + stT71 100 := by
    have h := Finset.sum_range_succ (fun i => stT71 (i+1)) 99
    simpa using h
  have hprev := st71_p99
  have hstep := st71_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 71`.** -/
theorem station_71_sign : 0 < hardyG (((71:ℕ)):ℝ) := by
  have hcore := phase_station_lower 71 100 (by norm_num) (by norm_num)
    ((-19347/250000 : ℚ) : ℝ)
  have hchain := st71_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT71 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((71:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-19347/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((71:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((71:ℕ)):ℝ)+1) * ((((71:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((4511447/7100000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((10362068718017/5000000000000 : ℚ) : ℝ) - ((4511447/7100000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-19347/250000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((71:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-19347/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((71:ℕ)):ℝ))).re
      - Real.sin ((-19347/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((71:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((71:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((71:ℕ)):ℝ)
      = ((((71:ℕ)):ℝ) * (Real.log (((71:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((71:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_71
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
  have hθwin : |(((-19347/250000 : ℚ) : ℝ) + ((8:ℤ)) * (2*Real.pi)) - theta (((71:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((71:ℕ)):ℝ))
    (φ := ((-19347/250000 : ℚ) : ℝ) + ((8:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-19347/250000 : ℚ)) : ℝ) 8).1,
    (cos_sin_shift (((-19347/250000 : ℚ)) : ℝ) 8).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_71_sign
end AxiomAudit
