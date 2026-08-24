import RequestProject.DVPCosSinEval
import RequestProject.DVPLog200Table
import RequestProject.DVPLog250Table
import RequestProject.DVPLog500Table

/-!
# The cosine table at `t = 581/2` (rung-290.5; halved brackets, N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos581o2_br_2 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (2 : ℕ) / 2)) - ((478063/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (2 : ℕ) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 743293/10000000) (δ := 3643/250000000) 581 32
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_3 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (3 : ℕ) / 2)) - ((4246/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log (3 : ℕ) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (3 : ℕ) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -161949/500000) (δ := 1821/125000000) 581 51
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_4 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (4 : ℕ) / 2)) - ((165669/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log (4 : ℕ) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (4 : ℕ) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1486623/10000000) (δ := 14711/1000000000) 581 64
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_5 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (5 : ℕ) / 2)) - ((-424797/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log (5 : ℕ) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (5 : ℕ) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6465029/10000000) (δ := 1467/100000000) 581 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_6 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (6 : ℕ) / 2)) - ((108353/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log (6 : ℕ) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (6 : ℕ) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2495651/10000000) (δ := 229/15625000) 581 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_7 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (7 : ℕ) / 2)) - ((98011/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log (7 : ℕ) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (7 : ℕ) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62431/1250000) (δ := 2931/200000000) 581 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_8 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (8 : ℕ) / 2)) - ((19621/31250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log (8 : ℕ) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (8 : ℕ) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34843/156250) (δ := 14541/1000000000) 581 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_9 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (9 : ℕ) / 2)) - ((-852303/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log (9 : ℕ) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (9 : ℕ) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1619481/2500000) (δ := 14569/1000000000) 581 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_10 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (10 : ℕ) / 2)) - ((-966831/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log (10 : ℕ) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (10 : ℕ) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3604143/5000000) (δ := 1459/100000000) 581 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_11 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (11 : ℕ) / 2)) - ((165933/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log (11 : ℕ) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (11 : ℕ) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2112497/10000000) (δ := 7349/500000000) 581 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_12 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (12 : ℕ) / 2)) - ((191061/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log (12 : ℕ) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (12 : ℕ) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1752321/10000000) (δ := 14627/1000000000) 581 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_13 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (13 : ℕ) / 2)) - ((-847081/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log (13 : ℕ) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (13 : ℕ) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6453163/10000000) (δ := 7353/500000000) 581 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_14 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (14 : ℕ) / 2)) - ((199049/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log (14 : ℕ) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (14 : ℕ) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 121941/5000000) (δ := 14627/1000000000) 581 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_15 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (15 : ℕ) / 2)) - ((276703/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log (15 : ℕ) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (15 : ℕ) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1613043/5000000) (δ := 14699/1000000000) 581 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_16 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (16 : ℕ) / 2)) - ((186149/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log (16 : ℕ) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (16 : ℕ) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2973281/10000000) (δ := 14683/1000000000) 581 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_17 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (17 : ℕ) / 2)) - ((99881/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log (17 : ℕ) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (17 : ℕ) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -121993/10000000) (δ := 14661/1000000000) 581 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_18 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (18 : ℕ) / 2)) - ((-165417/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log (18 : ℕ) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (18 : ℕ) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2867297/5000000) (δ := 7357/500000000) 581 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_19 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (19 : ℕ) / 2)) - ((165687/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log (19 : ℕ) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (19 : ℕ) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2115783/10000000) (δ := 227/15625000) 581 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_20 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (20 : ℕ) / 2)) - ((-499619/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log (20 : ℕ) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (20 : ℕ) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1939087/2500000) (δ := 7327/500000000) 581 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_21 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (21 : ℕ) / 2)) - ((9421/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log (21 : ℕ) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (21 : ℕ) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3738391/10000000) (δ := 7357/500000000) 581 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_22 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (22 : ℕ) / 2)) - ((426871/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log (22 : ℕ) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (22 : ℕ) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -85573/625000) (δ := 227/15625000) 581 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_23 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (23 : ℕ) / 2)) - ((979909/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log (23 : ℕ) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (23 : ℕ) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20079/400000) (δ := 1461/100000000) 581 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_24 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (24 : ℕ) / 2)) - ((459827/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log (24 : ℕ) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (24 : ℕ) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31531/312500) (δ := 3649/250000000) 581 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_25 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (25 : ℕ) / 2)) - ((55451/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log (25 : ℕ) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (25 : ℕ) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2777941/10000000) (δ := 7291/500000000) 581 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_26 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (26 : ℕ) / 2)) - ((-65421/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log (26 : ℕ) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (26 : ℕ) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2854917/5000000) (δ := 1817/125000000) 581 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_27 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (27 : ℕ) / 2)) - ((-734983/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log (27 : ℕ) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (27 : ℕ) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 748887/1250000) (δ := 14693/1000000000) 581 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_28 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (28 : ℕ) / 2)) - ((923041/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log (28 : ℕ) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (28 : ℕ) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 987211/10000000) (δ := 3649/250000000) 581 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_29 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (29 : ℕ) / 2)) - ((-395551/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log (29 : ℕ) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (29 : ℕ) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4943659/10000000) (δ := 14631/1000000000) 581 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_30 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (30 : ℕ) / 2)) - ((-847/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log (30 : ℕ) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (30 : ℕ) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1984671/5000000) (δ := 7337/500000000) 581 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_31 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (31 : ℕ) / 2)) - ((58679/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log (31 : ℕ) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (31 : ℕ) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3632919/10000000) (δ := 14643/1000000000) 581 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_32 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (32 : ℕ) / 2)) - ((84053/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log (32 : ℕ) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (32 : ℕ) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3716611/10000000) (δ := 73/5000000) 581 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_33 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (33 : ℕ) / 2)) - ((-539447/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log (33 : ℕ) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (33 : ℕ) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5351441/10000000) (δ := 2923/200000000) 581 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_34 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (34 : ℕ) / 2)) - ((484637/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log (34 : ℕ) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (34 : ℕ) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 621337/10000000) (δ := 7311/500000000) 581 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_35 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (35 : ℕ) / 2)) - ((-145603/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log (35 : ℕ) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (35 : ℕ) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1193109/2000000) (δ := 7337/500000000) 581 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_36 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (36 : ℕ) / 2)) - ((-412967/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log (36 : ℕ) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (36 : ℕ) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -998253/2000000) (δ := 14543/1000000000) 581 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_37 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (37 : ℕ) / 2)) - ((949147/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log (37 : ℕ) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (37 : ℕ) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -160141/2000000) (δ := 14703/1000000000) 581 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_38 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (38 : ℕ) / 2)) - ((10357/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log (38 : ℕ) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (38 : ℕ) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 357389/1250000) (δ := 2939/200000000) 581 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_39 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (39 : ℕ) / 2)) - ((-741663/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log (39 : ℕ) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (39 : ℕ) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 375991/625000) (δ := 7269/500000000) 581 169
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_40 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (40 : ℕ) / 2)) - ((-471977/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log (40 : ℕ) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (40 : ℕ) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3506509/5000000) (δ := 14629/1000000000) 581 171
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_41 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (41 : ℕ) / 2)) - ((-84407/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log (41 : ℕ) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (41 : ℕ) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4787981/10000000) (δ := 14617/1000000000) 581 172
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_42 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (42 : ℕ) / 2)) - ((182099/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log (42 : ℕ) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (42 : ℕ) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1497531/5000000) (δ := 909/62500000) 581 173
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_43 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (43 : ℕ) / 2)) - ((798739/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log (43 : ℕ) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (43 : ℕ) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -807/5000) (δ := 3663/250000000) 581 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_44 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (44 : ℕ) / 2)) - ((968829/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log (44 : ℕ) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (44 : ℕ) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -625839/10000000) (δ := 2939/200000000) 581 175
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_45 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (45 : ℕ) / 2)) - ((999987/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log (45 : ℕ) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (45 : ℕ) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12931/10000000) (δ := 3647/250000000) 581 176
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_46 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (46 : ℕ) / 2)) - ((497673/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log (46 : ℕ) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (46 : ℕ) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 120641/5000000) (δ := 14531/1000000000) 581 177
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_47 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (47 : ℕ) / 2)) - ((499073/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log (47 : ℕ) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (47 : ℕ) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 152269/10000000) (δ := 7287/500000000) 581 178
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_48 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (48 : ℕ) / 2)) - ((994359/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log (48 : ℕ) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (48 : ℕ) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -132831/5000000) (δ := 14687/1000000000) 581 179
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_49 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (49 : ℕ) / 2)) - ((921227/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log (49 : ℕ) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (49 : ℕ) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -249733/2500000) (δ := 14659/1000000000) 581 180
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_50 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (50 : ℕ) / 2)) - ((686709/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log (50 : ℕ) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (50 : ℕ) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2034611/10000000) (δ := 14701/1000000000) 581 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_51 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (51 : ℕ) / 2)) - ((56123/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log (51 : ℕ) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (51 : ℕ) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -420117/1250000) (δ := 3677/250000000) 581 182
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_52 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (52 : ℕ) / 2)) - ((-403927/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log (52 : ℕ) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (52 : ℕ) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -993301/2000000) (δ := 459/31250000) 581 183
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_53 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (53 : ℕ) / 2)) - ((-918981/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log (53 : ℕ) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (53 : ℕ) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6840713/10000000) (δ := 367/25000000) 581 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_54 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (54 : ℕ) / 2)) - ((-56337/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log (54 : ℕ) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (54 : ℕ) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 269377/400000) (δ := 1453/100000000) 581 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_55 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (55 : ℕ) / 2)) - ((-84691/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log (55 : ℕ) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (55 : ℕ) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 272031/625000) (δ := 367/25000000) 581 185
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_56 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (56 : ℕ) / 2)) - ((192463/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log (56 : ℕ) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (56 : ℕ) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 432617/2500000) (δ := 14537/1000000000) 581 186
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_57 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (57 : ℕ) / 2)) - ((900767/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log (57 : ℕ) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (57 : ℕ) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1123161/10000000) (δ := 14609/1000000000) 581 187
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_58 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (58 : ℕ) / 2)) - ((-54559/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log (58 : ℕ) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (58 : ℕ) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4200329/10000000) (δ := 14651/1000000000) 581 188
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_59 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (59 : ℕ) / 2)) - ((-989621/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log (59 : ℕ) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (59 : ℕ) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1498697/2000000) (δ := 2939/200000000) 581 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_60 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (60 : ℕ) / 2)) - ((-2473/8000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log (60 : ℕ) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (60 : ℕ) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 147271/312500) (δ := 913/62500000) 581 189
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_61 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (61 : ℕ) / 2)) - ((183927/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log (61 : ℕ) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (61 : ℕ) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1009113/10000000) (δ := 7333/500000000) 581 190
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_62 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (62 : ℕ) / 2)) - ((403127/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log (62 : ℕ) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (62 : ℕ) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1444831/5000000) (δ := 14723/1000000000) 581 191
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_63 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (63 : ℕ) / 2)) - ((-939147/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log (63 : ℕ) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (63 : ℕ) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1395467/2000000) (δ := 1463/100000000) 581 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_64 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (64 : ℕ) / 2)) - ((-211541/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log (64 : ℕ) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (64 : ℕ) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1114967/2500000) (δ := 367/25000000) 581 192
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_65 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (65 : ℕ) / 2)) - ((999989/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log (65 : ℕ) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (65 : ℕ) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1183/1000000) (δ := 14687/1000000000) 581 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_66 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (66 : ℕ) / 2)) - ((-26909/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log (66 : ℕ) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (66 : ℕ) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -288007/625000) (δ := 14609/1000000000) 581 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_67 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (67 : ℕ) / 2)) - ((-816007/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log (67 : ℕ) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (67 : ℕ) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6313163/10000000) (δ := 14559/1000000000) 581 194
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_68 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (68 : ℕ) / 2)) - ((427339/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log (68 : ℕ) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (68 : ℕ) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 682333/5000000) (δ := 14601/1000000000) 581 195
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_69 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (69 : ℕ) / 2)) - ((1859/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log (69 : ℕ) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (69 : ℕ) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3740919/10000000) (δ := 7347/500000000) 581 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_70 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (70 : ℕ) / 2)) - ((-22423/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log (70 : ℕ) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (70 : ℕ) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53671/80000) (δ := 14609/1000000000) 581 196
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_71 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (71 : ℕ) / 2)) - ((433663/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log (71 : ℕ) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (71 : ℕ) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1302477/10000000) (δ := 14637/1000000000) 581 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_72 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (72 : ℕ) / 2)) - ((-64013/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log (72 : ℕ) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (72 : ℕ) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33187/78125) (δ := 367/25000000) 581 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_73 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (73 : ℕ) / 2)) - ((-672057/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log (73 : ℕ) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (73 : ℕ) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5769449/10000000) (δ := 14723/1000000000) 581 198
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_74 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (74 : ℕ) / 2)) - ((124967/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log (74 : ℕ) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (74 : ℕ) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7181/1250000) (δ := 14623/1000000000) 581 199
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_75 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (75 : ℕ) / 2)) - ((-741939/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log (75 : ℕ) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (75 : ℕ) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1203377/2000000) (δ := 7333/500000000) 581 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_76 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (76 : ℕ) / 2)) - ((25891/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log (76 : ℕ) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (76 : ℕ) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1801221/5000000) (δ := 14587/1000000000) 581 200
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_77 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (77 : ℕ) / 2)) - ((251053/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log (77 : ℕ) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (77 : ℕ) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2611909/10000000) (δ := 913/62500000) 581 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_78 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (78 : ℕ) / 2)) - ((-226409/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log (78 : ℕ) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (78 : ℕ) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1351837/2000000) (δ := 3677/250000000) 581 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_79 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (79 : ℕ) / 2)) - ((248167/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log (79 : ℕ) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (79 : ℕ) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 302921/10000000) (δ := 1819/125000000) 581 202
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_80 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (80 : ℕ) / 2)) - ((-100729/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log (80 : ℕ) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (80 : ℕ) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6269689/10000000) (δ := 7297/500000000) 581 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_81 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (81 : ℕ) / 2)) - ((452829/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log (81 : ℕ) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (81 : ℕ) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 344019/1250000) (δ := 14609/1000000000) 581 203
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_82 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (82 : ℕ) / 2)) - ((-47047/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log (82 : ℕ) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (82 : ℕ) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4044651/10000000) (δ := 7333/500000000) 581 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_83 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (83 : ℕ) / 2)) - ((-326511/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log (83 : ℕ) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (83 : ℕ) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 951703/2000000) (δ := 14687/1000000000) 581 204
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_84 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (84 : ℕ) / 2)) - ((9704/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log (84 : ℕ) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (84 : ℕ) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2251769/10000000) (δ := 727/25000000) 581 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_85 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (85 : ℕ) / 2)) - ((-822847/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log (85 : ℕ) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (85 : ℕ) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6343/10000) (δ := 367/25000000) 581 205
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_86 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (86 : ℕ) / 2)) - ((187991/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log (86 : ℕ) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (86 : ℕ) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -870743/10000000) (δ := 14573/1000000000) 581 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_87 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (87 : ℕ) / 2)) - ((-991373/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log (87 : ℕ) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (87 : ℕ) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7525361/10000000) (δ := 1463/100000000) 581 206
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_88 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (88 : ℕ) / 2)) - ((62431/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log (88 : ℕ) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (88 : ℕ) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 117491/10000000) (δ := 3647/250000000) 581 207
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_89 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (89 : ℕ) / 2)) - ((-982397/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log (89 : ℕ) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (89 : ℕ) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7384211/10000000) (δ := 3677/250000000) 581 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_90 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (90 : ℕ) / 2)) - ((119703/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log (90 : ℕ) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (90 : ℕ) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 730399/10000000) (δ := 2939/200000000) 581 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_91 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (91 : ℕ) / 2)) - ((-116963/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log (91 : ℕ) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (91 : ℕ) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6952611/10000000) (δ := 14551/500000000) 581 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_92 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (92 : ℕ) / 2)) - ((923441/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log (92 : ℕ) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (92 : ℕ) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 984611/10000000) (δ := 14701/1000000000) 581 209
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_93 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (93 : ℕ) / 2)) - ((-461917/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log (93 : ℕ) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (93 : ℕ) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53687/78125) (δ := 3661/250000000) 581 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_94 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (94 : ℕ) / 2)) - ((468263/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log (94 : ℕ) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (94 : ℕ) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 447763/5000000) (δ := 14559/1000000000) 581 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_95 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (95 : ℕ) / 2)) - ((-479019/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log (95 : ℕ) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (95 : ℕ) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7127187/10000000) (δ := 1827/125000000) 581 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_96 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (96 : ℕ) / 2)) - ((61363/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log (96 : ℕ) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (96 : ℕ) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 238797/5000000) (δ := 14687/1000000000) 581 211
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_97 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (97 : ℕ) / 2)) - ((-99821/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log (97 : ℕ) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (97 : ℕ) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1540877/2000000) (δ := 7337/500000000) 581 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_98 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (98 : ℕ) / 2)) - ((497389/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log (98 : ℕ) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (98 : ℕ) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -127801/5000000) (δ := 457/31250000) 581 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_99 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (99 : ℕ) / 2)) - ((-95693/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log (99 : ℕ) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (99 : ℕ) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3558789/5000000) (δ := 14629/1000000000) 581 212
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_100 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (100 : ℕ) / 2)) - ((217383/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log (100 : ℕ) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (100 : ℕ) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -258271/2000000) (δ := 917/62500000) 581 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_101 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (101 : ℕ) / 2)) - ((-719619/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log (101 : ℕ) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (101 : ℕ) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5935123/10000000) (δ := 917/62500000) 581 213
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_102 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (102 : ℕ) / 2)) - ((250067/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log (102 : ℕ) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (102 : ℕ) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2617607/10000000) (δ := 7269/500000000) 581 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_103 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (103 : ℕ) / 2)) - ((-1717/8000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log (103 : ℕ) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (103 : ℕ) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4467761/10000000) (δ := 459/31250000) 581 214
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_104 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (104 : ℕ) / 2)) - ((-59113/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log (104 : ℕ) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (104 : ℕ) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -263953/625000) (δ := 913/62500000) 581 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_105 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (105 : ℕ) / 2)) - ((461917/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log (105 : ℕ) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (105 : ℕ) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1363301/5000000) (δ := 2939/200000000) 581 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_106 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (106 : ℕ) / 2)) - ((-381579/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log (106 : ℕ) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (106 : ℕ) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -381091/625000) (δ := 14601/1000000000) 581 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_107 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (107 : ℕ) / 2)) - ((958599/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log (107 : ℕ) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (107 : ℕ) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 360943/5000000) (δ := 14701/1000000000) 581 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_108 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (108 : ℕ) / 2)) - ((-494349/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log (108 : ℕ) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (108 : ℕ) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3738877/5000000) (δ := 14701/1000000000) 581 216
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_109 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (109 : ℕ) / 2)) - ((816969/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log (109 : ℕ) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (109 : ℕ) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1536653/10000000) (δ := 14559/1000000000) 581 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_110 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (110 : ℕ) / 2)) - ((-225343/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log (110 : ℕ) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (110 : ℕ) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 203833/400000) (δ := 909/62500000) 581 217
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_111 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (111 : ℕ) / 2)) - ((-5631/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log (111 : ℕ) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (111 : ℕ) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -126239/312500) (δ := 14667/1000000000) 581 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_112 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (112 : ℕ) / 2)) - ((137273/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log (112 : ℕ) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (112 : ℕ) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2473797/10000000) (δ := 7343/500000000) 581 218
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_113 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (113 : ℕ) / 2)) - ((-90889/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log (113 : ℕ) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (113 : ℕ) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -677853/1000000) (δ := 14679/1000000000) 581 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_114 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (114 : ℕ) / 2)) - ((3089/3125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log (114 : ℕ) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (114 : ℕ) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -379831/10000000) (δ := 7337/500000000) 581 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_115 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (115 : ℕ) / 2)) - ((-727321/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log (115 : ℕ) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (115 : ℕ) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2981509/5000000) (δ := 14629/1000000000) 581 219
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_116 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (116 : ℕ) / 2)) - ((93431/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log (116 : ℕ) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (116 : ℕ) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3457073/10000000) (δ := 7361/500000000) 581 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_117 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (117 : ℕ) / 2)) - ((55497/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log (117 : ℕ) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (117 : ℕ) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 173557/625000) (δ := 7311/500000000) 581 220
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_118 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (118 : ℕ) / 2)) - ((-904099/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log (118 : ℕ) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (118 : ℕ) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1350031/2000000) (δ := 3647/250000000) 581 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_119 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (119 : ℕ) / 2)) - ((48463/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log (119 : ℕ) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (119 : ℕ) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -621477/10000000) (δ := 2933/200000000) 581 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_120 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (120 : ℕ) / 2)) - ((-574181/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log (120 : ℕ) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (120 : ℕ) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5456001/10000000) (δ := 2923/200000000) 581 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_121 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (121 : ℕ) / 2)) - ((-23781/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log (121 : ℕ) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (121 : ℕ) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4224959/10000000) (δ := 3677/250000000) 581 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_122 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (122 : ℕ) / 2)) - ((764213/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log (122 : ℕ) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (122 : ℕ) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 876221/5000000) (δ := 7279/500000000) 581 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_123 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (123 : ℕ) / 2)) - ((-124701/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log (123 : ℕ) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (123 : ℕ) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7681039/10000000) (δ := 2929/200000000) 581 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_124 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (124 : ℕ) / 2)) - ((163387/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log (124 : ℕ) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (124 : ℕ) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2146333/10000000) (δ := 14553/1000000000) 581 223
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_125 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (125 : ℕ) / 2)) - ((23957/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log (125 : ℕ) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (125 : ℕ) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 921763/2500000) (δ := 73/5000000) 581 223
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_126 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (126 : ℕ) / 2)) - ((-398649/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log (126 : ℕ) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (126 : ℕ) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3117003/5000000) (δ := 14593/1000000000) 581 224
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_127 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (127 : ℕ) / 2)) - ((1569/1600 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log (127 : ℕ) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (127 : ℕ) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -492927/10000000) (δ := 14543/1000000000) 581 224
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_128 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (128 : ℕ) / 2)) - ((-244299/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log (128 : ℕ) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (128 : ℕ) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5203197/10000000) (δ := 14543/1000000000) 581 224
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_129 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (129 : ℕ) / 2)) - ((-361971/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log (129 : ℕ) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (129 : ℕ) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4852943/10000000) (δ := 14717/1000000000) 581 225
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_130 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (130 : ℕ) / 2)) - ((38189/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log (130 : ℕ) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (130 : ℕ) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 755159/10000000) (δ := 1817/125000000) 581 225
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_131 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (131 : ℕ) / 2)) - ((-817663/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log (131 : ℕ) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (131 : ℕ) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 316017/500000) (δ := 7293/500000000) 581 225
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_132 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (132 : ℕ) / 2)) - ((24881/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log (132 : ℕ) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (132 : ℕ) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1932391/5000000) (δ := 7337/500000000) 581 226
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_133 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (133 : ℕ) / 2)) - ((99771/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log (133 : ℕ) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (133 : ℕ) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 404093/2500000) (δ := 7337/500000000) 581 226
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_134 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (134 : ℕ) / 2)) - ((-474773/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log (134 : ℕ) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (134 : ℕ) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 882057/1250000) (δ := 29129/1000000000) 581 226
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_135 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (135 : ℕ) / 2)) - ((33347/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log (135 : ℕ) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (135 : ℕ) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5203/16000) (δ := 917/62500000) 581 227
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_136 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (136 : ℕ) / 2)) - ((6651/10000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log (136 : ℕ) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (136 : ℕ) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2107923/10000000) (δ := 14531/1000000000) 581 227
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_137 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (137 : ℕ) / 2)) - ((-61597/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log (137 : ℕ) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (137 : ℕ) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7428503/10000000) (δ := 3643/250000000) 581 227
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_138 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (138 : ℕ) / 2)) - ((363229/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log (138 : ℕ) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (138 : ℕ) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1498831/5000000) (δ := 2923/200000000) 581 228
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_139 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (139 : ℕ) / 2)) - ((622837/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log (139 : ℕ) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (139 : ℕ) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2246081/10000000) (δ := 2913/200000000) 581 228
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_140 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (140 : ℕ) / 2)) - ((-493557/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log (140 : ℕ) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (140 : ℕ) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1863051/2500000) (δ := 2923/200000000) 581 228
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_141 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (141 : ℕ) / 2)) - ((65961/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log (141 : ℕ) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (141 : ℕ) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3086747/10000000) (δ := 7323/500000000) 581 229
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_142 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (142 : ℕ) / 2)) - ((683447/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log (142 : ℕ) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (142 : ℕ) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2045807/10000000) (δ := 7323/500000000) 581 229
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_143 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (143 : ℕ) / 2)) - ((-479879/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log (143 : ℕ) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (143 : ℕ) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7142339/10000000) (δ := 7323/500000000) 581 229
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_144 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (144 : ℕ) / 2)) - ((84061/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log (144 : ℕ) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (144 : ℕ) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3504679/10000000) (δ := 73/5000000) 581 230
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_145 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (145 : ℕ) / 2)) - ((820487/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log (145 : ℕ) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (145 : ℕ) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 760667/5000000) (δ := 293/20000000) 581 230
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_146 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (146 : ℕ) / 2)) - ((-107439/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log (146 : ℕ) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (146 : ℕ) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3256389/5000000) (δ := 14553/1000000000) 581 230
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_147 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (147 : ℕ) / 2)) - ((-124033/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log (147 : ℕ) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (147 : ℕ) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33903/80000) (δ := 1471/100000000) 581 231
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_148 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (148 : ℕ) / 2)) - ((962601/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log (148 : ℕ) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (148 : ℕ) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 342941/5000000) (δ := 733/50000000) 581 231
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_149 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (149 : ℕ) / 2)) - ((-612969/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log (149 : ℕ) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (149 : ℕ) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2788261/5000000) (δ := 1461/100000000) 581 231
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_150 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (150 : ℕ) / 2)) - ((-256491/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log (150 : ℕ) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (150 : ℕ) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1318407/2500000) (δ := 7293/500000000) 581 232
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_151 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (151 : ℕ) / 2)) - ((245997/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log (151 : ℕ) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (151 : ℕ) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -447987/10000000) (δ := 14567/1000000000) 581 232
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_152 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (152 : ℕ) / 2)) - ((-16673/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log (152 : ℕ) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (152 : ℕ) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4345771/10000000) (δ := 3659/250000000) 581 232
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_153 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (153 : ℕ) / 2)) - ((-175359/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log (153 : ℕ) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (153 : ℕ) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -164997/250000) (δ := 457/31250000) 581 233
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_154 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (154 : ℕ) / 2)) - ((733437/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log (154 : ℕ) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (154 : ℕ) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1868579/10000000) (δ := 7337/500000000) 581 233
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_155 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (155 : ℕ) / 2)) - ((424099/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log (155 : ℕ) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (155 : ℕ) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1416037/5000000) (δ := 457/31250000) 581 233
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_156 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (156 : ℕ) / 2)) - ((-495067/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log (156 : ℕ) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (156 : ℕ) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1500503/2000000) (δ := 7287/500000000) 581 233
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_157 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (157 : ℕ) / 2)) - ((36087/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log (157 : ℕ) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (157 : ℕ) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -445607/1250000) (δ := 7291/500000000) 581 234
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_158 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (158 : ℕ) / 2)) - ((9137/10000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log (158 : ℕ) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (158 : ℕ) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 837/8000) (δ := 14671/1000000000) 581 234
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_159 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (159 : ℕ) / 2)) - ((-314601/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log (159 : ℕ) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (159 : ℕ) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5628307/10000000) (δ := 7291/500000000) 581 234
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_160 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (160 : ℕ) / 2)) - ((-596993/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log (160 : ℕ) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (160 : ℕ) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5526359/10000000) (δ := 14689/1000000000) 581 235
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_161 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (161 : ℕ) / 2)) - ((460417/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log (161 : ℕ) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (161 : ℕ) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1001459/10000000) (δ := 7307/500000000) 581 235
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_162 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (162 : ℕ) / 2)) - ((42937/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log (162 : ℕ) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (162 : ℕ) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3495481/10000000) (δ := 7307/500000000) 581 235
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_163 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (163 : ℕ) / 2)) - ((-999019/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log (163 : ℕ) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (163 : ℕ) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1935803/2500000) (δ := 3649/250000000) 581 236
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_164 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (164 : ℕ) / 2)) - ((247663/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log (164 : ℕ) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (164 : ℕ) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1650661/5000000) (δ := 14557/1000000000) 581 236
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_165 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (165 : ℕ) / 2)) - ((902429/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log (165 : ℕ) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (165 : ℕ) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 69597/625000) (δ := 3649/250000000) 581 236
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_166 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (166 : ℕ) / 2)) - ((-294537/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log (166 : ℕ) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (166 : ℕ) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1375443/2500000) (δ := 14607/1000000000) 581 236
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_167 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (167 : ℕ) / 2)) - ((-86739/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log (167 : ℕ) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (167 : ℕ) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5844261/10000000) (δ := 291/20000000) 581 237
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_168 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (168 : ℕ) / 2)) - ((823417/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log (168 : ℕ) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (168 : ℕ) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -377119/2500000) (δ := 73/5000000) 581 237
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_169 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (169 : ℕ) / 2)) - ((10877/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log (169 : ℕ) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (169 : ℕ) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2801673/10000000) (δ := 14653/1000000000) 581 237
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_170 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (170 : ℕ) / 2)) - ((-476613/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log (170 : ℕ) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (170 : ℕ) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 708633/1000000) (δ := 14603/1000000000) 581 237
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_171 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (171 : ℕ) / 2)) - ((-10823/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log (171 : ℕ) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (171 : ℕ) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -872421/2000000) (δ := 14693/1000000000) 581 238
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_172 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (172 : ℕ) / 2)) - ((499351/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log (172 : ℕ) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (172 : ℕ) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -127413/10000000) (δ := 1471/100000000) 581 238
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_173 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (173 : ℕ) / 2)) - ((-12451/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log (173 : ℕ) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (173 : ℕ) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 408273/1000000) (δ := 14693/1000000000) 581 238
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_174 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (174 : ℕ) / 2)) - ((-493139/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log (174 : ℕ) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (174 : ℕ) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3719673/5000000) (δ := 3659/250000000) 581 239
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_175 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (175 : ℕ) / 2)) - ((256913/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log (175 : ℕ) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (175 : ℕ) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -131097/400000) (δ := 7293/500000000) 581 239
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_176 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (176 : ℕ) / 2)) - ((14708/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log (176 : ℕ) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (176 : ℕ) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 215187/2500000) (δ := 14667/1000000000) 581 239
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_177 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (177 : ℕ) / 2)) - ((-407229/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log (177 : ℕ) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (177 : ℕ) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 995107/2000000) (δ := 14567/1000000000) 581 239
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_178 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (178 : ℕ) / 2)) - ((-884563/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log (178 : ℕ) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (178 : ℕ) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6640881/10000000) (δ := 583/40000000) 581 240
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_179 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (179 : ℕ) / 2)) - ((20631/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log (179 : ℕ) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (179 : ℕ) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2572211/10000000) (δ := 3657/250000000) 581 240
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_180 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (180 : ℕ) / 2)) - ((103903/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log (180 : ℕ) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (180 : ℕ) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23027/156250) (δ := 227/15625000) 581 240
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_181 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (181 : ℕ) / 2)) - ((-587627/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log (181 : ℕ) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (181 : ℕ) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2748649/5000000) (δ := 3657/250000000) 581 240
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_182 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (182 : ℕ) / 2)) - ((-791299/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log (182 : ℕ) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (182 : ℕ) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3104659/5000000) (δ := 3633/250000000) 581 241
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_183 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (183 : ℕ) / 2)) - ((627909/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log (183 : ℕ) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (183 : ℕ) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2229831/10000000) (δ := 7291/500000000) 581 241
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_184 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (184 : ℕ) / 2)) - ((770497/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log (184 : ℕ) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (184 : ℕ) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1727941/10000000) (δ := 7291/500000000) 581 241
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_185 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (185 : ℕ) / 2)) - ((-640323/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log (185 : ℕ) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (185 : ℕ) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 177009/312500) (δ := 14721/1000000000) 581 241
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_186 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (186 : ℕ) / 2)) - ((-15423/20000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log (186 : ℕ) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (186 : ℕ) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3064303/5000000) (δ := 14639/1000000000) 581 242
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_187 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (187 : ℕ) / 2)) - ((626469/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log (187 : ℕ) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (187 : ℕ) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1117227/5000000) (δ := 7307/500000000) 581 242
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_188 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (188 : ℕ) / 2)) - ((396359/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log (188 : ℕ) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (188 : ℕ) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 327771/2000000) (δ := 1833/125000000) 581 242
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_189 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (189 : ℕ) / 2)) - ((-36613/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log (189 : ℕ) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (189 : ℕ) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1372921/2500000) (δ := 7307/500000000) 581 242
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_190 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (190 : ℕ) / 2)) - ((-104003/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log (190 : ℕ) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (190 : ℕ) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3191929/5000000) (δ := 14607/1000000000) 581 243
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_191 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (191 : ℕ) / 2)) - ((20641/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log (191 : ℕ) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (191 : ℕ) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2571481/10000000) (δ := 7273/500000000) 581 243
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_192 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (192 : ℕ) / 2)) - ((883099/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log (192 : ℕ) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (192 : ℕ) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 305231/2500000) (δ := 3649/250000000) 581 243
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_193 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (193 : ℕ) / 2)) - ((-82767/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log (193 : ℕ) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (193 : ℕ) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4993647/10000000) (δ := 14657/1000000000) 581 243
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_194 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (194 : ℕ) / 2)) - ((-93689/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log (194 : ℕ) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (194 : ℕ) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -217533/312500) (δ := 291/20000000) 581 244
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_195 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (195 : ℕ) / 2)) - ((69077/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log (195 : ℕ) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (195 : ℕ) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1613557/5000000) (δ := 14603/1000000000) 581 244
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_196 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (196 : ℕ) / 2)) - ((98103/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log (196 : ℕ) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (196 : ℕ) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 487727/10000000) (δ := 73/5000000) 581 244
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_197 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (197 : ℕ) / 2)) - ((-51249/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log (197 : ℕ) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (197 : ℕ) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2091843/5000000) (δ := 291/20000000) 581 244
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_198 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (198 : ℕ) / 2)) - ((-249999/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log (198 : ℕ) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (198 : ℕ) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -490441/625000) (δ := 14693/1000000000) 581 245
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_199 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (199 : ℕ) / 2)) - ((-20871/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log (199 : ℕ) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (199 : ℕ) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4188353/10000000) (δ := 733/50000000) 581 245
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_200 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (200 : ℕ) / 2)) - ((97607/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log (200 : ℕ) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (200 : ℕ) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21921/400000) (δ := 1461/100000000) 581 245
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_201 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (201 : ℕ) / 2)) - ((83633/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log (201 : ℕ) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (201 : ℕ) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3074219/10000000) (δ := 14643/1000000000) 581 245
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_202 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (202 : ℕ) / 2)) - ((-891459/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log (202 : ℕ) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (202 : ℕ) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 333919/500000) (δ := 14593/1000000000) 581 245
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_203 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (203 : ℕ) / 2)) - ((-569963/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log (203 : ℕ) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (203 : ℕ) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5443143/10000000) (δ := 2927/200000000) 581 246
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_204 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (204 : ℕ) / 2)) - ((365933/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log (204 : ℕ) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (204 : ℕ) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37487/200000) (δ := 7309/500000000) 581 246
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_205 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (205 : ℕ) / 2)) - ((391661/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log (205 : ℕ) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (205 : ℕ) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 419253/2500000) (δ := 2927/200000000) 581 246
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_206 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (206 : ℕ) / 2)) - ((-491351/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log (206 : ℕ) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (206 : ℕ) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 521109/1000000) (δ := 2907/200000000) 581 246
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_207 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (207 : ℕ) / 2)) - ((-939503/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log (207 : ℕ) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (207 : ℕ) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1395987/2000000) (δ := 227/15625000) 581 247
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_208 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (208 : ℕ) / 2)) - ((177877/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log (208 : ℕ) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (208 : ℕ) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1739959/5000000) (δ := 587/40000000) 581 247
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_209 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (209 : ℕ) / 2)) - ((999999/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log (209 : ℕ) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (209 : ℕ) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1661/5000000) (δ := 583/40000000) 581 247
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_210 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (210 : ℕ) / 2)) - ((181807/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log (210 : ℕ) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (210 : ℕ) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3469931/10000000) (δ := 227/15625000) 581 247
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_211 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (211 : ℕ) / 2)) - ((-93103/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log (211 : ℕ) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (211 : ℕ) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3460027/5000000) (δ := 3657/250000000) 581 247
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_212 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (212 : ℕ) / 2)) - ((-540351/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log (212 : ℕ) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (212 : ℕ) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2677063/5000000) (δ := 7341/500000000) 581 248
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_213 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (213 : ℕ) / 2)) - ((71471/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log (213 : ℕ) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (213 : ℕ) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1936467/10000000) (δ := 14721/1000000000) 581 248
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_214 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (214 : ℕ) / 2)) - ((104139/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log (214 : ℕ) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (214 : ℕ) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11447/78125) (δ := 7291/500000000) 581 248
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_215 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (215 : ℕ) / 2)) - ((-361243/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log (215 : ℕ) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (215 : ℕ) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4850993/10000000) (δ := 14671/1000000000) 581 248
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_216 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (216 : ℕ) / 2)) - ((-494619/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log (216 : ℕ) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (216 : ℕ) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7486879/10000000) (δ := 14689/1000000000) 581 249
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_217 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (217 : ℕ) / 2)) - ((-10259/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log (217 : ℕ) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (217 : ℕ) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4132403/10000000) (δ := 14639/1000000000) 581 249
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_218 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (218 : ℕ) / 2)) - ((118759/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log (218 : ℕ) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (218 : ℕ) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -198331/2500000) (δ := 1833/125000000) 581 249
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_219 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (219 : ℕ) / 2)) - ((105999/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log (219 : ℕ) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (219 : ℕ) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 506101/2000000) (δ := 14639/1000000000) 581 249
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_220 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (220 : ℕ) / 2)) - ((-17311/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log (220 : ℕ) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (220 : ℕ) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2919577/5000000) (δ := 7357/500000000) 581 249
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_221 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (221 : ℕ) / 2)) - ((-871989/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log (221 : ℕ) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (221 : ℕ) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -82189/125000) (δ := 14607/1000000000) 581 250
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_222 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (222 : ℕ) / 2)) - ((249573/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log (222 : ℕ) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (222 : ℕ) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -412049/1250000) (δ := 14707/1000000000) 581 250
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_223 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (223 : ℕ) / 2)) - ((249979/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log (223 : ℕ) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (223 : ℕ) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16167/5000000) (δ := 14707/1000000000) 581 250
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_224 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (224 : ℕ) / 2)) - ((56029/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log (224 : ℕ) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (224 : ℕ) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3217127/10000000) (δ := 3649/250000000) 581 250
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_225 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (225 : ℕ) / 2)) - ((-846863/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log (225 : ℕ) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (225 : ℕ) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1290427/2000000) (δ := 3649/250000000) 581 250
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_226 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (226 : ℕ) / 2)) - ((-746841/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log (226 : ℕ) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (226 : ℕ) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6035237/10000000) (δ := 29249/1000000000) 581 251
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_227 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (227 : ℕ) / 2)) - ((212641/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log (227 : ℕ) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (227 : ℕ) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1414403/5000000) (δ := 919/62500000) 581 251
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_228 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (228 : ℕ) / 2)) - ((123681/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log (228 : ℕ) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (228 : ℕ) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 181749/5000000) (δ := 14549/1000000000) 581 251
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_229 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (229 : ℕ) / 2)) - ((38361/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log (229 : ℕ) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (229 : ℕ) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3541859/10000000) (δ := 919/62500000) 581 251
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_230 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (230 : ℕ) / 2)) - ((-112059/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log (230 : ℕ) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (230 : ℕ) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1676587/2500000) (δ := 7327/500000000) 581 251
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_231 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (231 : ℕ) / 2)) - ((-10872/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log (231 : ℕ) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (231 : ℕ) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5850853/10000000) (δ := 3673/250000000) 581 252
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_232 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (232 : ℕ) / 2)) - ((466473/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log (232 : ℕ) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (232 : ℕ) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2713743/10000000) (δ := 14561/1000000000) 581 252
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_233 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (233 : ℕ) / 2)) - ((986587/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log (233 : ℕ) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (233 : ℕ) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 409931/10000000) (δ := 14611/1000000000) 581 252
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_234 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (234 : ℕ) / 2)) - ((161983/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log (234 : ℕ) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (234 : ℕ) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1760121/5000000) (δ := 14661/1000000000) 581 252
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_235 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (235 : ℕ) / 2)) - ((-880117/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log (235 : ℕ) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (235 : ℕ) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3308631/5000000) (δ := 57/3906250) 581 252
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_236 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (236 : ℕ) / 2)) - ((-147847/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log (236 : ℕ) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (236 : ℕ) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3003413/5000000) (δ := 2927/200000000) 581 253
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_237 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (237 : ℕ) / 2)) - ((48261/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log (237 : ℕ) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (237 : ℕ) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2936023/10000000) (δ := 2917/200000000) 581 253
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_238 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (238 : ℕ) / 2)) - ((249703/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log (238 : ℕ) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (238 : ℕ) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 121853/10000000) (δ := 7309/500000000) 581 253
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_239 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (239 : ℕ) / 2)) - ((74839/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log (239 : ℕ) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (239 : ℕ) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1583473/5000000) (δ := 2937/200000000) 581 253
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_240 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (240 : ℕ) / 2)) - ((-15777/20000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log (240 : ℕ) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (240 : ℕ) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6199331/10000000) (δ := 3667/250000000) 581 253
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_241 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (241 : ℕ) / 2)) - ((-213647/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log (241 : ℕ) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (241 : ℕ) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1297777/2000000) (δ := 583/40000000) 581 254
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_242 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (242 : ℕ) / 2)) - ((44301/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log (242 : ℕ) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (242 : ℕ) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3481629/10000000) (δ := 583/40000000) 581 254
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_243 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (243 : ℕ) / 2)) - ((981103/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log (243 : ℕ) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (243 : ℕ) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60849/1250000) (δ := 227/15625000) 581 254
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_244 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (244 : ℕ) / 2)) - ((21669/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log (244 : ℕ) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (244 : ℕ) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 623943/2500000) (δ := 589/40000000) 581 254
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_245 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (245 : ℕ) / 2)) - ((-577483/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log (245 : ℕ) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (245 : ℕ) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2733049/5000000) (δ := 1167/40000000) 581 254
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_246 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (246 : ℕ) / 2)) - ((-194817/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log (246 : ℕ) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (246 : ℕ) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1456719/2000000) (δ := 7291/500000000) 581 255
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_247 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (247 : ℕ) / 2)) - ((-32681/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log (247 : ℕ) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (247 : ℕ) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67771/156250) (δ := 7291/500000000) 581 255
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_248 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (248 : ℕ) / 2)) - ((105827/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log (248 : ℕ) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (248 : ℕ) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -350751/2500000) (δ := 14671/1000000000) 581 255
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_249 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (249 : ℕ) / 2)) - ((820907/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log (249 : ℕ) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (249 : ℕ) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1519499/10000000) (δ := 3633/250000000) 581 255
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_250 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (250 : ℕ) / 2)) - ((-199999/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log (250 : ℕ) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (250 : ℕ) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2215191/5000000) (δ := 7341/500000000) 581 255
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_251 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (251 : ℕ) / 2)) - ((-6113/6250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log (251 : ℕ) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (251 : ℕ) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1832393/2500000) (δ := 7341/500000000) 581 255
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_252 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (252 : ℕ) / 2)) - ((-117101/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log (252 : ℕ) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (252 : ℕ) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5490749/10000000) (δ := 14539/1000000000) 581 256
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_253 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (253 : ℕ) / 2)) - ((501207/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log (253 : ℕ) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (253 : ℕ) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2614509/10000000) (δ := 7357/500000000) 581 256
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_254 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (254 : ℕ) / 2)) - ((248747/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log (254 : ℕ) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (254 : ℕ) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 125201/5000000) (δ := 7357/500000000) 581 256
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_255 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (255 : ℕ) / 2)) - ((323261/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log (255 : ℕ) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (255 : ℕ) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3104057/10000000) (δ := 14689/1000000000) 581 256
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_256 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (256 : ℕ) / 2)) - ((-361389/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log (256 : ℕ) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (256 : ℕ) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2973263/5000000) (δ := 7357/500000000) 581 256
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_257 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (257 : ℕ) / 2)) - ((-466243/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log (257 : ℕ) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (257 : ℕ) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6930079/10000000) (δ := 7353/500000000) 581 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_258 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (258 : ℕ) / 2)) - ((-73013/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log (258 : ℕ) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (258 : ℕ) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4109687/10000000) (δ := 229/15625000) 581 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_259 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (259 : ℕ) / 2)) - ((433891/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log (259 : ℕ) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (259 : ℕ) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1300189/10000000) (δ := 7353/500000000) 581 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_260 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (260 : ℕ) / 2)) - ((825677/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log (260 : ℕ) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (260 : ℕ) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 187311/1250000) (δ := 7353/500000000) 581 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_261 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (261 : ℕ) / 2)) - ((-35819/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log (261 : ℕ) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (261 : ℕ) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4286417/10000000) (δ := 14547/1000000000) 581 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_262 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (262 : ℕ) / 2)) - ((-950447/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log (262 : ℕ) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (262 : ℕ) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 706367/1000000) (δ := 43747/1000000000) 581 257
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_263 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (263 : ℕ) / 2)) - ((-140693/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log (263 : ℕ) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (263 : ℕ) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1469411/2500000) (δ := 7327/500000000) 581 258
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_264 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (264 : ℕ) / 2)) - ((79167/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log (264 : ℕ) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (264 : ℕ) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3121453/10000000) (δ := 43599/1000000000) 581 258
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_265 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (265 : ℕ) / 2)) - ((123591/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log (265 : ℕ) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (265 : ℕ) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9393/250000) (δ := 14699/1000000000) 581 258
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_266 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (266 : ℕ) / 2)) - ((11733/20000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log (266 : ℕ) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (266 : ℕ) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2359701/10000000) (δ := 14549/1000000000) 581 258
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_267 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (267 : ℕ) / 2)) - ((-111687/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log (267 : ℕ) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (267 : ℕ) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5084809/10000000) (δ := 7277/500000000) 581 258
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_268 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (268 : ℕ) / 2)) - ((-199953/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log (268 : ℕ) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (268 : ℕ) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7799749/10000000) (δ := 14649/1000000000) 581 258
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_269 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (269 : ℕ) / 2)) - ((-244329/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log (269 : ℕ) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (269 : ℕ) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -650421/1250000) (δ := 14711/1000000000) 581 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_270 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (270 : ℕ) / 2)) - ((537423/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log (270 : ℕ) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (270 : ℕ) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -501709/2000000) (δ := 14611/1000000000) 581 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_271 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (271 : ℕ) / 2)) - ((498757/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log (271 : ℕ) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (271 : ℕ) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22041/1250000) (δ := 3673/250000000) 581 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_272 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (272 : ℕ) / 2)) - ((417139/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log (272 : ℕ) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (272 : ℕ) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 712813/2500000) (δ := 3673/250000000) 581 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_273 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (273 : ℕ) / 2)) - ((-593783/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log (273 : ℕ) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (273 : ℕ) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1379093/2500000) (δ := 7271/500000000) 581 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_274 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (274 : ℕ) / 2)) - ((-991929/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log (274 : ℕ) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (274 : ℕ) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7536131/10000000) (δ := 2927/200000000) 581 260
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_275 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (275 : ℕ) / 2)) - ((-93981/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log (275 : ℕ) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (275 : ℕ) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -195619/400000) (δ := 2937/200000000) 581 260
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_276 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (276 : ℕ) / 2)) - ((155063/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log (276 : ℕ) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (276 : ℕ) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -563583/2500000) (δ := 3667/250000000) 581 260
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_277 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (277 : ℕ) / 2)) - ((247233/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log (277 : ℕ) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (277 : ℕ) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46537/1250000) (δ := 2907/200000000) 581 260
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_278 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (278 : ℕ) / 2)) - ((183151/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log (278 : ℕ) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (278 : ℕ) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2989411/10000000) (δ := 7359/500000000) 581 260
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_279 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (279 : ℕ) / 2)) - ((-309723/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log (279 : ℕ) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (279 : ℕ) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1399271/2500000) (δ := 7309/500000000) 581 260
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_280 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (280 : ℕ) / 2)) - ((-495341/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log (280 : ℕ) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (280 : ℕ) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -751243/1000000) (δ := 7339/500000000) 581 261
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_281 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (281 : ℕ) / 2)) - ((-97019/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log (281 : ℕ) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (281 : ℕ) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1230837/2500000) (δ := 587/40000000) 581 261
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_282 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (282 : ℕ) / 2)) - ((73989/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log (282 : ℕ) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (282 : ℕ) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1171709/5000000) (δ := 7289/500000000) 581 261
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_283 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (283 : ℕ) / 2)) - ((995867/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log (283 : ℕ) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (283 : ℕ) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 113681/5000000) (δ := 583/40000000) 581 261
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_284 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (284 : ℕ) / 2)) - ((43959/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log (284 : ℕ) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (284 : ℕ) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 174321/625000) (δ := 7289/500000000) 581 261
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_285 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (285 : ℕ) / 2)) - ((-536207/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log (285 : ℕ) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (285 : ℕ) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 667729/1250000) (δ := 3657/250000000) 581 261
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_286 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (286 : ℕ) / 2)) - ((-12499/12500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log (286 : ℕ) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (286 : ℕ) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1564459/2000000) (δ := 14583/1000000000) 581 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_287 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (287 : ℕ) / 2)) - ((-5177/10000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log (287 : ℕ) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (287 : ℕ) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -165231/312500) (δ := 14583/1000000000) 581 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_288 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (288 : ℕ) / 2)) - ((224773/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log (288 : ℕ) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (288 : ℕ) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2761349/10000000) (δ := 14683/1000000000) 581 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_289 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (289 : ℕ) / 2)) - ((24881/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log (289 : ℕ) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (289 : ℕ) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -122011/5000000) (δ := 1467/100000000) 581 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_290 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (290 : ℕ) / 2)) - ((123401/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log (290 : ℕ) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (290 : ℕ) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 283083/1250000) (δ := 14633/1000000000) 581 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_291 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (291 : ℕ) / 2)) - ((-328823/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log (291 : ℕ) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (291 : ℕ) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2382317/5000000) (δ := 1457/100000000) 581 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_292 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (292 : ℕ) / 2)) - ((-48577/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log (292 : ℕ) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (292 : ℕ) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7256107/10000000) (δ := 1467/100000000) 581 262
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_293 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (293 : ℕ) / 2)) - ((-182237/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log (293 : ℕ) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (293 : ℕ) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -746119/1250000) (δ := 1469/100000000) 581 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_294 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (294 : ℕ) / 2)) - ((172117/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log (294 : ℕ) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (294 : ℕ) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1747273/5000000) (δ := 727/50000000) 581 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_295 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (295 : ℕ) / 2)) - ((916563/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log (295 : ℕ) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (295 : ℕ) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -257123/2500000) (δ := 14713/1000000000) 581 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_296 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (296 : ℕ) / 2)) - ((840991/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log (296 : ℕ) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (296 : ℕ) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1429211/10000000) (δ := 14563/1000000000) 581 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_297 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (297 : ℕ) / 2)) - ((9671/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log (297 : ℕ) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (297 : ℕ) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1939317/5000000) (δ := 14713/1000000000) 581 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_298 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (298 : ℕ) / 2)) - ((-408767/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log (298 : ℕ) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (298 : ℕ) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6319779/10000000) (δ := 1469/100000000) 581 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_299 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (299 : ℕ) / 2)) - ((-187213/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log (299 : ℕ) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (299 : ℕ) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -278207/400000) (δ := 7353/500000000) 581 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_300 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (300 : ℕ) / 2)) - ((-238987/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log (300 : ℕ) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (300 : ℕ) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2265149/5000000) (δ := 14697/1000000000) 581 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_301 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (301 : ℕ) / 2)) - ((663437/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log (301 : ℕ) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (301 : ℕ) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -528371/2500000) (δ := 229/15625000) 581 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_302 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (302 : ℕ) / 2)) - ((99303/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log (302 : ℕ) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (302 : ℕ) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 147671/5000000) (δ := 229/15625000) 581 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_303 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (303 : ℕ) / 2)) - ((18907/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log (303 : ℕ) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (303 : ℕ) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 134809/500000) (δ := 14697/1000000000) 581 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_304 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (304 : ℕ) / 2)) - ((-448283/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log (304 : ℕ) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (304 : ℕ) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5089101/10000000) (δ := 14647/1000000000) 581 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_305 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (305 : ℕ) / 2)) - ((-494239/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log (305 : ℕ) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (305 : ℕ) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3737053/5000000) (δ := 14647/1000000000) 581 264
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_306 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (306 : ℕ) / 2)) - ((-174361/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log (306 : ℕ) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (306 : ℕ) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5856551/10000000) (δ := 14599/1000000000) 581 265
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_307 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (307 : ℕ) / 2)) - ((35011/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log (307 : ℕ) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (307 : ℕ) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -217943/625000) (δ := 14699/1000000000) 581 265
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_308 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (308 : ℕ) / 2)) - ((900391/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log (308 : ℕ) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (308 : ℕ) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1125323/10000000) (δ := 14699/1000000000) 581 265
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_309 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (309 : ℕ) / 2)) - ((881613/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log (309 : ℕ) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (309 : ℕ) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1228817/10000000) (δ := 3651/250000000) 581 265
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_310 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (310 : ℕ) / 2)) - ((140201/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log (310 : ℕ) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (310 : ℕ) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3575331/10000000) (δ := 919/62500000) 581 265
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_311 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (311 : ℕ) / 2)) - ((-178457/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log (311 : ℕ) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (311 : ℕ) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1478591/2500000) (δ := 7277/500000000) 581 265
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_312 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (312 : ℕ) / 2)) - ((-197549/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log (312 : ℕ) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (312 : ℕ) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -466387/625000) (δ := 3673/250000000) 581 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_313 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (313 : ℕ) / 2)) - ((-465749/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log (313 : ℕ) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (313 : ℕ) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -321137/625000) (δ := 3673/250000000) 581 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_314 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (314 : ℕ) / 2)) - ((42789/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log (314 : ℕ) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (314 : ℕ) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2821599/10000000) (δ := 14661/1000000000) 581 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_315 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (315 : ℕ) / 2)) - ((489537/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log (315 : ℕ) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (315 : ℕ) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -256171/5000000) (δ := 14611/1000000000) 581 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_316 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (316 : ℕ) / 2)) - ((188637/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log (316 : ℕ) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (316 : ℕ) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 89479/500000) (δ := 14611/1000000000) 581 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_317 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (317 : ℕ) / 2)) - ((-62829/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log (317 : ℕ) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (317 : ℕ) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4084167/10000000) (δ := 14661/1000000000) 581 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_318 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (318 : ℕ) / 2)) - ((-414643/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log (318 : ℕ) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (318 : ℕ) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1592891/2500000) (δ := 14661/1000000000) 581 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_319 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (319 : ℕ) / 2)) - ((-14836/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log (319 : ℕ) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (319 : ℕ) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -176403/250000) (δ := 2917/200000000) 581 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_320 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (320 : ℕ) / 2)) - ((-335791/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log (320 : ℕ) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (320 : ℕ) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4783103/10000000) (δ := 2937/200000000) 581 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_321 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (321 : ℕ) / 2)) - ((534549/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log (321 : ℕ) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (321 : ℕ) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2517057/10000000) (δ := 3667/250000000) 581 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_322 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (322 : ℕ) / 2)) - ((497337/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log (322 : ℕ) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (322 : ℕ) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -258129/10000000) (δ := 3667/250000000) 581 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_323 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (323 : ℕ) / 2)) - ((174619/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log (323 : ℕ) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (323 : ℕ) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1993827/10000000) (δ := 3667/250000000) 581 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_324 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (324 : ℕ) / 2)) - ((-24881/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log (324 : ℕ) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (324 : ℕ) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4238811/10000000) (δ := 3667/250000000) 581 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_325 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (325 : ℕ) / 2)) - ((-852073/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log (325 : ℕ) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (325 : ℕ) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6476823/10000000) (δ := 3667/250000000) 581 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_326 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (326 : ℕ) / 2)) - ((-117777/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log (326 : ℕ) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (326 : ℕ) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1399991/2000000) (δ := 3669/250000000) 581 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_327 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (327 : ℕ) / 2)) - ((-332961/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log (327 : ℕ) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (327 : ℕ) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4775597/10000000) (δ := 14577/1000000000) 581 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_328 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (328 : ℕ) / 2)) - ((520639/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log (328 : ℕ) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (328 : ℕ) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -319749/1250000) (δ := 7363/500000000) 581 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_329 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (329 : ℕ) / 2)) - ((990371/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log (329 : ℕ) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (329 : ℕ) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69443/2000000) (δ := 14577/1000000000) 581 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_330 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (330 : ℕ) / 2)) - ((73661/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log (330 : ℕ) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (330 : ℕ) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1856881/10000000) (δ := 14627/1000000000) 581 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_331 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (331 : ℕ) / 2)) - ((-509/10000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log (331 : ℕ) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (331 : ℕ) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 506787/1250000) (δ := 911/62500000) 581 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_332 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (332 : ℕ) / 2)) - ((-79997/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log (332 : ℕ) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (332 : ℕ) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3122551/5000000) (δ := 3669/250000000) 581 268
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_333 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (333 : ℕ) / 2)) - ((-486819/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log (333 : ℕ) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (333 : ℕ) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1455733/2000000) (δ := 731/50000000) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_334 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (334 : ℕ) / 2)) - ((-226267/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log (334 : ℕ) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (334 : ℕ) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1275251/2500000) (δ := 14583/1000000000) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_335 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (335 : ℕ) / 2)) - ((388381/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log (335 : ℕ) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (335 : ℕ) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2929807/10000000) (δ := 14583/1000000000) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_336 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (336 : ℕ) / 2)) - ((953529/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log (336 : ℕ) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (336 : ℕ) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -382573/5000000) (δ := 14683/1000000000) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_337 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (337 : ℕ) / 2)) - ((848713/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log (337 : ℕ) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (337 : ℕ) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1393123/10000000) (δ := 1467/100000000) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_338 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (338 : ℕ) / 2)) - ((152231/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log (338 : ℕ) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (338 : ℕ) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3544929/10000000) (δ := 23/1562500) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_339 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (339 : ℕ) / 2)) - ((-324169/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log (339 : ℕ) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (339 : ℕ) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 569049/1000000) (δ := 14583/1000000000) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_340 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (340 : ℕ) / 2)) - ((-999953/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log (340 : ℕ) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (340 : ℕ) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7829659/10000000) (δ := 731/50000000) 581 269
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_341 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (341 : ℕ) / 2)) - ((-664919/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log (341 : ℕ) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (341 : ℕ) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5745453/10000000) (δ := 727/50000000) 581 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_342 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (342 : ℕ) / 2)) - ((61487/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log (342 : ℕ) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (342 : ℕ) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -144751/400000) (δ := 1459/100000000) 581 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_343 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (343 : ℕ) / 2)) - ((82571/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log (343 : ℕ) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (343 : ℕ) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1498343/10000000) (δ := 727/50000000) 581 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_344 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (344 : ℕ) / 2)) - ((193961/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log (344 : ℕ) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (344 : ℕ) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 153979/2500000) (δ := 727/50000000) 581 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_345 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (345 : ℕ) / 2)) - ((231407/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log (345 : ℕ) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (345 : ℕ) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1362037/5000000) (δ := 14713/1000000000) 581 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_346 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (346 : ℕ) / 2)) - ((-175963/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log (346 : ℕ) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (346 : ℕ) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 241303/500000) (δ := 1459/100000000) 581 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_347 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (347 : ℕ) / 2)) - ((-232829/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log (347 : ℕ) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (347 : ℕ) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6922017/10000000) (δ := 14663/1000000000) 581 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_348 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (348 : ℕ) / 2)) - ((-894633/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log (348 : ℕ) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (348 : ℕ) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -418501/625000) (δ := 14647/1000000000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_349 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (349 : ℕ) / 2)) - ((-67651/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log (349 : ℕ) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (349 : ℕ) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2306021/5000000) (δ := 3639/250000000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_350 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (350 : ℕ) / 2)) - ((66097/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log (350 : ℕ) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (350 : ℕ) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -506819/2000000) (δ := 14697/1000000000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_351 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (351 : ℕ) / 2)) - ((982971/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log (351 : ℕ) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (351 : ℕ) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28877/625000) (δ := 7353/500000000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_352 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (352 : ℕ) / 2)) - ((801121/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log (352 : ℕ) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (352 : ℕ) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1604077/10000000) (δ := 3639/250000000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_353 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (353 : ℕ) / 2)) - ((104853/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log (353 : ℕ) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (353 : ℕ) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 458047/1250000) (δ := 14647/1000000000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_354 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (354 : ℕ) / 2)) - ((-656937/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log (354 : ℕ) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (354 : ℕ) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 357429/625000) (δ := 229/15625000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_355 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (355 : ℕ) / 2)) - ((-999401/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log (355 : ℕ) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (355 : ℕ) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 776747/1000000) (δ := 229/15625000) 581 271
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_356 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (356 : ℕ) / 2)) - ((-354551/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log (356 : ℕ) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (356 : ℕ) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -368597/625000) (δ := 14649/1000000000) 581 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_357 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (357 : ℕ) / 2)) - ((213/8000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log (357 : ℕ) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (357 : ℕ) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -193021/500000) (δ := 919/62500000) 581 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_358 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (358 : ℕ) / 2)) - ((744119/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log (358 : ℕ) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (358 : ℕ) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -914477/5000000) (δ := 14549/1000000000) 581 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_359 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (359 : ℕ) / 2)) - ((498451/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log (359 : ℕ) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (359 : ℕ) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12303/625000) (δ := 3651/250000000) 581 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_360 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (360 : ℕ) / 2)) - ((315939/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log (360 : ℕ) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (360 : ℕ) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2217057/10000000) (δ := 14699/1000000000) 581 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_361 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (361 : ℕ) / 2)) - ((-121543/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log (361 : ℕ) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (361 : ℕ) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2115801/5000000) (δ := 14649/1000000000) 581 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_362 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (362 : ℕ) / 2)) - ((-399447/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log (362 : ℕ) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (362 : ℕ) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1560157/2500000) (δ := 7327/500000000) 581 272
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_363 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (363 : ℕ) / 2)) - ((-246963/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log (363 : ℕ) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (363 : ℕ) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3731951/5000000) (δ := 7331/500000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_364 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (364 : ℕ) / 2)) - ((-72181/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log (364 : ℕ) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (364 : ℕ) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5465989/10000000) (δ := 14691/1000000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_365 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (365 : ℕ) / 2)) - ((36079/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log (365 : ℕ) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (365 : ℕ) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1736761/5000000) (δ := 14641/1000000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_366 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (366 : ℕ) / 2)) - ((207093/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log (366 : ℕ) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (366 : ℕ) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -743251/5000000) (δ := 14641/1000000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_367 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (367 : ℕ) / 2)) - ((122557/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log (367 : ℕ) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (367 : ℕ) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 495071/10000000) (δ := 14691/1000000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_368 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (368 : ℕ) / 2)) - ((549937/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log (368 : ℕ) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (368 : ℕ) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 247127/1000000) (δ := 14641/1000000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_369 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (369 : ℕ) / 2)) - ((-204587/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log (369 : ℕ) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (369 : ℕ) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 888419/2000000) (δ := 7281/500000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_370 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (370 : ℕ) / 2)) - ((-837259/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log (370 : ℕ) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (370 : ℕ) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3203809/5000000) (δ := 7281/500000000) 581 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_371 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (371 : ℕ) / 2)) - ((-244739/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log (371 : ℕ) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (371 : ℕ) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7340197/10000000) (δ := 3671/250000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_372 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (372 : ℕ) / 2)) - ((-550793/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log (372 : ℕ) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (372 : ℕ) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5385277/10000000) (δ := 1823/125000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_373 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (373 : ℕ) / 2)) - ((195299/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log (373 : ℕ) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (373 : ℕ) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1717793/5000000) (δ := 14569/1000000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_374 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (374 : ℕ) / 2)) - ((827319/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log (374 : ℕ) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (374 : ℕ) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1491197/10000000) (δ := 7267/500000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_375 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (375 : ℕ) / 2)) - ((983979/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log (375 : ℕ) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (375 : ℕ) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 112027/2500000) (δ := 3671/250000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_376 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (376 : ℕ) / 2)) - ((579343/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log (376 : ℕ) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (376 : ℕ) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 476437/2000000) (δ := 14619/1000000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_377 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (377 : ℕ) / 2)) - ((-76521/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log (377 : ℕ) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (377 : ℕ) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 862221/2000000) (δ := 14619/1000000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_378 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (378 : ℕ) / 2)) - ((-199381/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log (378 : ℕ) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (378 : ℕ) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6234941/10000000) (δ := 7267/500000000) 581 274
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_379 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (379 : ℕ) / 2)) - ((-992819/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log (379 : ℕ) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (379 : ℕ) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7554197/10000000) (δ := 911/62500000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_380 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (380 : ℕ) / 2)) - ((-316497/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log (380 : ℕ) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (380 : ℕ) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -352533/625000) (δ := 3669/250000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_381 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (381 : ℕ) / 2)) - ((77969/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log (381 : ℕ) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (381 : ℕ) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3731871/10000000) (δ := 14627/1000000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_382 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (382 : ℕ) / 2)) - ((744333/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log (382 : ℕ) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (382 : ℕ) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -228519/1250000) (δ := 14677/1000000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_383 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (383 : ℕ) / 2)) - ((999603/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log (383 : ℕ) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (383 : ℕ) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17621/2500000) (δ := 7313/500000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_384 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (384 : ℕ) / 2)) - ((176723/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log (384 : ℕ) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (384 : ℕ) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1964253/10000000) (δ := 14627/1000000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_385 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (385 : ℕ) / 2)) - ((14779/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log (385 : ℕ) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (385 : ℕ) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 963271/2500000) (δ := 14627/1000000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_386 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (386 : ℕ) / 2)) - ((-331191/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log (386 : ℕ) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (386 : ℕ) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5736977/10000000) (δ := 7313/500000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_387 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (387 : ℕ) / 2)) - ((-995473/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log (387 : ℕ) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (387 : ℕ) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7616003/10000000) (δ := 14677/1000000000) 581 275
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_388 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (388 : ℕ) / 2)) - ((-793351/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log (388 : ℕ) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (388 : ℕ) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6217727/10000000) (δ := 23/1562500) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_389 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (389 : ℕ) / 2)) - ((-671/4000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log (389 : ℕ) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (389 : ℕ) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4348359/10000000) (δ := 14533/1000000000) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_390 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (390 : ℕ) / 2)) - ((545749/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log (390 : ℕ) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (390 : ℕ) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -496757/2000000) (δ := 731/50000000) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_391 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (391 : ℕ) / 2)) - ((969011/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log (391 : ℕ) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (391 : ℕ) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -156001/2500000) (δ := 731/50000000) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_392 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (392 : ℕ) / 2)) - ((88119/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log (392 : ℕ) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (392 : ℕ) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1231057/10000000) (δ := 14683/1000000000) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_393 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (393 : ℕ) / 2)) - ((13273/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log (393 : ℕ) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (393 : ℕ) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 770349/2500000) (δ := 1467/100000000) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_394 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (394 : ℕ) / 2)) - ((-389427/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log (394 : ℕ) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (394 : ℕ) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 985403/2000000) (δ := 23/1562500) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_395 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (395 : ℕ) / 2)) - ((-907111/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log (395 : ℕ) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (395 : ℕ) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3383957/5000000) (δ := 14533/1000000000) 581 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_396 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (396 : ℕ) / 2)) - ((-477653/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log (396 : ℕ) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (396 : ℕ) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3551863/5000000) (δ := 1459/100000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_397 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (397 : ℕ) / 2)) - ((-102493/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log (397 : ℕ) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (397 : ℕ) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1318031/2500000) (δ := 14663/1000000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_398 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (398 : ℕ) / 2)) - ((38319/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log (398 : ℕ) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (398 : ℕ) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -107657/312500) (δ := 14563/1000000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_399 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (399 : ℕ) / 2)) - ((796671/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log (399 : ℕ) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (399 : ℕ) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -405643/2500000) (δ := 1459/100000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_400 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (400 : ℕ) / 2)) - ((19939/20000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log (400 : ℕ) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (400 : ℕ) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24413/1250000) (δ := 14613/1000000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_401 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (401 : ℕ) / 2)) - ((173553/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log (401 : ℕ) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (401 : ℕ) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1004339/5000000) (δ := 1459/100000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_402 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (402 : ℕ) / 2)) - ((2737/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log (402 : ℕ) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (402 : ℕ) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 954369/2500000) (δ := 14563/1000000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_403 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (403 : ℕ) / 2)) - ((-627191/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log (403 : ℕ) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (403 : ℕ) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1405461/2500000) (δ := 14613/1000000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_404 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (404 : ℕ) / 2)) - ((-985089/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log (404 : ℕ) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (404 : ℕ) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 742171/1000000) (δ := 1469/100000000) 581 277
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_405 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (405 : ℕ) / 2)) - ((-85499/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log (405 : ℕ) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (405 : ℕ) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3245409/5000000) (δ := 14697/1000000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_406 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (406 : ℕ) / 2)) - ((-304229/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log (406 : ℕ) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (406 : ℕ) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4699813/10000000) (δ := 14647/1000000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_407 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (407 : ℕ) / 2)) - ((394479/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log (407 : ℕ) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (407 : ℕ) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1456619/5000000) (δ := 14647/1000000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_408 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (408 : ℕ) / 2)) - ((899397/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log (408 : ℕ) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (408 : ℕ) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1131021/10000000) (δ := 7303/500000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_409 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (409 : ℕ) / 2)) - ((483357/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log (409 : ℕ) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (409 : ℕ) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 646839/10000000) (δ := 7303/500000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_410 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (410 : ℕ) / 2)) - ((113367/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log (410 : ℕ) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (410 : ℕ) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1210171/5000000) (δ := 14647/1000000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_411 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (411 : ℕ) / 2)) - ((-52417/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log (411 : ℕ) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (411 : ℕ) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4189559/10000000) (δ := 229/15625000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_412 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (412 : ℕ) / 2)) - ((-724957/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log (412 : ℕ) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (412 : ℕ) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5954419/10000000) (δ := 7353/500000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_413 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (413 : ℕ) / 2)) - ((-199691/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log (413 : ℕ) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (413 : ℕ) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1542999/2000000) (δ := 14647/1000000000) 581 278
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_414 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (414 : ℕ) / 2)) - ((-398963/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log (414 : ℕ) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (414 : ℕ) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3118303/5000000) (δ := 7349/500000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_415 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (415 : ℕ) / 2)) - ((-110571/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log (415 : ℕ) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (415 : ℕ) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -896891/2000000) (δ := 7299/500000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_416 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (416 : ℕ) / 2)) - ((45837/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log (416 : ℕ) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (416 : ℕ) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2736589/10000000) (δ := 3637/250000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_417 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (417 : ℕ) / 2)) - ((922169/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log (417 : ℕ) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (417 : ℕ) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -992863/10000000) (δ := 1831/125000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_418 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (418 : ℕ) / 2)) - ((238933/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log (418 : ℕ) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (418 : ℕ) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 746651/10000000) (δ := 1831/125000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_419 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (419 : ℕ) / 2)) - ((273169/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log (419 : ℕ) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (419 : ℕ) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1241013/5000000) (δ := 2931/200000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_420 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (420 : ℕ) / 2)) - ((-57129/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log (420 : ℕ) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (420 : ℕ) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 210663/500000) (δ := 7349/500000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_421 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (421 : ℕ) / 2)) - ((-72107/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log (421 : ℕ) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (421 : ℕ) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1485089/2500000) (δ := 2941/200000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_422 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (422 : ℕ) / 2)) - ((-199419/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log (422 : ℕ) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (422 : ℕ) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 957923/1250000) (δ := 2931/200000000) 581 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_423 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (423 : ℕ) / 2)) - ((-818893/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log (423 : ℕ) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (423 : ℕ) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6325691/10000000) (δ := 7281/500000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_424 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (424 : ℕ) / 2)) - ((-2161/8000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log (424 : ℕ) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (424 : ℕ) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4610797/10000000) (δ := 14541/1000000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_425 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (425 : ℕ) / 2)) - ((399351/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log (425 : ℕ) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (425 : ℕ) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -289997/1000000) (δ := 14591/1000000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_426 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (426 : ℕ) / 2)) - ((888259/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log (426 : ℕ) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (426 : ℕ) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1193137/10000000) (δ := 7281/500000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_427 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (427 : ℕ) / 2)) - ((122411/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log (427 : ℕ) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (427 : ℕ) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 509701/10000000) (δ := 14641/1000000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_428 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (428 : ℕ) / 2)) - ((126907/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log (428 : ℕ) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (428 : ℕ) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2208473/10000000) (δ := 7331/500000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_429 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (429 : ℕ) / 2)) - ((4719/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log (429 : ℕ) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (429 : ℕ) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 780679/2000000) (δ := 7281/500000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_430 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (430 : ℕ) / 2)) - ((-618579/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log (430 : ℕ) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (430 : ℕ) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5594323/10000000) (δ := 3653/250000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_431 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (431 : ℕ) / 2)) - ((-973873/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log (431 : ℕ) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (431 : ℕ) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 910157/1250000) (δ := 14641/1000000000) 581 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_432 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (432 : ℕ) / 2)) - ((-902979/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log (432 : ℕ) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (432 : ℕ) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6743623/10000000) (δ := 3671/250000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_433 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (433 : ℕ) / 2)) - ((-17577/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log (433 : ℕ) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (433 : ℕ) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5064387/10000000) (δ := 14669/1000000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_434 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (434 : ℕ) / 2)) - ((21351/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log (434 : ℕ) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (434 : ℕ) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1694537/5000000) (δ := 1823/125000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_435 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (435 : ℕ) / 2)) - ((1237/1600 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log (435 : ℕ) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (435 : ℕ) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1717609/10000000) (δ := 14719/1000000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_436 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (436 : ℕ) / 2)) - ((4999/5000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log (436 : ℕ) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (436 : ℕ) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24997/5000000) (δ := 14619/1000000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_437 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (437 : ℕ) / 2)) - ((399397/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log (437 : ℕ) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (437 : ℕ) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 403443/2500000) (δ := 14569/1000000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_438 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (438 : ℕ) / 2)) - ((258301/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log (438 : ℕ) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (438 : ℕ) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1636917/5000000) (δ := 1823/125000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_439 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (439 : ℕ) / 2)) - ((-24409/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log (439 : ℕ) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (439 : ℕ) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4930047/10000000) (δ := 7317/500000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_440 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (440 : ℕ) / 2)) - ((-218357/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log (440 : ℕ) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (440 : ℕ) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1645621/2500000) (δ := 14569/1000000000) 581 281
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_441 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (441 : ℕ) / 2)) - ((-988641/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log (441 : ℕ) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (441 : ℕ) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7476819/10000000) (δ := 7313/500000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_442 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (442 : ℕ) / 2)) - ((-690333/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log (442 : ℕ) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (442 : ℕ) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5831863/10000000) (δ := 14527/1000000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_443 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (443 : ℕ) / 2)) - ((-105253/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log (443 : ℕ) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (443 : ℕ) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4190611/10000000) (δ := 14677/1000000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_444 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (444 : ℕ) / 2)) - ((261161/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log (444 : ℕ) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (444 : ℕ) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1276531/5000000) (δ := 911/62500000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_445 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (445 : ℕ) / 2)) - ((933161/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log (445 : ℕ) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (445 : ℕ) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -919217/10000000) (δ := 7363/500000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_446 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (446 : ℕ) / 2)) - ((959831/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log (446 : ℕ) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (446 : ℕ) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 177749/2500000) (δ := 911/62500000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_447 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (447 : ℕ) / 2)) - ((593817/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log (447 : ℕ) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (447 : ℕ) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 467501/2000000) (δ := 14677/1000000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_448 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (448 : ℕ) / 2)) - ((-6693/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log (448 : ℕ) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (448 : ℕ) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 495057/1250000) (δ := 14627/1000000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_449 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (449 : ℕ) / 2)) - ((-306987/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log (449 : ℕ) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (449 : ℕ) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5579703/10000000) (δ := 14627/1000000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_450 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (450 : ℕ) / 2)) - ((-965501/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log (450 : ℕ) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (450 : ℕ) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 56214/78125) (δ := 3669/250000000) 581 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_451 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (451 : ℕ) / 2)) - ((-928139/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log (451 : ℕ) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (451 : ℕ) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3450221/5000000) (δ := 1457/100000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_452 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (452 : ℕ) / 2)) - ((-519257/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log (452 : ℕ) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (452 : ℕ) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5291943/10000000) (δ := 14683/1000000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_453 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (453 : ℕ) / 2)) - ((23969/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log (453 : ℕ) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (453 : ℕ) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3686931/10000000) (δ := 1457/100000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_454 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (454 : ℕ) / 2)) - ((167939/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log (454 : ℕ) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (454 : ℕ) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41711/200000) (δ := 1467/100000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_455 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (455 : ℕ) / 2)) - ((981041/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log (455 : ℕ) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (455 : ℕ) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -243791/5000000) (δ := 731/50000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_456 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (456 : ℕ) / 2)) - ((180717/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log (456 : ℕ) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (456 : ℕ) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1106827/10000000) (δ := 23/1562500) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_457 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (457 : ℕ) / 2)) - ((472147/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log (457 : ℕ) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (457 : ℕ) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1348839/5000000) (δ := 1457/100000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_458 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (458 : ℕ) / 2)) - ((-3569/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log (458 : ℕ) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (458 : ℕ) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 857023/2000000) (δ := 1467/100000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_459 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (459 : ℕ) / 2)) - ((-701043/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log (459 : ℕ) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (459 : ℕ) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5869139/10000000) (δ := 731/50000000) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_460 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (460 : ℕ) / 2)) - ((-986947/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log (460 : ℕ) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (460 : ℕ) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1862401/2500000) (δ := 23/1562500) 581 283
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_461 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (461 : ℕ) / 2)) - ((-111497/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log (461 : ℕ) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (461 : ℕ) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3340617/5000000) (δ := 14641/1000000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_462 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (462 : ℕ) / 2)) - ((-113721/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log (462 : ℕ) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (462 : ℕ) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1276899/2500000) (δ := 3653/250000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_463 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (463 : ℕ) / 2)) - ((155247/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log (463 : ℕ) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (463 : ℕ) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1768649/5000000) (δ := 14541/1000000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_464 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (464 : ℕ) / 2)) - ((705147/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log (464 : ℕ) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (464 : ℕ) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -985207/5000000) (δ := 7331/500000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_465 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (465 : ℕ) / 2)) - ((493393/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log (465 : ℕ) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (465 : ℕ) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40687/1000000) (δ := 14541/1000000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_466 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (466 : ℕ) / 2)) - ((895473/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log (466 : ℕ) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (466 : ℕ) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 57663/500000) (δ := 3653/250000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_467 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (467 : ℕ) / 2)) - ((467779/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log (467 : ℕ) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (467 : ℕ) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54201/200000) (δ := 14641/1000000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_468 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (468 : ℕ) / 2)) - ((-134197/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log (468 : ℕ) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (468 : ℕ) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2131749/5000000) (δ := 1839/125000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_469 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (469 : ℕ) / 2)) - ((-171263/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log (469 : ℕ) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (469 : ℕ) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5813679/10000000) (δ := 7281/500000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_470 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (470 : ℕ) / 2)) - ((-980583/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log (470 : ℕ) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (470 : ℕ) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7360519/10000000) (δ := 14541/1000000000) 581 284
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_471 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (471 : ℕ) / 2)) - ((-913071/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log (471 : ℕ) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (471 : ℕ) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6803873/10000000) (δ := 2941/200000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_472 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (472 : ℕ) / 2)) - ((-127381/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log (472 : ℕ) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (472 : ℕ) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5263569/10000000) (δ := 2911/200000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_473 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (473 : ℕ) / 2)) - ((80097/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log (473 : ℕ) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (473 : ℕ) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3726533/10000000) (δ := 7349/500000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_474 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (474 : ℕ) / 2)) - ((639401/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log (474 : ℕ) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (474 : ℕ) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2192693/10000000) (δ := 7349/500000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_475 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (475 : ℕ) / 2)) - ((241283/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log (475 : ℕ) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (475 : ℕ) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -331061/5000000) (δ := 2941/200000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_476 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (476 : ℕ) / 2)) - ((117589/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log (476 : ℕ) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (476 : ℕ) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 432591/5000000) (δ := 2921/200000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_477 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (477 : ℕ) / 2)) - ((9016/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log (477 : ℕ) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (477 : ℕ) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 238929/1000000) (δ := 2941/200000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_478 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (478 : ℕ) / 2)) - ((3343/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log (478 : ℕ) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (478 : ℕ) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 977569/2500000) (δ := 7299/500000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_479 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (479 : ℕ) / 2)) - ((-564973/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log (479 : ℕ) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (479 : ℕ) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5427993/10000000) (δ := 2911/200000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_480 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (480 : ℕ) / 2)) - ((-233573/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log (480 : ℕ) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (480 : ℕ) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 347133/500000) (δ := 2911/200000000) 581 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_481 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (481 : ℕ) / 2)) - ((-971331/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log (481 : ℕ) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (481 : ℕ) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -453369/625000) (δ := 2931/200000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_482 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (482 : ℕ) / 2)) - ((-664949/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log (482 : ℕ) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (482 : ℕ) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1436389/2500000) (δ := 1831/125000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_483 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (483 : ℕ) / 2)) - ((-125037/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log (483 : ℕ) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (483 : ℕ) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4240403/10000000) (δ := 7349/500000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_484 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (484 : ℕ) / 2)) - ((228881/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log (484 : ℕ) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (484 : ℕ) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27383/100000) (δ := 1831/125000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_485 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (485 : ℕ) / 2)) - ((879609/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log (485 : ℕ) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (485 : ℕ) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38731/312500) (δ := 2931/200000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_486 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (486 : ℕ) / 2)) - ((49737/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log (486 : ℕ) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (486 : ℕ) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 256537/10000000) (δ := 7349/500000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_487 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (487 : ℕ) / 2)) - ((765011/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log (487 : ℕ) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (487 : ℕ) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54667/312500) (δ := 1831/125000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_488 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (488 : ℕ) / 2)) - ((271697/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log (488 : ℕ) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (488 : ℕ) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3239101/10000000) (δ := 2911/200000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_489 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (489 : ℕ) / 2)) - ((-31409/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log (489 : ℕ) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (489 : ℕ) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 945147/2000000) (δ := 2931/200000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_490 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (490 : ℕ) / 2)) - ((-791317/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log (490 : ℕ) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (490 : ℕ) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6209391/10000000) (δ := 2921/200000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_491 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (491 : ℕ) / 2)) - ((-997851/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log (491 : ℕ) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (491 : ℕ) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7690069/10000000) (δ := 1831/125000000) 581 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_492 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (492 : ℕ) / 2)) - ((-21627/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log (492 : ℕ) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (492 : ℕ) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3270133/5000000) (δ := 14641/1000000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_493 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (493 : ℕ) / 2)) - ((-109973/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log (493 : ℕ) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (493 : ℕ) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -633211/1250000) (δ := 14641/1000000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_494 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (494 : ℕ) / 2)) - ((132797/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log (494 : ℕ) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (494 : ℕ) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -718803/2000000) (δ := 14641/1000000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_495 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (495 : ℕ) / 2)) - ((131973/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log (495 : ℕ) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (495 : ℕ) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -132837/625000) (δ := 14541/1000000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_496 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (496 : ℕ) / 2)) - ((241347/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log (496 : ℕ) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (496 : ℕ) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -329837/5000000) (δ := 3653/250000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_497 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (497 : ℕ) / 2)) - ((948849/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log (497 : ℕ) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (497 : ℕ) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 401533/5000000) (δ := 7281/500000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_498 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (498 : ℕ) / 2)) - ((308791/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log (498 : ℕ) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (498 : ℕ) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 565707/2500000) (δ := 14691/1000000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_499 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (499 : ℕ) / 2)) - ((82827/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log (499 : ℕ) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (499 : ℕ) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1859843/5000000) (δ := 7281/500000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos581o2_br_500 :
    |Real.cos (((581 : ℕ) : ℝ) * (Real.log (500 : ℕ) / 2)) - ((-59781/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log (500 : ℕ) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (500 : ℕ) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2586819/5000000) (δ := 14691/1000000000) 581 287
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos581o2_br_500
end AxiomAudit
