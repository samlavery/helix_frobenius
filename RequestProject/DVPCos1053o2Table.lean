import RequestProject.DVPCosSinEval
import RequestProject.DVPLog200Table
import RequestProject.DVPLog250Table
import RequestProject.DVPLog500Table
import RequestProject.DVPLog1000Table

/-!
# The cosine table at `t = 1053/2` (rung-526.5; halved brackets, N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos1053o2_br_2 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (2 : ℕ) / 2)) - ((8691939/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (2 : ℕ) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6465333/50000000) (δ := 263437/10000000000) 1053 58
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_3 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (3 : ℕ) / 2)) - ((1867317/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log (3 : ℕ) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (3 : ℕ) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4578767/50000000) (δ := 2057/78125000) 1053 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_4 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (4 : ℕ) / 2)) - ((5109733/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log (4 : ℕ) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (4 : ℕ) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25861991/100000000) (δ := 263273/10000000000) 1053 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_5 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (5 : ℕ) / 2)) - ((40733/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log (5 : ℕ) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (5 : ℕ) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4304679/20000000) (δ := 263309/10000000000) 1053 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_6 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (6 : ℕ) / 2)) - ((1586019/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log (6 : ℕ) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (6 : ℕ) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22088859/100000000) (δ := 263371/10000000000) 1053 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_7 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (7 : ℕ) / 2)) - ((9350171/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log (7 : ℕ) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (7 : ℕ) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9062223/100000000) (δ := 65851/2500000000) 1053 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_8 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (8 : ℕ) / 2)) - ((61/3200 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log (8 : ℕ) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (8 : ℕ) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9698329/25000000) (δ := 131697/5000000000) 1053 174
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_9 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (9 : ℕ) / 2)) - ((3717093/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log (9 : ℕ) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (9 : ℕ) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9157863/50000000) (δ := 263391/10000000000) 1053 184
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_10 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (10 : ℕ) / 2)) - ((588439/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log (10 : ℕ) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (10 : ℕ) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8593387/100000000) (δ := 52689/2000000000) 1053 193
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_11 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (11 : ℕ) / 2)) - ((4548163/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log (11 : ℕ) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (11 : ℕ) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -535497/5000000) (δ := 32929/1250000000) 1053 201
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_12 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (12 : ℕ) / 2)) - ((338343/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log (12 : ℕ) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (12 : ℕ) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35020183/100000000) (δ := 32921/1250000000) 1053 208
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_13 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (13 : ℕ) / 2)) - ((1131467/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log (13 : ℕ) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (13 : ℕ) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10975207/100000000) (δ := 52673/2000000000) 1053 215
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_14 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (14 : ℕ) / 2)) - ((6373501/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log (14 : ℕ) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (14 : ℕ) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21993547/100000000) (δ := 52667/2000000000) 1053 221
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_15 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (15 : ℕ) / 2)) - ((2200387/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log (15 : ℕ) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (15 : ℕ) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12365203/100000000) (δ := 65851/2500000000) 1053 227
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_16 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (16 : ℕ) / 2)) - ((-4778357/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log (16 : ℕ) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (16 : ℕ) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 323279/625000) (δ := 52669/2000000000) 1053 232
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_17 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (17 : ℕ) / 2)) - ((-8420727/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log (17 : ℕ) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (17 : ℕ) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32148887/50000000) (δ := 131693/5000000000) 1053 237
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_18 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (18 : ℕ) / 2)) - ((3154343/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log (18 : ℕ) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (18 : ℕ) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31247051/100000000) (δ := 65819/2500000000) 1053 242
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_19 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (19 : ℕ) / 2)) - ((-128511/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log (19 : ℕ) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (19 : ℕ) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5311449/12500000) (δ := 52687/2000000000) 1053 247
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_20 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (20 : ℕ) / 2)) - ((2462459/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log (20 : ℕ) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (20 : ℕ) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2168969/50000000) (δ := 263281/10000000000) 1053 251
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_21 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (21 : ℕ) / 2)) - ((7459631/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log (21 : ℕ) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (21 : ℕ) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3644083/20000000) (δ := 263309/10000000000) 1053 255
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_22 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (22 : ℕ) / 2)) - ((199211/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log (22 : ℕ) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (22 : ℕ) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 277673/12500000) (δ := 131653/5000000000) 1053 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_23 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (23 : ℕ) / 2)) - ((-21613/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log (23 : ℕ) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (23 : ℕ) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41000329/100000000) (δ := 65821/2500000000) 1053 263
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_24 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (24 : ℕ) / 2)) - ((-26588/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log (24 : ℕ) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (24 : ℕ) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11987877/25000000) (δ := 263299/10000000000) 1053 266
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_25 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (25 : ℕ) / 2)) - ((-1505273/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log (25 : ℕ) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (25 : ℕ) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5380931/12500000) (δ := 263317/10000000000) 1053 270
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_26 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (26 : ℕ) / 2)) - ((2492351/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log (26 : ℕ) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (26 : ℕ) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 978059/50000000) (δ := 131651/5000000000) 1053 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_27 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (27 : ℕ) / 2)) - ((568157/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log (27 : ℕ) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (27 : ℕ) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27473919/100000000) (δ := 263417/10000000000) 1053 276
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_28 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (28 : ℕ) / 2)) - ((864639/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log (28 : ℕ) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (28 : ℕ) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4365609/12500000) (δ := 263333/10000000000) 1053 279
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_29 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (29 : ℕ) / 2)) - ((5208001/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log (29 : ℕ) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (29 : ℕ) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2557521/10000000) (δ := 52651/2000000000) 1053 282
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_30 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (30 : ℕ) / 2)) - ((1249681/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log (30 : ℕ) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (30 : ℕ) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 282403/50000000) (δ := 263363/10000000000) 1053 285
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_31 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (31 : ℕ) / 2)) - ((77149/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log (31 : ℕ) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (31 : ℕ) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19538517/50000000) (δ := 1029/39062500) 1053 288
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_32 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (32 : ℕ) / 2)) - ((-4248569/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log (32 : ℕ) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (32 : ℕ) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12931193/20000000) (δ := 131661/5000000000) 1053 290
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_33 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (33 : ℕ) / 2)) - ((9980743/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log (33 : ℕ) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (33 : ℕ) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -387937/25000000) (δ := 131669/5000000000) 1053 293
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_34 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (34 : ℕ) / 2)) - ((-9986259/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log (34 : ℕ) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (34 : ℕ) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 77229099/100000000) (δ := 263281/10000000000) 1053 295
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_35 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (35 : ℕ) / 2)) - ((1756627/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log (35 : ℕ) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (35 : ℕ) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1246183/10000000) (δ := 263397/10000000000) 1053 298
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_36 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (36 : ℕ) / 2)) - ((-1950797/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log (36 : ℕ) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (36 : ℕ) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5522297/12500000) (δ := 3293/125000000) 1053 300
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_37 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (37 : ℕ) / 2)) - ((-8847937/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log (37 : ℕ) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (37 : ℕ) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13284237/20000000) (δ := 32907/1250000000) 1053 303
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_38 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (38 : ℕ) / 2)) - ((946737/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log (38 : ℕ) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (38 : ℕ) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7390067/25000000) (δ := 32913/1250000000) 1053 305
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_39 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (39 : ℕ) / 2)) - ((9973599/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log (39 : ℕ) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (39 : ℕ) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -908507/50000000) (δ := 263443/10000000000) 1053 307
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_40 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (40 : ℕ) / 2)) - ((7707553/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log (40 : ℕ) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (40 : ℕ) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17269263/100000000) (δ := 131693/5000000000) 1053 309
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_41 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (41 : ℕ) / 2)) - ((53891/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log (41 : ℕ) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (41 : ℕ) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5625269/20000000) (δ := 26333/1000000000) 1053 311
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_42 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (42 : ℕ) / 2)) - ((1595249/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log (42 : ℕ) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (42 : ℕ) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31151739/100000000) (δ := 263429/10000000000) 1053 313
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_43 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (43 : ℕ) / 2)) - ((1203583/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log (43 : ℕ) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (43 : ℕ) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 667817/2500000) (δ := 131693/5000000000) 1053 315
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_44 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (44 : ℕ) / 2)) - ((1027339/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log (44 : ℕ) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (44 : ℕ) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15152709/100000000) (δ := 263361/10000000000) 1053 317
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_45 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (45 : ℕ) / 2)) - ((4958883/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log (45 : ℕ) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (45 : ℕ) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3208327/100000000) (δ := 263399/10000000000) 1053 319
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_46 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (46 : ℕ) / 2)) - ((4331489/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log (46 : ℕ) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (46 : ℕ) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28070321/100000000) (δ := 52671/2000000000) 1053 321
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_47 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (47 : ℕ) / 2)) - ((-3570439/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log (47 : ℕ) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (47 : ℕ) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3697057/6250000) (δ := 8231/312500000) 1053 323
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_48 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (48 : ℕ) / 2)) - ((-7607819/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log (48 : ℕ) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (48 : ℕ) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3805177/6250000) (δ := 3293/125000000) 1053 324
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_49 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (49 : ℕ) / 2)) - ((1871329/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log (49 : ℕ) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (49 : ℕ) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18123787/100000000) (δ := 2057/78125000) 1053 326
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_50 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (50 : ℕ) / 2)) - ((1790123/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log (50 : ℕ) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (50 : ℕ) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30116123/100000000) (δ := 263351/10000000000) 1053 328
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_51 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (51 : ℕ) / 2)) - ((-9793947/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log (51 : ℕ) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (51 : ℕ) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73455967/100000000) (δ := 131711/5000000000) 1053 329
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_52 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (52 : ℕ) / 2)) - ((4139347/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log (52 : ℕ) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (52 : ℕ) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7443721/50000000) (δ := 263437/10000000000) 1053 331
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_53 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (53 : ℕ) / 2)) - ((-3627333/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log (53 : ℕ) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (53 : ℕ) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4854989/10000000) (δ := 26341/1000000000) 1053 333
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_54 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (54 : ℕ) / 2)) - ((-226989/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log (54 : ℕ) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (54 : ℕ) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40405243/100000000) (δ := 131661/5000000000) 1053 334
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_55 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (55 : ℕ) / 2)) - ((34717/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log (55 : ℕ) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (55 : ℕ) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32233993/100000000) (δ := 10537/400000000) 1053 336
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_56 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (56 : ℕ) / 2)) - ((-673379/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log (56 : ℕ) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (56 : ℕ) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 299093/625000) (δ := 131653/5000000000) 1053 337
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_57 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (57 : ℕ) / 2)) - ((47047/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log (57 : ℕ) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (57 : ℕ) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -166667/500000) (δ := 13167/500000000) 1053 339
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_58 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (58 : ℕ) / 2)) - ((152651/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log (58 : ℕ) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (58 : ℕ) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7701307/20000000) (δ := 65853/2500000000) 1053 340
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_59 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (59 : ℕ) / 2)) - ((-4395623/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log (59 : ℕ) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (59 : ℕ) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -50647691/100000000) (δ := 263347/10000000000) 1053 342
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_60 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (60 : ℕ) / 2)) - ((8577883/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log (60 : ℕ) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (60 : ℕ) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1349613/10000000) (δ := 16461/625000000) 1053 343
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_61 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (61 : ℕ) / 2)) - ((-2458593/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log (61 : ℕ) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (61 : ℕ) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73983409/100000000) (δ := 263299/10000000000) 1053 344
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_62 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (62 : ℕ) / 2)) - ((5011397/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log (62 : ℕ) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (62 : ℕ) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1045881/4000000) (δ := 263343/10000000000) 1053 346
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_63 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (63 : ℕ) / 2)) - ((2289591/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log (63 : ℕ) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (63 : ℕ) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27378607/100000000) (δ := 32911/1250000000) 1053 347
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_64 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (64 : ℕ) / 2)) - ((-4996361/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log (64 : ℕ) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (64 : ℕ) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 77585973/100000000) (δ := 263317/10000000000) 1053 348
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_65 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (65 : ℕ) / 2)) - ((2675273/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log (65 : ℕ) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (65 : ℕ) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1624963/5000000) (δ := 263373/10000000000) 1053 350
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_66 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (66 : ℕ) / 2)) - ((4490903/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log (66 : ℕ) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (66 : ℕ) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1422447/12500000) (δ := 263401/10000000000) 1053 351
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_67 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (67 : ℕ) / 2)) - ((-4957131/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log (67 : ℕ) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (67 : ℕ) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26118151/50000000) (δ := 263429/10000000000) 1053 352
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_68 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (68 : ℕ) / 2)) - ((-8939003/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log (68 : ℕ) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (68 : ℕ) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66919209/100000000) (δ := 263317/10000000000) 1053 354
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_69 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (69 : ℕ) / 2)) - ((2927589/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log (69 : ℕ) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (69 : ℕ) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31842137/100000000) (δ := 131657/5000000000) 1053 355
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_70 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (70 : ℕ) / 2)) - ((9998237/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log (70 : ℕ) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (70 : ℕ) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 234747/50000000) (δ := 131671/5000000000) 1053 356
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_71 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (71 : ℕ) / 2)) - ((3588261/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log (71 : ℕ) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (71 : ℕ) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30094659/100000000) (δ := 26327/1000000000) 1053 357
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_72 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (72 : ℕ) / 2)) - ((-6545533/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log (72 : ℕ) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (72 : ℕ) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 571097/1000000) (δ := 263299/10000000000) 1053 358
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_73 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (73 : ℕ) / 2)) - ((-9925937/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log (73 : ℕ) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (73 : ℕ) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37747627/50000000) (δ := 52651/2000000000) 1053 360
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_74 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (74 : ℕ) / 2)) - ((-5386641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log (74 : ℕ) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (74 : ℕ) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53491177/100000000) (δ := 263383/10000000000) 1053 361
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_75 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (75 : ℕ) / 2)) - ((2135683/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log (75 : ℕ) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (75 : ℕ) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4236157/12500000) (δ := 263411/10000000000) 1053 362
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_76 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (76 : ℕ) / 2)) - ((1573639/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log (76 : ℕ) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (76 : ℕ) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16628943/100000000) (δ := 263363/10000000000) 1053 363
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_77 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (77 : ℕ) / 2)) - ((1995661/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log (77 : ℕ) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (77 : ℕ) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -82353/5000000) (δ := 32921/1250000000) 1053 364
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_78 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (78 : ℕ) / 2)) - ((4513973/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log (78 : ℕ) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (78 : ℕ) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1111431/10000000) (δ := 2057/78125000) 1053 365
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_79 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (79 : ℕ) / 2)) - ((1614987/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log (79 : ℕ) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (79 : ℕ) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4342353/20000000) (δ := 263279/10000000000) 1053 366
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_80 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (80 : ℕ) / 2)) - ((88717/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log (80 : ℕ) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (80 : ℕ) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30200587/100000000) (δ := 32919/1250000000) 1053 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_81 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (81 : ℕ) / 2)) - ((526581/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log (81 : ℕ) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (81 : ℕ) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36632111/100000000) (δ := 131661/5000000000) 1053 368
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_82 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (82 : ℕ) / 2)) - ((-142899/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log (82 : ℕ) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (82 : ℕ) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 41057669/100000000) (δ := 263409/10000000000) 1053 369
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_83 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (83 : ℕ) / 2)) - ((-1694211/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log (83 : ℕ) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (83 : ℕ) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10881491/25000000) (δ := 263337/10000000000) 1053 370
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_84 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (84 : ℕ) / 2)) - ((-478283/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log (84 : ℕ) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (84 : ℕ) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22041203/50000000) (δ := 263269/5000000000) 1053 371
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_85 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (85 : ℕ) / 2)) - ((-1396941/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log (85 : ℕ) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (85 : ℕ) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42773721/100000000) (δ := 263393/10000000000) 1053 372
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_86 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (86 : ℕ) / 2)) - ((-149107/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log (86 : ℕ) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (86 : ℕ) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39642689/100000000) (δ := 263381/10000000000) 1053 373
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_87 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (87 : ℕ) / 2)) - ((90233/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log (87 : ℕ) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (87 : ℕ) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17366701/50000000) (δ := 5267/200000000) 1053 374
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_88 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (88 : ℕ) / 2)) - ((865309/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log (88 : ℕ) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (88 : ℕ) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28084033/100000000) (δ := 131689/5000000000) 1053 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_89 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (89 : ℕ) / 2)) - ((3521489/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log (89 : ℕ) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (89 : ℕ) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19734069/100000000) (δ := 131703/5000000000) 1053 376
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_90 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (90 : ℕ) / 2)) - ((1156649/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log (90 : ℕ) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (90 : ℕ) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4861499/50000000) (δ := 263269/10000000000) 1053 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_91 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (91 : ℕ) / 2)) - ((4985369/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log (91 : ℕ) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (91 : ℕ) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -239123/12500000) (δ := 26327/500000000) 1053 378
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_92 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (92 : ℕ) / 2)) - ((2055459/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log (92 : ℕ) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (92 : ℕ) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3784749/25000000) (δ := 16457/625000000) 1053 379
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_93 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (93 : ℕ) / 2)) - ((146133/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log (93 : ℕ) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (93 : ℕ) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14960079/50000000) (δ := 263419/10000000000) 1053 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_94 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (94 : ℕ) / 2)) - ((-1372741/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log (94 : ℕ) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (94 : ℕ) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5777863/12500000) (δ := 32907/1250000000) 1053 381
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_95 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (95 : ℕ) / 2)) - ((-2089831/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log (95 : ℕ) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (95 : ℕ) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12803129/20000000) (δ := 65857/2500000000) 1053 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_96 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (96 : ℕ) / 2)) - ((-4910889/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log (96 : ℕ) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (96 : ℕ) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73812841/100000000) (δ := 8229/312500000) 1053 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_97 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (97 : ℕ) / 2)) - ((-658197/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log (97 : ℕ) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (97 : ℕ) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53133563/100000000) (δ := 32913/1250000000) 1053 383
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_98 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (98 : ℕ) / 2)) - ((645421/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log (98 : ℕ) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (98 : ℕ) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3881889/12500000) (δ := 263371/10000000000) 1053 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_99 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (99 : ℕ) / 2)) - ((1192587/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log (99 : ℕ) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (99 : ℕ) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1901611/25000000) (δ := 13163/500000000) 1053 385
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_100 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (100 : ℕ) / 2)) - ((7728701/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log (100 : ℕ) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (100 : ℕ) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3437223/20000000) (δ := 32911/1250000000) 1053 386
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_101 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (101 : ℕ) / 2)) - ((-80127/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log (101 : ℕ) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (101 : ℕ) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5411701/12500000) (δ := 263417/10000000000) 1053 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_102 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (102 : ℕ) / 2)) - ((-9511369/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log (102 : ℕ) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (102 : ℕ) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35346171/50000000) (δ := 52689/2000000000) 1053 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_103 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (103 : ℕ) / 2)) - ((-6728811/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log (103 : ℕ) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (103 : ℕ) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2308893/4000000) (δ := 131679/5000000000) 1053 388
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_104 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (104 : ℕ) / 2)) - ((4422433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log (104 : ℕ) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (104 : ℕ) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27817451/100000000) (δ := 26333/1000000000) 1053 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_105 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (105 : ℕ) / 2)) - ((1982563/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log (105 : ℕ) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (105 : ℕ) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1651819/50000000) (δ := 131651/5000000000) 1053 390
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_106 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (106 : ℕ) / 2)) - ((1454829/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log (106 : ℕ) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (106 : ℕ) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17809941/50000000) (δ := 131637/5000000000) 1053 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_107 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (107 : ℕ) / 2)) - ((-9296473/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log (107 : ℕ) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (107 : ℕ) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2159571/3125000) (δ := 52669/2000000000) 1053 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_108 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (108 : ℕ) / 2)) - ((-2667217/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log (108 : ℕ) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (108 : ℕ) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6667071/12500000) (δ := 52669/2000000000) 1053 392
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_109 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (109 : ℕ) / 2)) - ((3815121/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log (109 : ℕ) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (109 : ℕ) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17570433/100000000) (δ := 263417/10000000000) 1053 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_110 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (110 : ℕ) / 2)) - ((286577/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log (110 : ℕ) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (110 : ℕ) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19302669/100000000) (δ := 131657/5000000000) 1053 394
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_111 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (111 : ℕ) / 2)) - ((-6591767/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log (111 : ℕ) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (111 : ℕ) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57262993/100000000) (δ := 131671/5000000000) 1053 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_112 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (112 : ℕ) / 2)) - ((-7582677/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log (112 : ℕ) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (112 : ℕ) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12157241/20000000) (δ := 263361/10000000000) 1053 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_113 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (113 : ℕ) / 2)) - ((1352227/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log (113 : ℕ) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (113 : ℕ) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4141607/20000000) (δ := 263433/10000000000) 1053 396
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_114 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (114 : ℕ) / 2)) - ((3425399/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log (114 : ℕ) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (114 : ℕ) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5100519/25000000) (δ := 263399/10000000000) 1053 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_115 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (115 : ℕ) / 2)) - ((-8017269/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log (115 : ℕ) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (115 : ℕ) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31262191/50000000) (δ := 65819/2500000000) 1053 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_116 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (116 : ℕ) / 2)) - ((-467681/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log (116 : ℕ) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (116 : ℕ) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51436543/100000000) (δ := 65819/2500000000) 1053 398
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_117 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (117 : ℕ) / 2)) - ((4785973/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log (117 : ℕ) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (117 : ℕ) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3670589/50000000) (δ := 65837/2500000000) 1053 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_118 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (118 : ℕ) / 2)) - ((621017/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log (118 : ℕ) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (118 : ℕ) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18858183/50000000) (δ := 6583/250000000) 1053 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_119 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (119 : ℕ) / 2)) - ((-2446517/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log (119 : ℕ) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (119 : ℕ) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73359339/100000000) (δ := 6583/250000000) 1053 400
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_120 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (120 : ℕ) / 2)) - ((2457007/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log (120 : ℕ) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (120 : ℕ) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5285491/20000000) (δ := 65823/2500000000) 1053 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_121 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (121 : ℕ) / 2)) - ((6548827/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log (121 : ℕ) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (121 : ℕ) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21419223/100000000) (δ := 13167/500000000) 1053 402
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_122 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (122 : ℕ) / 2)) - ((-4722057/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log (122 : ℕ) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (122 : ℕ) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70164899/100000000) (δ := 52667/2000000000) 1053 403
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_123 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (123 : ℕ) / 2)) - ((396657/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log (123 : ℕ) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (123 : ℕ) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37284537/100000000) (δ := 65817/2500000000) 1053 403
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_124 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (124 : ℕ) / 2)) - ((4317499/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log (124 : ℕ) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (124 : ℕ) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13215701/100000000) (δ := 65849/2500000000) 1053 404
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_125 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (125 : ℕ) / 2)) - ((-2119819/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log (125 : ℕ) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (125 : ℕ) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -64571501/100000000) (δ := 65831/2500000000) 1053 405
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_126 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (126 : ℕ) / 2)) - ((-41589/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log (126 : ℕ) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (126 : ℕ) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10077483/25000000) (δ := 263379/10000000000) 1053 405
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_127 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (127 : ℕ) / 2)) - ((4366763/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log (127 : ℕ) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (127 : ℕ) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6359411/50000000) (δ := 263351/10000000000) 1053 406
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_128 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (128 : ℕ) / 2)) - ((-1774821/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log (128 : ℕ) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (128 : ℕ) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13312467/20000000) (δ := 263281/10000000000) 1053 407
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_129 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (129 : ℕ) / 2)) - ((1355429/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log (129 : ℕ) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (129 : ℕ) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35870873/100000000) (δ := 131711/5000000000) 1053 407
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_130 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (130 : ℕ) / 2)) - ((3544999/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log (130 : ℕ) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (130 : ℕ) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3913587/20000000) (δ := 131647/5000000000) 1053 408
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_131 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (131 : ℕ) / 2)) - ((-4969667/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log (131 : ℕ) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (131 : ℕ) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75784647/100000000) (δ := 263437/10000000000) 1053 409
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_132 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (132 : ℕ) / 2)) - ((1408221/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log (132 : ℕ) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (132 : ℕ) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24310901/100000000) (δ := 131633/5000000000) 1053 409
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_133 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (133 : ℕ) / 2)) - ((1157639/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log (133 : ℕ) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (133 : ℕ) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4178589/12500000) (δ := 52673/2000000000) 1053 410
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_134 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (134 : ℕ) / 2)) - ((-2753/3200 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log (134 : ℕ) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (134 : ℕ) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 65166969/100000000) (δ := 263269/5000000000) 1053 410
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_135 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (135 : ℕ) / 2)) - ((9718127/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log (135 : ℕ) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (135 : ℕ) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2974933/50000000) (δ := 26341/1000000000) 1053 411
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_136 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (136 : ℕ) / 2)) - ((-27767/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log (136 : ℕ) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (136 : ℕ) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53989201/100000000) (δ := 131661/5000000000) 1053 412
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_137 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (137 : ℕ) / 2)) - ((-10119/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log (137 : ℕ) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (137 : ℕ) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4244059/10000000) (δ := 131711/5000000000) 1053 412
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_138 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (138 : ℕ) / 2)) - ((727253/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log (138 : ℕ) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (138 : ℕ) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18912129/100000000) (δ := 5269/200000000) 1053 413
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_139 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (139 : ℕ) / 2)) - ((-2488347/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log (139 : ℕ) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (139 : ℕ) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7612507/10000000) (δ := 5267/200000000) 1053 413
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_140 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (140 : ℕ) / 2)) - ((1074677/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log (140 : ℕ) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (140 : ℕ) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13400819/100000000) (δ := 10533/400000000) 1053 414
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_141 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (141 : ℕ) / 2)) - ((-4160027/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log (141 : ℕ) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (141 : ℕ) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12499009/25000000) (δ := 263397/10000000000) 1053 415
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_142 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (142 : ℕ) / 2)) - ((-93549/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log (142 : ℕ) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (142 : ℕ) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 672281/1562500) (δ := 263397/10000000000) 1053 415
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_143 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (143 : ℕ) / 2)) - ((404267/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log (143 : ℕ) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (143 : ℕ) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21684489/100000000) (δ := 263269/10000000000) 1053 416
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_144 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (144 : ℕ) / 2)) - ((-2356883/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log (144 : ℕ) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (144 : ℕ) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17509927/25000000) (δ := 131717/5000000000) 1053 416
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_145 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (145 : ℕ) / 2)) - ((154203/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log (145 : ℕ) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (145 : ℕ) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4051157/100000000) (δ := 263263/10000000000) 1053 417
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_146 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (146 : ℕ) / 2)) - ((-4013357/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log (146 : ℕ) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (146 : ℕ) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62563929/100000000) (δ := 65853/2500000000) 1053 418
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_147 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (147 : ℕ) / 2)) - ((4613509/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log (147 : ℕ) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (147 : ℕ) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27281979/100000000) (δ := 263391/10000000000) 1053 418
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_148 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (148 : ℕ) / 2)) - ((-515749/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log (148 : ℕ) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (148 : ℕ) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10139963/25000000) (δ := 65821/2500000000) 1053 419
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_149 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (149 : ℕ) / 2)) - ((-3450699/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log (149 : ℕ) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (149 : ℕ) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48077739/100000000) (δ := 263319/10000000000) 1053 419
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_150 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (150 : ℕ) / 2)) - ((3343379/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log (150 : ℕ) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (150 : ℕ) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20959247/100000000) (δ := 65839/2500000000) 1053 420
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_151 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (151 : ℕ) / 2)) - ((-8862639/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log (151 : ℕ) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (151 : ℕ) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 665003/1000000) (δ := 263347/10000000000) 1053 420
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_152 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (152 : ℕ) / 2)) - ((494541/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log (152 : ℕ) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (152 : ℕ) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3697619/100000000) (δ := 2107/80000000) 1053 421
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_153 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (153 : ℕ) / 2)) - ((-2466873/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log (153 : ℕ) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (153 : ℕ) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37232737/50000000) (δ := 32913/1250000000) 1053 422
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_154 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (154 : ℕ) / 2)) - ((8998501/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log (154 : ℕ) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (154 : ℕ) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2256853/20000000) (δ := 263299/10000000000) 1053 422
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_155 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (155 : ℕ) / 2)) - ((-1506839/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log (155 : ℕ) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (155 : ℕ) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60601087/100000000) (δ := 32929/1250000000) 1053 423
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_156 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (156 : ℕ) / 2)) - ((5720237/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log (156 : ℕ) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (156 : ℕ) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4809127/20000000) (δ := 263371/10000000000) 1053 423
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_157 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (157 : ℕ) / 2)) - ((-75359/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log (157 : ℕ) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (157 : ℕ) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9785651/20000000) (δ := 263443/10000000000) 1053 424
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_158 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (158 : ℕ) / 2)) - ((92009/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log (158 : ℕ) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (158 : ℕ) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3464309/10000000) (δ := 263443/10000000000) 1053 424
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_159 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (159 : ℕ) / 2)) - ((-12179/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log (159 : ℕ) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (159 : ℕ) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19695849/50000000) (δ := 52663/2000000000) 1053 425
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_160 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (160 : ℕ) / 2)) - ((-307733/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log (160 : ℕ) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (160 : ℕ) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5391489/12500000) (δ := 52663/2000000000) 1053 425
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_161 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (161 : ℕ) / 2)) - ((2890609/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log (161 : ℕ) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (161 : ℕ) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6387753/20000000) (δ := 32927/1250000000) 1053 426
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_162 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (162 : ℕ) / 2)) - ((-800411/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log (162 : ℕ) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (162 : ℕ) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9912687/20000000) (δ := 32927/1250000000) 1053 426
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_163 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (163 : ℕ) / 2)) - ((976663/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log (163 : ℕ) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (163 : ℕ) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26515489/100000000) (δ := 52689/2000000000) 1053 427
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_164 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (164 : ℕ) / 2)) - ((-5553331/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log (164 : ℕ) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (164 : ℕ) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26994497/50000000) (δ := 131629/5000000000) 1053 427
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_165 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (165 : ℕ) / 2)) - ((6034051/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log (165 : ℕ) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (165 : ℕ) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23075801/100000000) (δ := 26333/1000000000) 1053 428
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_166 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (166 : ℕ) / 2)) - ((-6345627/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log (166 : ℕ) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (166 : ℕ) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 56455973/100000000) (δ := 26343/1000000000) 1053 428
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_167 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (167 : ℕ) / 2)) - ((52029/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log (167 : ℕ) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (167 : ℕ) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21568369/100000000) (δ := 263301/10000000000) 1053 429
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_168 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (168 : ℕ) / 2)) - ((-814533/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log (168 : ℕ) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (168 : ℕ) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3563317/6250000) (δ := 263401/10000000000) 1053 429
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_169 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (169 : ℕ) / 2)) - ((6386989/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log (169 : ℕ) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (169 : ℕ) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4389951/20000000) (δ := 131687/5000000000) 1053 430
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_170 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (170 : ℕ) / 2)) - ((-1527663/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log (170 : ℕ) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (170 : ℕ) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27852523/50000000) (δ := 131637/5000000000) 1053 430
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_171 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (171 : ℕ) / 2)) - ((354853/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log (171 : ℕ) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (171 : ℕ) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3021901/12500000) (δ := 263257/10000000000) 1053 431
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_172 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (172 : ℕ) / 2)) - ((-2536997/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log (172 : ℕ) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (172 : ℕ) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52574013/100000000) (δ := 263357/10000000000) 1053 431
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_173 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (173 : ℕ) / 2)) - ((4284211/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log (173 : ℕ) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (173 : ℕ) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28201291/100000000) (δ := 131693/5000000000) 1053 432
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_174 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (174 : ℕ) / 2)) - ((-3294681/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log (174 : ℕ) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (174 : ℕ) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 47663411/100000000) (δ := 263417/10000000000) 1053 432
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_175 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (175 : ℕ) / 2)) - ((524477/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log (175 : ℕ) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (175 : ℕ) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33985883/100000000) (δ := 263389/10000000000) 1053 433
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_176 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (176 : ℕ) / 2)) - ((-5446/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log (176 : ℕ) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (176 : ℕ) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20507021/50000000) (δ := 263389/10000000000) 1053 433
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_177 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (177 : ℕ) / 2)) - ((-88667/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log (177 : ℕ) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (177 : ℕ) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41489499/100000000) (δ := 131721/5000000000) 1053 434
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_178 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (178 : ℕ) / 2)) - ((163199/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log (178 : ℕ) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (178 : ℕ) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16332697/50000000) (δ := 263261/10000000000) 1053 434
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_179 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (179 : ℕ) / 2)) - ((-220253/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log (179 : ℕ) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (179 : ℕ) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10134793/20000000) (δ := 26327/1000000000) 1053 435
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_180 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (180 : ℕ) / 2)) - ((6167627/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log (180 : ℕ) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (180 : ℕ) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22654323/100000000) (δ := 263433/10000000000) 1053 435
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_181 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (181 : ℕ) / 2)) - ((-1553263/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log (181 : ℕ) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (181 : ℕ) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15375607/25000000) (δ := 263399/10000000000) 1053 436
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_182 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (182 : ℕ) / 2)) - ((4522251/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log (182 : ℕ) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (182 : ℕ) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5508841/50000000) (δ := 263399/10000000000) 1053 436
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_183 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (183 : ℕ) / 2)) - ((-4915533/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log (183 : ℕ) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (183 : ℕ) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4621127/6250000) (δ := 263427/10000000000) 1053 437
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_184 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (184 : ℕ) / 2)) - ((1992207/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log (184 : ℕ) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (184 : ℕ) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -275959/12500000) (δ := 263427/10000000000) 1053 437
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_185 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (185 : ℕ) / 2)) - ((-2325153/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log (185 : ℕ) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (185 : ℕ) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13826879/20000000) (δ := 16461/625000000) 1053 437
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_186 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (186 : ℕ) / 2)) - ((1555707/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log (186 : ℕ) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (186 : ℕ) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16988833/100000000) (δ := 52651/2000000000) 1053 438
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_187 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (187 : ℕ) / 2)) - ((-1354849/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log (187 : ℕ) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (187 : ℕ) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13397123/25000000) (δ := 52651/2000000000) 1053 438
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_188 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (188 : ℕ) / 2)) - ((473721/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log (188 : ℕ) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (188 : ℕ) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33291579/100000000) (δ := 13171/500000000) 1053 439
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_189 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (189 : ℕ) / 2)) - ((1091067/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log (189 : ℕ) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (189 : ℕ) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36536799/100000000) (δ := 263383/10000000000) 1053 439
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_190 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (190 : ℕ) / 2)) - ((-4551819/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log (190 : ℕ) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (190 : ℕ) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -51084321/100000000) (δ := 263311/10000000000) 1053 440
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_191 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (191 : ℕ) / 2)) - ((375759/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log (191 : ℕ) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (191 : ℕ) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18010907/100000000) (δ := 8231/312500000) 1053 440
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_192 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (192 : ℕ) / 2)) - ((-378653/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log (192 : ℕ) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (192 : ℕ) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70335467/100000000) (δ := 263363/10000000000) 1053 441
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_193 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (193 : ℕ) / 2)) - ((9969317/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log (193 : ℕ) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (193 : ℕ) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7652/390625) (δ := 263363/10000000000) 1053 441
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_194 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (194 : ℕ) / 2)) - ((-8780629/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log (194 : ℕ) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (194 : ℕ) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8258111/12500000) (δ := 263363/10000000000) 1053 441
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_195 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (195 : ℕ) / 2)) - ((59491/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log (195 : ℕ) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (195 : ℕ) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23341067/100000000) (δ := 52687/2000000000) 1053 442
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_196 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (196 : ℕ) / 2)) - ((-1875439/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log (196 : ℕ) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (196 : ℕ) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10996609/25000000) (δ := 32921/1250000000) 1053 442
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_197 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (197 : ℕ) / 2)) - ((-1350613/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log (197 : ℕ) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (197 : ℕ) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23053959/50000000) (δ := 65849/2500000000) 1053 443
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_198 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (198 : ℕ) / 2)) - ((3405579/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log (198 : ℕ) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (198 : ℕ) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20537769/100000000) (δ := 263407/10000000000) 1053 443
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_199 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (199 : ℕ) / 2)) - ((-9452881/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log (199 : ℕ) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (199 : ℕ) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35115911/50000000) (δ := 1029/39062500) 1053 444
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_200 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (200 : ℕ) / 2)) - ((9855523/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log (200 : ℕ) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (200 : ℕ) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -425479/10000000) (δ := 263379/10000000000) 1053 444
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_201 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (201 : ℕ) / 2)) - ((-1547809/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log (201 : ℕ) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (201 : ℕ) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12278899/20000000) (δ := 263379/10000000000) 1053 444
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_202 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (202 : ℕ) / 2)) - ((871911/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log (202 : ℕ) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (202 : ℕ) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30363599/100000000) (δ := 263351/10000000000) 1053 445
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_203 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (203 : ℕ) / 2)) - ((1842663/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log (203 : ℕ) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (203 : ℕ) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1385471/4000000) (δ := 263451/10000000000) 1053 445
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_204 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (204 : ℕ) / 2)) - ((-6740641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log (204 : ℕ) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (204 : ℕ) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57762333/100000000) (δ := 131661/5000000000) 1053 446
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_205 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (205 : ℕ) / 2)) - ((96533/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log (205 : ℕ) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (205 : ℕ) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1650573/25000000) (δ := 131661/5000000000) 1053 446
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_206 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (206 : ℕ) / 2)) - ((-9506579/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log (206 : ℕ) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (206 : ℕ) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70653649/100000000) (δ := 263381/10000000000) 1053 446
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_207 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (207 : ℕ) / 2)) - ((3078941/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log (207 : ℕ) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (207 : ℕ) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22685261/100000000) (δ := 263309/10000000000) 1053 447
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_208 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (208 : ℕ) / 2)) - ((-295601/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log (208 : ℕ) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (208 : ℕ) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1629951/4000000) (δ := 263409/10000000000) 1053 447
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_209 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (209 : ℕ) / 2)) - ((-2644223/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log (209 : ℕ) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (209 : ℕ) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -425607/800000) (δ := 263337/10000000000) 1053 448
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_210 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (210 : ℕ) / 2)) - ((9267581/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log (210 : ℕ) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (210 : ℕ) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4813843/50000000) (δ := 263437/10000000000) 1053 448
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_211 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (211 : ℕ) / 2)) - ((-967589/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log (211 : ℕ) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (211 : ℕ) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 72157459/100000000) (δ := 131633/5000000000) 1053 448
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_212 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (212 : ℕ) / 2)) - ((6156843/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log (212 : ℕ) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (212 : ℕ) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22688557/100000000) (δ := 131719/5000000000) 1053 449
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_213 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (213 : ℕ) / 2)) - ((6823/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log (213 : ℕ) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (213 : ℕ) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39252851/100000000) (δ := 52673/2000000000) 1053 449
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_214 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (214 : ℕ) / 2)) - ((-125167/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log (214 : ℕ) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (214 : ℕ) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14043737/25000000) (δ := 263393/10000000000) 1053 450
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_215 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (215 : ℕ) / 2)) - ((9785397/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log (215 : ℕ) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (215 : ℕ) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5188627/100000000) (δ := 263393/10000000000) 1053 450
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_216 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (216 : ℕ) / 2)) - ((-4409599/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log (216 : ℕ) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (216 : ℕ) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16566973/25000000) (δ := 263393/10000000000) 1053 450
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_217 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (217 : ℕ) / 2)) - ((361781/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log (217 : ℕ) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (217 : ℕ) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30015469/100000000) (δ := 263281/10000000000) 1053 451
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_218 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (218 : ℕ) / 2)) - ((3435797/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log (218 : ℕ) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (218 : ℕ) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30501757/100000000) (δ := 131661/5000000000) 1053 451
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_219 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (219 : ℕ) / 2)) - ((-8832207/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log (219 : ℕ) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (219 : ℕ) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33168531/50000000) (δ := 5267/200000000) 1053 452
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_220 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (220 : ℕ) / 2)) - ((4838501/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log (220 : ℕ) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (220 : ℕ) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -398209/6250000) (δ := 263353/10000000000) 1053 452
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_221 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (221 : ℕ) / 2)) - ((-5329919/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log (221 : ℕ) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (221 : ℕ) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26661613/50000000) (δ := 263353/10000000000) 1053 452
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_222 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (222 : ℕ) / 2)) - ((-1005707/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log (222 : ℕ) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (222 : ℕ) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5541623/12500000) (δ := 10537/400000000) 1053 453
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_223 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (223 : ℕ) / 2)) - ((4146389/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log (223 : ℕ) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (223 : ℕ) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3706139/25000000) (δ := 10537/400000000) 1053 453
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_224 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (224 : ℕ) / 2)) - ((-490727/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log (224 : ℕ) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (224 : ℕ) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73717529/100000000) (δ := 131689/5000000000) 1053 453
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_225 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (225 : ℕ) / 2)) - ((549323/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log (225 : ℕ) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (225 : ℕ) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24731063/100000000) (δ := 263397/10000000000) 1053 454
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_226 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (226 : ℕ) / 2)) - ((558371/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log (226 : ℕ) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (226 : ℕ) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33638701/100000000) (δ := 263253/5000000000) 1053 454
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_227 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (227 : ℕ) / 2)) - ((-8635749/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log (227 : ℕ) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (227 : ℕ) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16331959/25000000) (δ := 263269/10000000000) 1053 455
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_228 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (228 : ℕ) / 2)) - ((597301/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log (228 : ℕ) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (228 : ℕ) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7470751/100000000) (δ := 263269/10000000000) 1053 455
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_229 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (229 : ℕ) / 2)) - ((-4210007/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log (229 : ℕ) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (229 : ℕ) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25066807/50000000) (δ := 263269/10000000000) 1053 455
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_230 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (230 : ℕ) / 2)) - ((-4012911/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log (230 : ℕ) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (230 : ℕ) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49593057/100000000) (δ := 3293/125000000) 1053 456
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_231 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (231 : ℕ) / 2)) - ((597003/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log (231 : ℕ) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (231 : ℕ) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7511133/100000000) (δ := 3293/125000000) 1053 456
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_232 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (232 : ℕ) / 2)) - ((-1054477/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log (232 : ℕ) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (232 : ℕ) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16091967/25000000) (δ := 3293/125000000) 1053 456
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_233 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (233 : ℕ) / 2)) - ((1265149/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log (233 : ℕ) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (233 : ℕ) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4512317/12500000) (δ := 65853/2500000000) 1053 457
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_234 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (234 : ℕ) / 2)) - ((3444231/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log (234 : ℕ) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (234 : ℕ) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10136251/50000000) (δ := 263391/10000000000) 1053 457
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_235 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (235 : ℕ) / 2)) - ((-9963483/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log (235 : ℕ) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (235 : ℕ) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76402667/100000000) (δ := 263391/10000000000) 1053 457
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_236 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (236 : ℕ) / 2)) - ((219007/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log (236 : ℕ) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (236 : ℕ) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12392521/50000000) (δ := 263419/10000000000) 1053 458
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_237 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (237 : ℕ) / 2)) - ((824279/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log (237 : ℕ) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (237 : ℕ) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30869957/100000000) (δ := 263319/10000000000) 1053 458
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_238 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (238 : ℕ) / 2)) - ((-297601/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log (238 : ℕ) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (238 : ℕ) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70788969/100000000) (δ := 65839/2500000000) 1053 459
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_239 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (239 : ℕ) / 2)) - ((1014437/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log (239 : ℕ) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (239 : ℕ) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15599923/100000000) (δ := 32907/1250000000) 1053 459
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_240 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (240 : ℕ) / 2)) - ((-8887/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log (240 : ℕ) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (240 : ℕ) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39358779/100000000) (δ := 263447/10000000000) 1053 459
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_241 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (241 : ℕ) / 2)) - ((-1625493/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log (241 : ℕ) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (241 : ℕ) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31495589/50000000) (δ := 8229/312500000) 1053 460
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_242 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (242 : ℕ) / 2)) - ((235729/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log (242 : ℕ) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (242 : ℕ) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4243949/50000000) (δ := 8229/312500000) 1053 460
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_243 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (243 : ℕ) / 2)) - ((-20146/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log (243 : ℕ) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (243 : ℕ) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45790303/100000000) (δ := 10531/400000000) 1053 460
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_244 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (244 : ℕ) / 2)) - ((-3291457/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log (244 : ℕ) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (244 : ℕ) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2289343/4000000) (δ := 65851/2500000000) 1053 461
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_245 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (245 : ℕ) / 2)) - ((2476921/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log (245 : ℕ) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (245 : ℕ) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -424951/12500000) (δ := 131651/2500000000) 1053 461
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_246 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (246 : ℕ) / 2)) - ((-169593/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log (246 : ℕ) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (246 : ℕ) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25107931/50000000) (δ := 263399/10000000000) 1053 461
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_247 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (247 : ℕ) / 2)) - ((-5378201/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log (247 : ℕ) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (247 : ℕ) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53466141/100000000) (δ := 263271/10000000000) 1053 462
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_248 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (248 : ℕ) / 2)) - ((9999353/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log (248 : ℕ) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (248 : ℕ) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35547/12500000) (δ := 263271/10000000000) 1053 462
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_249 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (249 : ℕ) / 2)) - ((-5111457/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log (249 : ℕ) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (249 : ℕ) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1317071/2500000) (δ := 65833/2500000000) 1053 462
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_250 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (250 : ℕ) / 2)) - ((-4748651/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log (250 : ℕ) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (250 : ℕ) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3227511/6250000) (δ := 263343/10000000000) 1053 463
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_251 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (251 : ℕ) / 2)) - ((1998691/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log (251 : ℕ) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (251 : ℕ) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 226131/25000000) (δ := 263343/10000000000) 1053 463
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_252 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (252 : ℕ) / 2)) - ((-2650851/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log (252 : ℕ) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (252 : ℕ) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2661997/5000000) (δ := 13163/500000000) 1053 463
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_253 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (253 : ℕ) / 2)) - ((-2386769/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log (253 : ℕ) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (253 : ℕ) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3231933/6250000) (δ := 65847/2500000000) 1053 464
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_254 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (254 : ℕ) / 2)) - ((9999639/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log (254 : ℕ) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (254 : ℕ) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 106251/50000000) (δ := 65847/2500000000) 1053 464
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_255 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (255 : ℕ) / 2)) - ((-303189/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log (255 : ℕ) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (255 : ℕ) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25965957/50000000) (δ := 52683/2000000000) 1053 464
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_256 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (256 : ℕ) / 2)) - ((-2716841/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log (256 : ℕ) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (256 : ℕ) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5363101/10000000) (δ := 263387/10000000000) 1053 465
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_257 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (257 : ℕ) / 2)) - ((9957131/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log (257 : ℕ) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (257 : ℕ) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -289461/12500000) (δ := 65829/2500000000) 1053 465
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_258 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (258 : ℕ) / 2)) - ((-3720707/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log (258 : ℕ) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (258 : ℕ) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48800881/100000000) (δ := 263287/10000000000) 1053 465
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_259 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (259 : ℕ) / 2)) - ((-6620783/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log (259 : ℕ) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (259 : ℕ) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57359621/100000000) (δ := 52689/2000000000) 1053 466
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_260 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (260 : ℕ) / 2)) - ((2412427/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log (260 : ℕ) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (260 : ℕ) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6636611/100000000) (δ := 52689/2000000000) 1053 466
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_261 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (261 : ℕ) / 2)) - ((-919081/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log (261 : ℕ) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (261 : ℕ) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21945797/50000000) (δ := 52689/2000000000) 1053 466
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_262 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (262 : ℕ) / 2)) - ((-1619043/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log (262 : ℕ) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (262 : ℕ) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31426661/50000000) (δ := 789773/10000000000) 1053 467
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_263 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (263 : ℕ) / 2)) - ((8735093/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log (263 : ℕ) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (263 : ℕ) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6355389/50000000) (δ := 26333/1000000000) 1053 467
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_264 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (264 : ℕ) / 2)) - ((101273/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log (264 : ℕ) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (264 : ℕ) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18621113/50000000) (δ := 78993/1000000000) 1053 467
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_265 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (265 : ℕ) / 2)) - ((-943209/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log (265 : ℕ) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (265 : ℕ) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70073943/100000000) (δ := 131701/5000000000) 1053 468
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_266 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (266 : ℕ) / 2)) - ((106609/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log (266 : ℕ) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (266 : ℕ) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20497387/100000000) (δ := 131651/5000000000) 1053 468
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_267 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (267 : ℕ) / 2)) - ((1008217/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log (267 : ℕ) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (267 : ℕ) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14446131/50000000) (δ := 131701/5000000000) 1053 468
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_268 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (268 : ℕ) / 2)) - ((-2499609/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log (268 : ℕ) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (268 : ℕ) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15619527/20000000) (δ := 263401/10000000000) 1053 468
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_269 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (269 : ℕ) / 2)) - ((3638641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log (269 : ℕ) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (269 : ℕ) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14979791/50000000) (δ := 131687/5000000000) 1053 469
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_270 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (270 : ℕ) / 2)) - ((3640509/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log (270 : ℕ) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (270 : ℕ) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1888119/10000000) (δ := 263329/10000000000) 1053 469
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_271 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (271 : ℕ) / 2)) - ((-9047827/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log (271 : ℕ) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (271 : ℕ) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16885409/25000000) (δ := 263429/10000000000) 1053 469
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_272 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (272 : ℕ) / 2)) - ((-357289/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log (272 : ℕ) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (272 : ℕ) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10264469/25000000) (δ := 131673/5000000000) 1053 470
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_273 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (273 : ℕ) / 2)) - ((4791531/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log (273 : ℕ) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (273 : ℕ) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 144891/2000000) (δ := 263257/10000000000) 1053 470
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_274 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (274 : ℕ) / 2)) - ((-750579/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log (274 : ℕ) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (274 : ℕ) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11074383/20000000) (δ := 263257/10000000000) 1053 470
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_275 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (275 : ℕ) / 2)) - ((-547627/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log (275 : ℕ) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (275 : ℕ) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26879023/50000000) (δ := 263417/10000000000) 1053 471
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_276 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (276 : ℕ) / 2)) - ((4857601/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log (276 : ℕ) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (276 : ℕ) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1495201/25000000) (δ := 131643/5000000000) 1053 471
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_277 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (277 : ℕ) / 2)) - ((-3761/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log (277 : ℕ) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (277 : ℕ) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4162401/10000000) (δ := 263317/10000000000) 1053 471
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_278 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (278 : ℕ) / 2)) - ((-9128183/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log (278 : ℕ) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (278 : ℕ) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34011619/50000000) (δ := 131657/5000000000) 1053 472
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_279 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (279 : ℕ) / 2)) - ((269809/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log (279 : ℕ) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (279 : ℕ) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4152393/20000000) (δ := 263389/10000000000) 1053 472
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_280 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (280 : ℕ) / 2)) - ((4947183/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log (280 : ℕ) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (280 : ℕ) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26332143/100000000) (δ := 131707/5000000000) 1053 472
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_281 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (281 : ℕ) / 2)) - ((-9777519/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log (281 : ℕ) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (281 : ℕ) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9157057/12500000) (δ := 263289/10000000000) 1053 472
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_282 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (282 : ℕ) / 2)) - ((176187/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log (282 : ℕ) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (282 : ℕ) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4633089/12500000) (δ := 131671/5000000000) 1053 473
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_283 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (283 : ℕ) / 2)) - ((3713/4000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log (283 : ℕ) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (283 : ℕ) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4763953/50000000) (δ := 263361/10000000000) 1053 473
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_284 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (284 : ℕ) / 2)) - ((-6190213/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log (284 : ℕ) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (284 : ℕ) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13989327/25000000) (δ := 131671/5000000000) 1053 473
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_285 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (285 : ℕ) / 2)) - ((-182463/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log (285 : ℕ) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (285 : ℕ) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -54857453/100000000) (δ := 263333/10000000000) 1053 474
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_286 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (286 : ℕ) / 2)) - ((9393293/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log (286 : ℕ) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (286 : ℕ) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2188291/25000000) (δ := 263433/10000000000) 1053 474
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_287 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (287 : ℕ) / 2)) - ((51957/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log (287 : ℕ) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (287 : ℕ) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18594613/50000000) (δ := 263433/10000000000) 1053 474
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_288 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (288 : ℕ) / 2)) - ((-393733/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log (288 : ℕ) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (288 : ℕ) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -370543/500000) (δ := 131699/5000000000) 1053 475
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_289 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (289 : ℕ) / 2)) - ((418149/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log (289 : ℕ) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (289 : ℕ) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14242371/50000000) (δ := 52661/2000000000) 1053 475
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_290 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (290 : ℕ) / 2)) - ((7780131/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log (290 : ℕ) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (290 : ℕ) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8491241/50000000) (δ := 52681/2000000000) 1053 475
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_291 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (291 : ℕ) / 2)) - ((-7961307/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log (291 : ℕ) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (291 : ℕ) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12458351/20000000) (δ := 131699/5000000000) 1053 475
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_292 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (292 : ℕ) / 2)) - ((-805479/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log (292 : ℕ) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (292 : ℕ) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9926521/20000000) (δ := 263327/10000000000) 1053 476
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_293 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (293 : ℕ) / 2)) - ((9828799/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log (293 : ℕ) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (293 : ℕ) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -92653/2000000) (δ := 263327/10000000000) 1053 476
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_294 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (294 : ℕ) / 2)) - ((-377269/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log (294 : ℕ) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (294 : ℕ) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5026663/12500000) (δ := 65819/2500000000) 1053 476
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_295 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (295 : ℕ) / 2)) - ((-2419333/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log (295 : ℕ) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (295 : ℕ) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2255367/3125000) (δ := 52671/2000000000) 1053 477
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_296 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (296 : ℕ) / 2)) - ((1122521/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log (296 : ℕ) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (296 : ℕ) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27628527/100000000) (δ := 32931/1250000000) 1053 477
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_297 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (297 : ℕ) / 2)) - ((391729/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log (297 : ℕ) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (297 : ℕ) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4191159/25000000) (δ := 52671/2000000000) 1053 477
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_298 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (298 : ℕ) / 2)) - ((-955019/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log (298 : ℕ) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (298 : ℕ) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15251937/25000000) (δ := 32931/1250000000) 1053 477
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_299 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (299 : ℕ) / 2)) - ((-608313/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log (299 : ℕ) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (299 : ℕ) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25988097/50000000) (δ := 263283/10000000000) 1053 478
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_300 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (300 : ℕ) / 2)) - ((1897767/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log (300 : ℕ) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (300 : ℕ) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8027923/100000000) (δ := 263383/10000000000) 1053 478
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_301 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (301 : ℕ) / 2)) - ((1393713/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log (301 : ℕ) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (301 : ℕ) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7154849/20000000) (δ := 6583/250000000) 1053 478
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_302 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (302 : ℕ) / 2)) - ((-4996819/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log (302 : ℕ) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (302 : ℕ) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9706001/12500000) (δ := 263311/10000000000) 1053 479
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_303 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (303 : ℕ) / 2)) - ((2039389/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log (303 : ℕ) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (303 : ℕ) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6827083/20000000) (δ := 8231/312500000) 1053 479
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_304 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (304 : ℕ) / 2)) - ((2331407/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log (304 : ℕ) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (304 : ℕ) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4616853/50000000) (δ := 65823/2500000000) 1053 479
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_305 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (305 : ℕ) / 2)) - ((-5034421/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log (305 : ℕ) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (305 : ℕ) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13114839/25000000) (δ := 65823/2500000000) 1053 479
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_306 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (306 : ℕ) / 2)) - ((-3887151/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log (306 : ℕ) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (306 : ℕ) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61534149/100000000) (δ := 65841/2500000000) 1053 480
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_307 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (307 : ℕ) / 2)) - ((1472063/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log (307 : ℕ) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (307 : ℕ) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18590177/100000000) (δ := 263339/10000000000) 1053 480
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_308 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (308 : ℕ) / 2)) - ((2832389/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log (308 : ℕ) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (308 : ℕ) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24214273/100000000) (δ := 263339/10000000000) 1053 480
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_309 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (309 : ℕ) / 2)) - ((-1786411/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log (309 : ℕ) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (309 : ℕ) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66880517/100000000) (δ := 8227/312500000) 1053 480
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_310 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (310 : ℕ) / 2)) - ((-412197/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log (310 : ℕ) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (310 : ℕ) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23835539/50000000) (δ := 52667/2000000000) 1053 481
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_311 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (311 : ℕ) / 2)) - ((9777917/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log (311 : ℕ) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (311 : ℕ) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2639307/50000000) (δ := 52687/2000000000) 1053 481
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_312 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (312 : ℕ) / 2)) - ((458209/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log (312 : ℕ) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (312 : ℕ) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36975643/100000000) (δ := 65817/2500000000) 1053 481
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_313 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (313 : ℕ) / 2)) - ((-9997529/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log (313 : ℕ) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (313 : ℕ) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7798399/10000000) (δ := 65849/2500000000) 1053 482
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_314 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (314 : ℕ) / 2)) - ((326233/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log (314 : ℕ) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (314 : ℕ) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35998247/100000000) (δ := 263307/10000000000) 1053 482
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_315 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (315 : ℕ) / 2)) - ((2431761/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log (315 : ℕ) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (315 : ℕ) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2927277/50000000) (δ := 2057/78125000) 1053 482
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_316 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (316 : ℕ) / 2)) - ((-407631/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log (316 : ℕ) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (316 : ℕ) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23787207/50000000) (δ := 2057/78125000) 1053 482
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_317 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (317 : ℕ) / 2)) - ((-4555481/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log (317 : ℕ) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (317 : ℕ) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -679183/1000000) (δ := 65831/2500000000) 1053 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_318 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (318 : ℕ) / 2)) - ((4902083/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log (318 : ℕ) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (318 : ℕ) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2646169/10000000) (δ := 65831/2500000000) 1053 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_319 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (319 : ℕ) / 2)) - ((4141759/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log (319 : ℕ) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (319 : ℕ) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1858241/12500000) (δ := 263379/10000000000) 1053 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_320 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (320 : ℕ) / 2)) - ((-6223023/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log (320 : ℕ) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (320 : ℕ) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 350387/625000) (δ := 65831/2500000000) 1053 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_321 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (321 : ℕ) / 2)) - ((-7359893/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log (321 : ℕ) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (321 : ℕ) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -749351/1250000) (δ := 65813/2500000000) 1053 484
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_322 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (322 : ℕ) / 2)) - ((724631/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log (322 : ℕ) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (322 : ℕ) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -237593/1250000) (δ := 65813/2500000000) 1053 484
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_323 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (323 : ℕ) / 2)) - ((6430871/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log (323 : ℕ) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (323 : ℕ) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 545171/2500000) (δ := 65813/2500000000) 1053 484
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_324 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (324 : ℕ) / 2)) - ((-4005091/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log (324 : ℕ) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (324 : ℕ) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1562369/2500000) (δ := 65813/2500000000) 1053 484
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_325 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (325 : ℕ) / 2)) - ((-2782371/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log (325 : ℕ) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (325 : ℕ) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -54023313/100000000) (δ := 263381/10000000000) 1053 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_326 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (326 : ℕ) / 2)) - ((8559457/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log (326 : ℕ) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (326 : ℕ) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -339637/2500000) (δ := 131661/5000000000) 1053 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_327 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (327 : ℕ) / 2)) - ((4808741/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log (327 : ℕ) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (327 : ℕ) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 213829/800000) (δ := 131661/5000000000) 1053 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_328 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (328 : ℕ) / 2)) - ((-4469601/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log (328 : ℕ) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (328 : ℕ) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66920319/100000000) (δ := 131711/5000000000) 1053 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_329 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (329 : ℕ) / 2)) - ((-2097333/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log (329 : ℕ) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (329 : ℕ) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12522837/25000000) (δ := 263309/10000000000) 1053 486
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_330 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (330 : ℕ) / 2)) - ((9187951/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log (330 : ℕ) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (330 : ℕ) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10144477/100000000) (δ := 263409/10000000000) 1053 486
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_331 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (331 : ℕ) / 2)) - ((233881/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log (331 : ℕ) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (331 : ℕ) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 296813/1000000) (δ := 131697/5000000000) 1053 486
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_332 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (332 : ℕ) / 2)) - ((-9337303/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log (332 : ℕ) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (332 : ℕ) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 69387297/100000000) (δ := 263309/10000000000) 1053 486
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_333 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (333 : ℕ) / 2)) - ((-3461351/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log (333 : ℕ) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (333 : ℕ) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -48106117/100000000) (δ := 263337/10000000000) 1053 487
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_334 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (334 : ℕ) / 2)) - ((4704473/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log (334 : ℕ) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (334 : ℕ) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8638361/100000000) (δ := 263437/10000000000) 1053 487
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_335 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (335 : ℕ) / 2)) - ((671321/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log (335 : ℕ) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (335 : ℕ) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30712249/100000000) (δ := 263437/10000000000) 1053 487
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_336 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (336 : ℕ) / 2)) - ((-37659/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log (336 : ℕ) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (336 : ℕ) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 69944397/100000000) (δ := 131633/5000000000) 1053 487
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_337 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (337 : ℕ) / 2)) - ((-1714303/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log (337 : ℕ) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (337 : ℕ) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24009459/50000000) (δ := 131669/5000000000) 1053 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_338 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (338 : ℕ) / 2)) - ((9356183/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log (338 : ℕ) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (338 : ℕ) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9019747/100000000) (δ := 52653/2000000000) 1053 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_339 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (339 : ℕ) / 2)) - ((1836699/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log (339 : ℕ) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (339 : ℕ) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29866227/100000000) (δ := 131669/5000000000) 1053 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_340 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (340 : ℕ) / 2)) - ((-9225581/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log (340 : ℕ) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (340 : ℕ) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 68636371/100000000) (δ := 131719/5000000000) 1053 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_341 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (341 : ℕ) / 2)) - ((-4084077/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log (341 : ℕ) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (341 : ℕ) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3111727/6250000) (δ := 26331/1000000000) 1053 489
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_342 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (342 : ℕ) / 2)) - ((1801107/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log (342 : ℕ) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (342 : ℕ) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11243883/100000000) (δ := 26341/1000000000) 1053 489
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_343 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (343 : ℕ) / 2)) - ((46473/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log (343 : ℕ) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (343 : ℕ) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6796667/25000000) (δ := 26331/1000000000) 1053 489
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_344 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (344 : ℕ) / 2)) - ((-8671331/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log (344 : ℕ) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (344 : ℕ) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32752669/50000000) (δ := 26331/1000000000) 1053 489
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_345 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (345 : ℕ) / 2)) - ((-5344453/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log (345 : ℕ) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (345 : ℕ) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5336619/10000000) (δ := 131661/5000000000) 1053 490
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_346 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (346 : ℕ) / 2)) - ((4095951/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log (346 : ℕ) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (346 : ℕ) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7634983/50000000) (δ := 263281/10000000000) 1053 490
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_347 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (347 : ℕ) / 2)) - ((6147871/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log (347 : ℕ) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (347 : ℕ) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22717009/100000000) (δ := 263281/10000000000) 1053 490
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_348 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (348 : ℕ) / 2)) - ((-1883131/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log (348 : ℕ) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (348 : ℕ) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12118947/20000000) (δ := 131661/5000000000) 1053 490
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_349 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (349 : ℕ) / 2)) - ((-7017193/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log (349 : ℕ) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (349 : ℕ) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1834847/3125000) (δ := 5267/200000000) 1053 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_350 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (350 : ℕ) / 2)) - ((3329181/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log (350 : ℕ) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (350 : ℕ) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21054559/100000000) (δ := 5267/200000000) 1053 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_351 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (351 : ℕ) / 2)) - ((7900077/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log (351 : ℕ) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (351 : ℕ) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1649937/10000000) (δ := 263253/10000000000) 1053 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_352 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (352 : ℕ) / 2)) - ((-5538809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log (352 : ℕ) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (352 : ℕ) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26972683/50000000) (δ := 5267/200000000) 1053 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_353 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (353 : ℕ) / 2)) - ((-4364089/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log (353 : ℕ) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (353 : ℕ) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6579357/10000000) (δ := 10533/400000000) 1053 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_354 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (354 : ℕ) / 2)) - ((415479/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log (354 : ℕ) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (354 : ℕ) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14279087/50000000) (δ := 131639/5000000000) 1053 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_355 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (355 : ℕ) / 2)) - ((9418091/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log (355 : ℕ) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (355 : ℕ) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4285303/50000000) (δ := 131639/5000000000) 1053 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_356 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (356 : ℕ) / 2)) - ((-2503797/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log (356 : ℕ) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (356 : ℕ) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45596719/100000000) (δ := 10537/400000000) 1053 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_357 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (357 : ℕ) / 2)) - ((-9873689/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log (357 : ℕ) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (357 : ℕ) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37281051/50000000) (δ := 131703/5000000000) 1053 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_358 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (358 : ℕ) / 2)) - ((305001/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log (358 : ℕ) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (358 : ℕ) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37743957/100000000) (δ := 131703/5000000000) 1053 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_359 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (359 : ℕ) / 2)) - ((9991539/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log (359 : ℕ) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (359 : ℕ) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1028479/100000000) (δ := 263297/10000000000) 1053 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_360 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (360 : ℕ) / 2)) - ((183547/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log (360 : ℕ) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (360 : ℕ) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35585647/100000000) (δ := 131653/5000000000) 1053 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_361 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (361 : ℕ) / 2)) - ((-4834883/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log (361 : ℕ) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (361 : ℕ) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36048553/50000000) (δ := 263297/10000000000) 1053 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_362 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (362 : ℕ) / 2)) - ((-3635239/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log (362 : ℕ) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (362 : ℕ) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -48571103/100000000) (δ := 263269/10000000000) 1053 494
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_363 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (363 : ℕ) / 2)) - ((8821251/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log (363 : ℕ) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (363 : ℕ) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12261031/100000000) (δ := 131717/5000000000) 1053 494
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_364 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (364 : ℕ) / 2)) - ((5751897/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log (364 : ℕ) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (364 : ℕ) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23949007/100000000) (δ := 263269/10000000000) 1053 494
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_365 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (365 : ℕ) / 2)) - ((-1478043/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log (365 : ℕ) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (365 : ℕ) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30030163/50000000) (δ := 263369/10000000000) 1053 494
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_366 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (366 : ℕ) / 2)) - ((-7639883/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log (366 : ℕ) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (366 : ℕ) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61006707/100000000) (δ := 263263/10000000000) 1053 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_367 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (367 : ℕ) / 2)) - ((2685871/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log (367 : ℕ) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (367 : ℕ) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12546413/50000000) (δ := 263363/10000000000) 1053 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_368 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (368 : ℕ) / 2)) - ((4547023/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log (368 : ℕ) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (368 : ℕ) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10723653/100000000) (δ := 263263/10000000000) 1053 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_369 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (369 : ℕ) / 2)) - ((-1414963/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log (369 : ℕ) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (369 : ℕ) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46442729/100000000) (δ := 263363/10000000000) 1053 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_370 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (370 : ℕ) / 2)) - ((-9900709/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log (370 : ℕ) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (370 : ℕ) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75013913/100000000) (δ := 65853/2500000000) 1053 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_371 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (371 : ℕ) / 2)) - ((-43683/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log (371 : ℕ) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (371 : ℕ) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19744163/50000000) (δ := 263291/10000000000) 1053 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_372 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (372 : ℕ) / 2)) - ((4934291/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log (372 : ℕ) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (372 : ℕ) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1014377/25000000) (δ := 65853/2500000000) 1053 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_373 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (373 : ℕ) / 2)) - ((785597/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log (373 : ℕ) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (373 : ℕ) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31278539/100000000) (δ := 263291/10000000000) 1053 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_374 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (374 : ℕ) / 2)) - ((-8866009/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log (374 : ℕ) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (374 : ℕ) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 133037/200000) (δ := 263391/10000000000) 1053 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_375 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (375 : ℕ) / 2)) - ((-752233/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log (375 : ℕ) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (375 : ℕ) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55413309/100000000) (δ := 263419/10000000000) 1053 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_376 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (376 : ℕ) / 2)) - ((274519/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log (376 : ℕ) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (376 : ℕ) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4072051/20000000) (δ := 263319/10000000000) 1053 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_377 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (377 : ℕ) / 2)) - ((8342783/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log (377 : ℕ) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (377 : ℕ) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2919869/20000000) (δ := 263319/10000000000) 1053 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_378 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (378 : ℕ) / 2)) - ((-793321/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log (378 : ℕ) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (378 : ℕ) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6183351/12500000) (δ := 32923/1250000000) 1053 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_379 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (379 : ℕ) / 2)) - ((-2435219/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log (379 : ℕ) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (379 : ℕ) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9104523/12500000) (δ := 263347/10000000000) 1053 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_380 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (380 : ℕ) / 2)) - ((55827/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log (380 : ℕ) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (380 : ℕ) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9538249/25000000) (δ := 65839/2500000000) 1053 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_381 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (381 : ℕ) / 2)) - ((9898747/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log (381 : ℕ) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (381 : ℕ) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -356063/10000000) (δ := 32907/1250000000) 1053 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_382 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (382 : ℕ) / 2)) - ((3269809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log (382 : ℕ) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (382 : ℕ) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30942231/100000000) (δ := 263347/10000000000) 1053 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_383 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (383 : ℕ) / 2)) - ((-8640811/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log (383 : ℕ) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (383 : ℕ) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13070591/20000000) (δ := 32907/1250000000) 1053 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_384 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (384 : ℕ) / 2)) - ((-6634119/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log (384 : ℕ) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (384 : ℕ) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57404143/100000000) (δ := 2107/80000000) 1053 499
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_385 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (385 : ℕ) / 2)) - ((1200721/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log (385 : ℕ) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (385 : ℕ) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23171113/100000000) (δ := 2107/80000000) 1053 499
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_386 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (386 : ℕ) / 2)) - ((9052211/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log (386 : ℕ) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (386 : ℕ) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2743103/25000000) (δ := 2107/80000000) 1053 499
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_387 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (387 : ℕ) / 2)) - ((-2282829/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log (387 : ℕ) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (387 : ℕ) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45027749/100000000) (δ := 65857/2500000000) 1053 499
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_388 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (388 : ℕ) / 2)) - ((-4999167/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log (388 : ℕ) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (388 : ℕ) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3904171/5000000) (δ := 263399/10000000000) 1053 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_389 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (389 : ℕ) / 2)) - ((-1960513/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log (389 : ℕ) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (389 : ℕ) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8840629/20000000) (δ := 263399/10000000000) 1053 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_390 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (390 : ℕ) / 2)) - ((9145551/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log (390 : ℕ) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (390 : ℕ) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10409743/100000000) (δ := 32913/1250000000) 1053 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_391 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (391 : ℕ) / 2)) - ((5963327/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log (391 : ℕ) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (391 : ℕ) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23296787/100000000) (δ := 32913/1250000000) 1053 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_392 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (392 : ℕ) / 2)) - ((-3243649/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log (392 : ℕ) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (392 : ℕ) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 56917761/100000000) (δ := 263299/10000000000) 1053 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_393 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (393 : ℕ) / 2)) - ((-8885899/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log (393 : ℕ) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (393 : ℕ) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33313227/50000000) (δ := 263371/10000000000) 1053 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_394 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (394 : ℕ) / 2)) - ((1206633/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log (394 : ℕ) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (394 : ℕ) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33176593/100000000) (δ := 263271/10000000000) 1053 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_395 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (395 : ℕ) / 2)) - ((4999859/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log (395 : ℕ) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (395 : ℕ) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2933/1562500) (δ := 263271/10000000000) 1053 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_396 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (396 : ℕ) / 2)) - ((2299561/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log (396 : ℕ) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (396 : ℕ) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33469093/100000000) (δ := 65833/2500000000) 1053 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_397 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (397 : ℕ) / 2)) - ((-4446473/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log (397 : ℕ) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (397 : ℕ) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33332459/50000000) (δ := 65833/2500000000) 1053 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_398 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (398 : ℕ) / 2)) - ((-6603041/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log (398 : ℕ) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (398 : ℕ) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57300497/100000000) (δ := 13163/500000000) 1053 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_399 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (399 : ℕ) / 2)) - ((5646223/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log (399 : ℕ) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (399 : ℕ) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24270519/100000000) (δ := 263443/10000000000) 1053 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_400 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (400 : ℕ) / 2)) - ((9403763/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log (400 : ℕ) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (400 : ℕ) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4338267/50000000) (δ := 823/31250000) 1053 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_401 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (401 : ℕ) / 2)) - ((-907579/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log (401 : ℕ) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (401 : ℕ) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 41541981/100000000) (δ := 263443/10000000000) 1053 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_402 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (402 : ℕ) / 2)) - ((-4929093/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log (402 : ℕ) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (402 : ℕ) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 74324503/100000000) (δ := 13163/500000000) 1053 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_403 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (403 : ℕ) / 2)) - ((-4180699/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log (403 : ℕ) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (403 : ℕ) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25026449/50000000) (δ := 52683/2000000000) 1053 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_404 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (404 : ℕ) / 2)) - ((3832923/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log (404 : ℕ) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (404 : ℕ) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -697291/4000000) (δ := 65847/2500000000) 1053 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_405 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (405 : ℕ) / 2)) - ((8228873/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log (405 : ℕ) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (405 : ℕ) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7554029/50000000) (δ := 52663/2000000000) 1053 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_406 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (406 : ℕ) / 2)) - ((-162933/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log (406 : ℕ) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (406 : ℕ) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 47568099/100000000) (δ := 32911/1250000000) 1053 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_407 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (407 : ℕ) / 2)) - ((-624009/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log (407 : ℕ) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (407 : ℕ) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9641473/12500000) (δ := 32927/1250000000) 1053 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_408 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (408 : ℕ) / 2)) - ((-2206141/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log (408 : ℕ) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (408 : ℕ) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44831009/100000000) (δ := 32927/1250000000) 1053 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_409 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (409 : ℕ) / 2)) - ((8754799/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log (409 : ℕ) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (409 : ℕ) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12609209/100000000) (δ := 32927/1250000000) 1053 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_410 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (410 : ℕ) / 2)) - ((887459/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log (410 : ℕ) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (410 : ℕ) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1220851/6250000) (δ := 32927/1250000000) 1053 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_411 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (411 : ℕ) / 2)) - ((-4734073/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log (411 : ℕ) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (411 : ℕ) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51598783/100000000) (δ := 263387/10000000000) 1053 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_412 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (412 : ℕ) / 2)) - ((-9797061/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log (412 : ℕ) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (412 : ℕ) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73494659/100000000) (δ := 52669/2000000000) 1053 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_413 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (413 : ℕ) / 2)) - ((-462581/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log (413 : ℕ) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (413 : ℕ) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20793063/50000000) (δ := 131679/5000000000) 1053 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_414 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (414 : ℕ) / 2)) - ((2312123/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log (414 : ℕ) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (414 : ℕ) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -609621/6250000) (δ := 131679/5000000000) 1053 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_415 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (415 : ℕ) / 2)) - ((3185461/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log (415 : ℕ) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (415 : ℕ) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22001911/100000000) (δ := 52669/2000000000) 1053 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_416 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (416 : ℕ) / 2)) - ((-1362539/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log (416 : ℕ) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (416 : ℕ) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 536801/1000000) (δ := 131629/5000000000) 1053 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_417 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (417 : ℕ) / 2)) - ((-1204801/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log (417 : ℕ) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (417 : ℕ) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7179637/10000000) (δ := 26333/1000000000) 1053 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_418 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (418 : ℕ) / 2)) - ((-1599/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log (418 : ℕ) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (418 : ℕ) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -805391/2000000) (δ := 26333/1000000000) 1053 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_419 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (419 : ℕ) / 2)) - ((9384399/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log (419 : ℕ) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (419 : ℕ) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2204439/25000000) (δ := 26343/1000000000) 1053 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_420 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (420 : ℕ) / 2)) - ((774699/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log (420 : ℕ) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (420 : ℕ) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22559011/100000000) (δ := 263273/10000000000) 1053 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_421 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (421 : ℕ) / 2)) - ((-2755299/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log (421 : ℕ) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (421 : ℕ) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3366297/6250000) (δ := 263373/10000000000) 1053 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_422 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (422 : ℕ) / 2)) - ((-4829423/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log (422 : ℕ) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (422 : ℕ) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -71990849/100000000) (δ := 131651/5000000000) 1053 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_423 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (423 : ℕ) / 2)) - ((-626763/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log (423 : ℕ) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (423 : ℕ) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10209461/25000000) (δ := 131651/5000000000) 1053 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_424 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (424 : ℕ) / 2)) - ((924799/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log (424 : ℕ) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (424 : ℕ) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9757233/100000000) (δ := 263301/10000000000) 1053 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_425 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (425 : ℕ) / 2)) - ((6599931/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log (425 : ℕ) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (425 : ℕ) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5312417/25000000) (δ := 263401/10000000000) 1053 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_426 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (426 : ℕ) / 2)) - ((-1234753/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log (426 : ℕ) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (426 : ℕ) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3261511/6250000) (δ := 131651/5000000000) 1053 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_427 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (427 : ℕ) / 2)) - ((-9837973/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log (427 : ℕ) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (427 : ℕ) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74033343/100000000) (δ := 131637/5000000000) 1053 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_428 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (428 : ℕ) / 2)) - ((-1583321/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log (428 : ℕ) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (428 : ℕ) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -43244939/100000000) (δ := 131687/5000000000) 1053 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_429 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (429 : ℕ) / 2)) - ((4385389/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log (429 : ℕ) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (429 : ℕ) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12526297/100000000) (δ := 263329/10000000000) 1053 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_430 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (430 : ℕ) / 2)) - ((7486333/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log (430 : ℕ) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (430 : ℕ) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1132497/6250000) (δ := 131637/5000000000) 1053 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_431 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (431 : ℕ) / 2)) - ((-3680919/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log (431 : ℕ) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (431 : ℕ) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48693807/100000000) (δ := 131637/5000000000) 1053 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_432 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (432 : ℕ) / 2)) - ((-1249567/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log (432 : ℕ) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (432 : ℕ) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19470433/25000000) (δ := 263257/10000000000) 1053 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_433 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (433 : ℕ) / 2)) - ((-1606489/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log (433 : ℕ) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (433 : ℕ) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -47447399/100000000) (δ := 131723/5000000000) 1053 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_434 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (434 : ℕ) / 2)) - ((193863/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log (434 : ℕ) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (434 : ℕ) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1067759/6250000) (δ := 131723/5000000000) 1053 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_435 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (435 : ℕ) / 2)) - ((8636279/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log (435 : ℕ) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (435 : ℕ) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13209349/100000000) (δ := 263357/10000000000) 1053 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_436 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (436 : ℕ) / 2)) - ((-103599/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log (436 : ℕ) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (436 : ℕ) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21716541/50000000) (δ := 131673/5000000000) 1053 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_437 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (437 : ℕ) / 2)) - ((-4902201/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log (437 : ℕ) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (437 : ℕ) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73587053/100000000) (δ := 263257/10000000000) 1053 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_438 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (438 : ℕ) / 2)) - ((-669727/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log (438 : ℕ) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (438 : ℕ) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53405737/100000000) (δ := 263317/10000000000) 1053 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_439 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (439 : ℕ) / 2)) - ((1483447/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log (439 : ℕ) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (439 : ℕ) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1461791/6250000) (δ := 131643/5000000000) 1053 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_440 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (440 : ℕ) / 2)) - ((1207213/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log (440 : ℕ) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (440 : ℕ) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 327999/5000000) (δ := 131693/5000000000) 1053 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_441 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (441 : ℕ) / 2)) - ((1129479/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log (441 : ℕ) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (441 : ℕ) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9110043/25000000) (δ := 263417/10000000000) 1053 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_442 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (442 : ℕ) / 2)) - ((-8816433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log (442 : ℕ) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (442 : ℕ) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33126617/50000000) (δ := 131643/5000000000) 1053 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_443 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (443 : ℕ) / 2)) - ((-3829443/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log (443 : ℕ) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (443 : ℕ) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12216093/20000000) (δ := 131657/5000000000) 1053 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_444 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (444 : ℕ) / 2)) - ((3095597/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log (444 : ℕ) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (444 : ℕ) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1570083/5000000) (δ := 131657/5000000000) 1053 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_445 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (445 : ℕ) / 2)) - ((9974379/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log (445 : ℕ) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (445 : ℕ) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55937/3125000) (δ := 131707/5000000000) 1053 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_446 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (446 : ℕ) / 2)) - ((1111127/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log (446 : ℕ) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (446 : ℕ) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 693897/2500000) (δ := 131657/5000000000) 1053 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_447 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (447 : ℕ) / 2)) - ((-6583227/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log (447 : ℕ) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (447 : ℕ) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11446923/20000000) (δ := 131657/5000000000) 1053 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_448 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (448 : ℕ) / 2)) - ((-592409/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log (448 : ℕ) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (448 : ℕ) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70430779/100000000) (δ := 131671/5000000000) 1053 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_449 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (449 : ℕ) / 2)) - ((-181217/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log (449 : ℕ) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (449 : ℕ) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41083669/100000000) (δ := 131671/5000000000) 1053 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_450 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (450 : ℕ) / 2)) - ((1781283/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log (450 : ℕ) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (450 : ℕ) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2360211/20000000) (δ := 263261/10000000000) 1053 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_451 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (451 : ℕ) / 2)) - ((958719/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log (451 : ℕ) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (451 : ℕ) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8708531/50000000) (δ := 131721/5000000000) 1053 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_452 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (452 : ℕ) / 2)) - ((-1439237/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log (452 : ℕ) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (452 : ℕ) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46569367/100000000) (δ := 131721/5000000000) 1053 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_453 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (453 : ℕ) / 2)) - ((-9933657/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log (453 : ℕ) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (453 : ℕ) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18914623/25000000) (δ := 131721/5000000000) 1053 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_454 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (454 : ℕ) / 2)) - ((-5013141/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log (454 : ℕ) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (454 : ℕ) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13099457/25000000) (δ := 26337/1000000000) 1053 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_455 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (455 : ℕ) / 2)) - ((1479603/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log (455 : ℕ) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (455 : ℕ) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23436379/100000000) (δ := 26327/1000000000) 1053 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_456 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (456 : ℕ) / 2)) - ((2440601/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log (456 : ℕ) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (456 : ℕ) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2730287/50000000) (δ := 263433/10000000000) 1053 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_457 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (457 : ℕ) / 2)) - ((494407/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log (457 : ℕ) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (457 : ℕ) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3429303/10000000) (δ := 263333/10000000000) 1053 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_458 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (458 : ℕ) / 2)) - ((-4072157/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log (458 : ℕ) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (458 : ℕ) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31531811/50000000) (δ := 26337/1000000000) 1053 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_459 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (459 : ℕ) / 2)) - ((-21579/25000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log (459 : ℕ) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (459 : ℕ) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32653641/50000000) (δ := 131699/5000000000) 1053 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_460 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (460 : ℕ) / 2)) - ((208171/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log (460 : ℕ) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (460 : ℕ) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36663049/100000000) (δ := 52661/2000000000) 1053 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_461 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (461 : ℕ) / 2)) - ((118529/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log (461 : ℕ) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (461 : ℕ) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2019841/25000000) (δ := 52661/2000000000) 1053 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_462 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (462 : ℕ) / 2)) - ((6839407/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log (462 : ℕ) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (462 : ℕ) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20441141/100000000) (δ := 52661/2000000000) 1053 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_463 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (463 : ℕ) / 2)) - ((-1878943/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log (463 : ℕ) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (463 : ℕ) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24450549/50000000) (δ := 131699/5000000000) 1053 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_464 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (464 : ℕ) / 2)) - ((-9987689/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log (464 : ℕ) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (464 : ℕ) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9662399/12500000) (δ := 131649/5000000000) 1053 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_465 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (465 : ℕ) / 2)) - ((-292441/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log (465 : ℕ) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (465 : ℕ) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25721447/50000000) (δ := 16461/625000000) 1053 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_466 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (466 : ℕ) / 2)) - ((6004853/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log (466 : ℕ) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (466 : ℕ) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5791803/25000000) (δ := 263327/10000000000) 1053 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_467 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (467 : ℕ) / 2)) - ((9796839/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log (467 : ℕ) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (467 : ℕ) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5047923/100000000) (δ := 263327/10000000000) 1053 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_468 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (468 : ℕ) / 2)) - ((600801/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log (468 : ℕ) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (468 : ℕ) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33202511/100000000) (δ := 16461/625000000) 1053 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_469 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (469 : ℕ) / 2)) - ((-771451/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log (469 : ℕ) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (469 : ℕ) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61297867/100000000) (δ := 65819/2500000000) 1053 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_470 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (470 : ℕ) / 2)) - ((-9082497/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log (470 : ℕ) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (470 : ℕ) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67746957/100000000) (δ := 52651/2000000000) 1053 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_471 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (471 : ℕ) / 2)) - ((-8023/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log (471 : ℕ) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (471 : ℕ) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39771379/100000000) (δ := 32931/1250000000) 1053 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_472 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (472 : ℕ) / 2)) - ((8896577/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log (472 : ℕ) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (472 : ℕ) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11855033/100000000) (δ := 65837/2500000000) 1053 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_473 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (473 : ℕ) / 2)) - ((401023/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log (473 : ℕ) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (473 : ℕ) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8001041/50000000) (δ := 65837/2500000000) 1053 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_474 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (474 : ℕ) / 2)) - ((-1802641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log (474 : ℕ) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (474 : ℕ) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21900641/50000000) (δ := 65837/2500000000) 1053 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_475 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (475 : ℕ) / 2)) - ((-9610713/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log (475 : ℕ) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (475 : ℕ) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 71541251/100000000) (δ := 32931/1250000000) 1053 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_476 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (476 : ℕ) / 2)) - ((-3384377/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log (476 : ℕ) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (476 : ℕ) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11571529/20000000) (δ := 263383/10000000000) 1053 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_477 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (477 : ℕ) / 2)) - ((1767937/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log (477 : ℕ) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (477 : ℕ) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15117411/50000000) (δ := 6583/250000000) 1053 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_478 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (478 : ℕ) / 2)) - ((9943083/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log (478 : ℕ) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (478 : ℕ) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1334299/50000000) (δ := 13171/500000000) 1053 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_479 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (479 : ℕ) / 2)) - ((682163/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log (479 : ℕ) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (479 : ℕ) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12419197/50000000) (δ := 263283/10000000000) 1053 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_480 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (480 : ℕ) / 2)) - ((-497581/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log (480 : ℕ) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (480 : ℕ) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6536263/12500000) (δ := 263283/10000000000) 1053 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_481 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (481 : ℕ) / 2)) - ((-1997911/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log (481 : ℕ) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (481 : ℕ) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1547941/2000000) (δ := 263311/10000000000) 1053 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_482 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (482 : ℕ) / 2)) - ((-2091613/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log (482 : ℕ) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (482 : ℕ) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25029927/50000000) (δ := 263411/10000000000) 1053 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_483 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (483 : ℕ) / 2)) - ((3063899/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log (483 : ℕ) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (483 : ℕ) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5695143/25000000) (δ := 8231/312500000) 1053 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_484 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (484 : ℕ) / 2)) - ((9842463/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log (484 : ℕ) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (484 : ℕ) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2221713/50000000) (δ := 263411/10000000000) 1053 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_485 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (485 : ℕ) / 2)) - ((603287/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log (485 : ℕ) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (485 : ℕ) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3160951/10000000) (δ := 263311/10000000000) 1053 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_486 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (486 : ℕ) / 2)) - ((-1754763/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log (486 : ℕ) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (486 : ℕ) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14680407/25000000) (δ := 8231/312500000) 1053 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_487 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (487 : ℕ) / 2)) - ((-9583887/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log (487 : ℕ) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (487 : ℕ) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35651243/50000000) (δ := 65841/2500000000) 1053 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_488 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (488 : ℕ) / 2)) - ((-1999371/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log (488 : ℕ) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (488 : ℕ) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -177209/400000) (δ := 8227/312500000) 1053 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_489 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (489 : ℕ) / 2)) - ((7684733/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log (489 : ℕ) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (489 : ℕ) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17358613/100000000) (δ := 263439/10000000000) 1053 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_490 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (490 : ℕ) / 2)) - ((9282031/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log (490 : ℕ) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (490 : ℕ) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9531059/100000000) (δ := 65841/2500000000) 1053 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_491 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (491 : ℕ) / 2)) - ((1158649/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log (491 : ℕ) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (491 : ℕ) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9091691/25000000) (δ := 65841/2500000000) 1053 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_492 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (492 : ℕ) / 2)) - ((-510229/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log (492 : ℕ) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (492 : ℕ) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31573593/50000000) (δ := 263339/10000000000) 1053 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_493 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (493 : ℕ) / 2)) - ((-4495033/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log (493 : ℕ) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (493 : ℕ) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33603653/50000000) (δ := 52687/2000000000) 1053 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_494 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (494 : ℕ) / 2)) - ((-505747/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log (494 : ℕ) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (494 : ℕ) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1266713/3125000) (δ := 52687/2000000000) 1053 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_495 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (495 : ℕ) / 2)) - ((8490011/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log (495 : ℕ) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (495 : ℕ) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13917609/100000000) (δ := 65817/2500000000) 1053 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_496 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (496 : ℕ) / 2)) - ((4373747/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log (496 : ℕ) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (496 : ℕ) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12646949/100000000) (δ := 52687/2000000000) 1053 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_497 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (497 : ℕ) / 2)) - ((44947/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log (497 : ℕ) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (497 : ℕ) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1957877/5000000) (δ := 52667/2000000000) 1053 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_498 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (498 : ℕ) / 2)) - ((-869293/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log (498 : ℕ) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (498 : ℕ) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13122833/20000000) (δ := 52667/2000000000) 1053 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_499 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (499 : ℕ) / 2)) - ((-8581541/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log (499 : ℕ) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (499 : ℕ) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65061493/100000000) (δ := 2057/78125000) 1053 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_500 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (500 : ℕ) / 2)) - ((223877/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log (500 : ℕ) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (500 : ℕ) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4838771/12500000) (δ := 2057/78125000) 1053 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_501 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (501 : ℕ) / 2)) - ((4396497/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62166061/20000000 : ℚ) : ℝ) ≤ Real.log (501 : ℕ) / 2 := by
    have h := (log_br_501).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (501 : ℕ) / 2 ≤ ((31083031/10000000 : ℚ) : ℝ) := by
    have h := (log_br_501).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12410177/100000000) (δ := 65849/2500000000) 1053 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_502 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (502 : ℕ) / 2)) - ((4253623/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62186001/20000000 : ℚ) : ℝ) ≤ Real.log (502 : ℕ) / 2 := by
    have h := (log_br_502).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (502 : ℕ) / 2 ≤ ((31093001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_502).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1729481/12500000) (δ := 65849/2500000000) 1053 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_503 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (503 : ℕ) / 2)) - ((-303679/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62205901/20000000 : ℚ) : ℝ) ≤ Real.log (503 : ℕ) / 2 := by
    have h := (log_br_503).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (503 : ℕ) / 2 ≤ ((31102951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_503).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40029223/100000000) (δ := 65849/2500000000) 1053 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_504 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (504 : ℕ) / 2)) - ((-550057/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31112881/10000000 : ℚ) : ℝ) ≤ Real.log (504 : ℕ) / 2 := by
    have h := (log_br_504).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (504 : ℕ) / 2 ≤ ((62225763/20000000 : ℚ) : ℝ) := by
    have h := (log_br_504).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13234253/20000000) (δ := 263407/10000000000) 1053 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_505 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (505 : ℕ) / 2)) - ((-4265531/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3890349/1250000 : ℚ) : ℝ) ≤ Real.log (505 : ℕ) / 2 := by
    have h := (log_br_505).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (505 : ℕ) / 2 ≤ ((12449117/4000000 : ℚ) : ℝ) := by
    have h := (log_br_505).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -64817661/100000000) (δ := 1029/39062500) 1053 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_506 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (506 : ℕ) / 2)) - ((196109/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31132683/10000000 : ℚ) : ℝ) ≤ Real.log (506 : ℕ) / 2 := by
    have h := (log_br_506).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (506 : ℕ) / 2 ≤ ((62265367/20000000 : ℚ) : ℝ) := by
    have h := (log_br_506).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38779603/100000000) (δ := 263279/10000000000) 1053 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_507 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (507 : ℕ) / 2)) - ((8719317/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6228511/2000000 : ℚ) : ℝ) ≤ Real.log (507 : ℕ) / 2 := by
    have h := (log_br_507).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (507 : ℕ) / 2 ≤ ((62285111/20000000 : ℚ) : ℝ) := by
    have h := (log_br_507).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12791563/100000000) (δ := 263279/10000000000) 1053 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_508 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (508 : ℕ) / 2)) - ((4324731/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31152407/10000000 : ℚ) : ℝ) ≤ Real.log (508 : ℕ) / 2 := by
    have h := (log_br_508).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (508 : ℕ) / 2 ≤ ((12460963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_508).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13143827/100000000) (δ := 263279/10000000000) 1053 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_509 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (509 : ℕ) / 2)) - ((48141/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48691/15625 : ℚ) : ℝ) ≤ Real.log (509 : ℕ) / 2 := by
    have h := (log_br_509).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (509 : ℕ) / 2 ≤ ((62324481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_509).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39029199/100000000) (δ := 1029/39062500) 1053 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_510 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (510 : ℕ) / 2)) - ((-8540559/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62344107/20000000 : ℚ) : ℝ) ≤ Real.log (510 : ℕ) / 2 := by
    have h := (log_br_510).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (510 : ℕ) / 2 ≤ ((15586027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_510).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32431619/50000000) (δ := 65831/2500000000) 1053 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_511 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (511 : ℕ) / 2)) - ((-4425133/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12472739/4000000 : ℚ) : ℝ) ≤ Real.log (511 : ℕ) / 2 := by
    have h := (log_br_511).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (511 : ℕ) / 2 ≤ ((3897731/1250000 : ℚ) : ℝ) := by
    have h := (log_br_511).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66433689/100000000) (δ := 263451/10000000000) 1053 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_512 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (512 : ℕ) / 2)) - ((-571599/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31191623/10000000 : ℚ) : ℝ) ≤ Real.log (512 : ℕ) / 2 := by
    have h := (log_br_512).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (512 : ℕ) / 2 ≤ ((62383247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_512).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20349843/50000000) (δ := 32919/1250000000) 1053 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_513 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (513 : ℕ) / 2)) - ((8249511/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31201379/10000000 : ℚ) : ℝ) ≤ Real.log (513 : ℕ) / 2 := by
    have h := (log_br_513).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (513 : ℕ) / 2 ≤ ((62402759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_513).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1877127/12500000) (δ := 32919/1250000000) 1053 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_514 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (514 : ℕ) / 2)) - ((9111931/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7802779/2500000 : ℚ) : ℝ) ≤ Real.log (514 : ℕ) / 2 := by
    have h := (log_br_514).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (514 : ℕ) / 2 ≤ ((62422233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_514).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10615637/100000000) (δ := 263351/10000000000) 1053 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_515 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (515 : ℕ) / 2)) - ((1225043/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62441669/20000000 : ℚ) : ℝ) ≤ Real.log (515 : ℕ) / 2 := by
    have h := (log_br_515).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (515 : ℕ) / 2 ≤ ((6244167/2000000 : ℚ) : ℝ) := by
    have h := (log_br_515).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9049897/25000000) (δ := 65813/2500000000) 1053 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_516 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (516 : ℕ) / 2)) - ((-3911943/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62461067/20000000 : ℚ) : ℝ) ≤ Real.log (516 : ℕ) / 2 := by
    have h := (log_br_516).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (516 : ℕ) / 2 ≤ ((15615267/5000000 : ℚ) : ℝ) := by
    have h := (log_br_516).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30866103/50000000) (δ := 263451/10000000000) 1053 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_517 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (517 : ℕ) / 2)) - ((-4701897/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15620107/5000000 : ℚ) : ℝ) ≤ Real.log (517 : ℕ) / 2 := by
    have h := (log_br_517).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (517 : ℕ) / 2 ≤ ((62480429/20000000 : ℚ) : ℝ) := by
    have h := (log_br_517).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69863511/100000000) (δ := 3291/125000000) 1053 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_518 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (518 : ℕ) / 2)) - ((-409749/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7812469/2500000 : ℚ) : ℝ) ≤ Real.log (518 : ℕ) / 2 := by
    have h := (log_br_518).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (518 : ℕ) / 2 ≤ ((62499753/20000000 : ℚ) : ℝ) := by
    have h := (log_br_518).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5553537/12500000) (δ := 3291/125000000) 1053 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_519 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (519 : ℕ) / 2)) - ((7236473/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31259519/10000000 : ℚ) : ℝ) ≤ Real.log (519 : ℕ) / 2 := by
    have h := (log_br_519).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (519 : ℕ) / 2 ≤ ((62519039/20000000 : ℚ) : ℝ) := by
    have h := (log_br_519).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9521549/50000000) (δ := 263423/10000000000) 1053 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_520 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (520 : ℕ) / 2)) - ((2421171/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3908643/1250000 : ℚ) : ℝ) ≤ Real.log (520 : ℕ) / 2 := by
    have h := (log_br_520).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (520 : ℕ) / 2 ≤ ((62538289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_520).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3147357/50000000) (δ := 3291/125000000) 1053 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_521 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (521 : ℕ) / 2)) - ((302673/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25023/8000 : ℚ) : ℝ) ≤ Real.log (521 : ℕ) / 2 := by
    have h := (log_br_521).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (521 : ℕ) / 2 ≤ ((62557501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_521).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31582509/100000000) (δ := 3291/125000000) 1053 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_522 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (522 : ℕ) / 2)) - ((-3228989/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2503067/800000 : ℚ) : ℝ) ≤ Real.log (522 : ℕ) / 2 := by
    have h := (log_br_522).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (522 : ℕ) / 2 ≤ ((15644169/5000000 : ℚ) : ℝ) := by
    have h := (log_br_522).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 56821603/100000000) (δ := 263323/10000000000) 1053 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_523 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (523 : ℕ) / 2)) - ((-4951817/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31297907/10000000 : ℚ) : ℝ) ≤ Real.log (523 : ℕ) / 2 := by
    have h := (log_br_523).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (523 : ℕ) / 2 ≤ ((12519163/4000000 : ℚ) : ℝ) := by
    have h := (log_br_523).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75066321/100000000) (δ := 131647/5000000000) 1053 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_524 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (524 : ℕ) / 2)) - ((-4133557/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15653729/5000000 : ℚ) : ℝ) ≤ Real.log (524 : ℕ) / 2 := by
    have h := (log_br_524).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (524 : ℕ) / 2 ≤ ((62614917/20000000 : ℚ) : ℝ) := by
    have h := (log_br_524).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24961657/50000000) (δ := 263409/10000000000) 1053 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_525 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (525 : ℕ) / 2)) - ((5460891/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31316991/10000000 : ℚ) : ℝ) ≤ Real.log (525 : ℕ) / 2 := by
    have h := (log_br_525).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (525 : ℕ) / 2 ≤ ((62633983/20000000 : ℚ) : ℝ) := by
    have h := (log_br_525).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24827691/100000000) (δ := 131647/5000000000) 1053 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_526 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (526 : ℕ) / 2)) - ((9999611/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15663253/5000000 : ℚ) : ℝ) ≤ Real.log (526 : ℕ) / 2 := by
    have h := (log_br_526).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (526 : ℕ) / 2 ≤ ((62653013/20000000 : ℚ) : ℝ) := by
    have h := (log_br_526).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 110273/50000000) (δ := 263409/10000000000) 1053 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_527 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (527 : ℕ) / 2)) - ((5328737/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12534401/4000000 : ℚ) : ℝ) ≤ Real.log (527 : ℕ) / 2 := by
    have h := (log_br_527).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (527 : ℕ) / 2 ≤ ((31336003/10000000 : ℚ) : ℝ) := by
    have h := (log_br_527).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25220083/100000000) (δ := 131697/5000000000) 1053 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_528 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (528 : ℕ) / 2)) - ((-2112007/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31345481/10000000 : ℚ) : ℝ) ≤ Real.log (528 : ℕ) / 2 := by
    have h := (log_br_528).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (528 : ℕ) / 2 ≤ ((62690963/20000000 : ℚ) : ℝ) := by
    have h := (log_br_528).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25086117/50000000) (δ := 131647/5000000000) 1053 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_529 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (529 : ℕ) / 2)) - ((-9904297/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/5000000 : ℚ) : ℝ) ≤ Real.log (529 : ℕ) / 2 := by
    have h := (log_br_529).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (529 : ℕ) / 2 ≤ ((12541977/4000000 : ℚ) : ℝ) := by
    have h := (log_br_529).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18769579/25000000) (δ := 263409/10000000000) 1053 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_530 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (530 : ℕ) / 2)) - ((-6555483/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6272877/2000000 : ℚ) : ℝ) ≤ Real.log (530 : ℕ) / 2 := by
    have h := (log_br_530).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (530 : ℕ) / 2 ≤ ((62728771/20000000 : ℚ) : ℝ) := by
    have h := (log_br_530).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57142619/100000000) (δ := 263337/10000000000) 1053 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_531 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (531 : ℕ) / 2)) - ((547989/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3137381/1000000 : ℚ) : ℝ) ≤ Real.log (531 : ℕ) / 2 := by
    have h := (log_br_531).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (531 : ℕ) / 2 ≤ ((62747621/20000000 : ℚ) : ℝ) := by
    have h := (log_br_531).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16165653/50000000) (δ := 131683/5000000000) 1053 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_532 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (532 : ℕ) / 2)) - ((1909073/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31383217/10000000 : ℚ) : ℝ) ≤ Real.log (532 : ℕ) / 2 := by
    have h := (log_br_532).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (532 : ℕ) / 2 ≤ ((12553287/4000000 : ℚ) : ℝ) := by
    have h := (log_br_532).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7567379/100000000) (δ := 263337/10000000000) 1053 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_533 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (533 : ℕ) / 2)) - ((1547481/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31392607/10000000 : ℚ) : ℝ) ≤ Real.log (533 : ℕ) / 2 := by
    have h := (log_br_533).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (533 : ℕ) / 2 ≤ ((12557043/4000000 : ℚ) : ℝ) := by
    have h := (log_br_533).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4287949/25000000) (δ := 263337/10000000000) 1053 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_534 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (534 : ℕ) / 2)) - ((-63731/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31401979/10000000 : ℚ) : ℝ) ≤ Real.log (534 : ℕ) / 2 := by
    have h := (log_br_534).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (534 : ℕ) / 2 ≤ ((62803959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_534).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20911793/50000000) (δ := 263337/10000000000) 1053 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_535 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (535 : ℕ) / 2)) - ((-8853173/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62822667/20000000 : ℚ) : ℝ) ≤ Real.log (535 : ℕ) / 2 := by
    have h := (log_br_535).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (535 : ℕ) / 2 ≤ ((15705667/5000000 : ℚ) : ℝ) := by
    have h := (log_br_535).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66449307/100000000) (δ := 263437/10000000000) 1053 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_536 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (536 : ℕ) / 2)) - ((-8777907/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62841341/20000000 : ℚ) : ℝ) ≤ Real.log (536 : ℕ) / 2 := by
    have h := (log_br_536).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (536 : ℕ) / 2 ≤ ((31420671/10000000 : ℚ) : ℝ) := by
    have h := (log_br_536).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66050673/100000000) (δ := 52673/2000000000) 1053 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_537 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (537 : ℕ) / 2)) - ((-448831/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3142999/1000000 : ℚ) : ℝ) ≤ Real.log (537 : ℕ) / 2 := by
    have h := (log_br_537).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (537 : ℕ) / 2 ≤ ((62859981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_537).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41517089/100000000) (δ := 52653/2000000000) 1053 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_538 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (538 : ℕ) / 2)) - ((1553723/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12575717/4000000 : ℚ) : ℝ) ≤ Real.log (538 : ℕ) / 2 := by
    have h := (log_br_538).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (538 : ℕ) / 2 ≤ ((31439293/10000000 : ℚ) : ℝ) := by
    have h := (log_br_538).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8514129/50000000) (δ := 52673/2000000000) 1053 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_539 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (539 : ℕ) / 2)) - ((1912683/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12579431/4000000 : ℚ) : ℝ) ≤ Real.log (539 : ℕ) / 2 := by
    have h := (log_br_539).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (539 : ℕ) / 2 ≤ ((15724289/5000000 : ℚ) : ℝ) := by
    have h := (log_br_539).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1482901/20000000) (δ := 131669/5000000000) 1053 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_540 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (540 : ℕ) / 2)) - ((734729/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62915691/20000000 : ℚ) : ℝ) ≤ Real.log (540 : ℕ) / 2 := by
    have h := (log_br_540).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (540 : ℕ) / 2 ≤ ((15728923/5000000 : ℚ) : ℝ) := by
    have h := (log_br_540).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6362503/20000000) (δ := 131669/5000000000) 1053 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_541 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (541 : ℕ) / 2)) - ((-1563769/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3933387/1250000 : ℚ) : ℝ) ≤ Real.log (541 : ℕ) / 2 := by
    have h := (log_br_541).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (541 : ℕ) / 2 ≤ ((62934193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_541).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7020557/12500000) (δ := 52653/2000000000) 1053 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_542 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (542 : ℕ) / 2)) - ((-9970119/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3147633/1000000 : ℚ) : ℝ) ≤ Real.log (542 : ℕ) / 2 := by
    have h := (log_br_542).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (542 : ℕ) / 2 ≤ ((62952661/20000000 : ℚ) : ℝ) := by
    have h := (log_br_542).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4787917/6250000) (δ := 263393/10000000000) 1053 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_543 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (543 : ℕ) / 2)) - ((-249729/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62971093/20000000 : ℚ) : ℝ) ≤ Real.log (543 : ℕ) / 2 := by
    have h := (log_br_543).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (543 : ℕ) / 2 ≤ ((31485547/10000000 : ℚ) : ℝ) := by
    have h := (log_br_543).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10468847/20000000) (δ := 26341/1000000000) 1053 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_544 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (544 : ℕ) / 2)) - ((862241/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15747373/5000000 : ℚ) : ℝ) ≤ Real.log (544 : ℕ) / 2 := by
    have h := (log_br_544).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (544 : ℕ) / 2 ≤ ((62989493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_544).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3515819/12500000) (δ := 263393/10000000000) 1053 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_545 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (545 : ℕ) / 2)) - ((2468803/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63007857/20000000 : ℚ) : ℝ) ≤ Real.log (545 : ℕ) / 2 := by
    have h := (log_br_545).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (545 : ℕ) / 2 ≤ ((31503929/10000000 : ℚ) : ℝ) := by
    have h := (log_br_545).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -197681/5000000) (δ := 26341/1000000000) 1053 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_546 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (546 : ℕ) / 2)) - ((6916429/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63026189/20000000 : ℚ) : ℝ) ≤ Real.log (546 : ℕ) / 2 := by
    have h := (log_br_546).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (546 : ℕ) / 2 ≤ ((6302619/2000000 : ℚ) : ℝ) := by
    have h := (log_br_546).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 161407/800000) (δ := 26341/1000000000) 1053 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_547 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (547 : ℕ) / 2)) - ((-1983567/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7880561/2500000 : ℚ) : ℝ) ≤ Real.log (547 : ℕ) / 2 := by
    have h := (log_br_547).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (547 : ℕ) / 2 ≤ ((63044489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_547).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44261933/100000000) (δ := 263393/10000000000) 1053 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_548 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (548 : ℕ) / 2)) - ((-9173137/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1970711/625000 : ℚ) : ℝ) ≤ Real.log (548 : ℕ) / 2 := by
    have h := (log_br_548).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (548 : ℕ) / 2 ≤ ((63062753/20000000 : ℚ) : ℝ) := by
    have h := (log_br_548).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 68301923/100000000) (δ := 263393/10000000000) 1053 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_549 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (549 : ℕ) / 2)) - ((-8523159/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7885123/2500000 : ℚ) : ℝ) ≤ Real.log (549 : ℕ) / 2 := by
    have h := (log_br_549).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (549 : ℕ) / 2 ≤ ((12616197/4000000 : ℚ) : ℝ) := by
    have h := (log_br_549).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -64779839/100000000) (δ := 131691/5000000000) 1053 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_550 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (550 : ℕ) / 2)) - ((-622323/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31549591/10000000 : ℚ) : ℝ) ≤ Real.log (550 : ℕ) / 2 := by
    have h := (log_br_550).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (550 : ℕ) / 2 ≤ ((63099183/20000000 : ℚ) : ℝ) := by
    have h := (log_br_550).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20413361/50000000) (δ := 263321/10000000000) 1053 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_551 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (551 : ℕ) / 2)) - ((97461/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15779337/5000000 : ℚ) : ℝ) ≤ Real.log (551 : ℕ) / 2 := by
    have h := (log_br_551).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (551 : ℕ) / 2 ≤ ((63117349/20000000 : ℚ) : ℝ) := by
    have h := (log_br_551).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4228931/25000000) (δ := 131691/5000000000) 1053 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_552 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (552 : ℕ) / 2)) - ((1923201/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1578387/500000 : ℚ) : ℝ) ≤ Real.log (552 : ℕ) / 2 := by
    have h := (log_br_552).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (552 : ℕ) / 2 ≤ ((63135481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_552).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6950521/100000000) (δ := 131691/5000000000) 1053 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_553 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (553 : ℕ) / 2)) - ((833271/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3157679/1000000 : ℚ) : ℝ) ≤ Real.log (553 : ℕ) / 2 := by
    have h := (log_br_553).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (553 : ℕ) / 2 ≤ ((63153581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_553).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15387323/50000000) (δ := 131691/5000000000) 1053 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_554 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (554 : ℕ) / 2)) - ((-1434963/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31585823/10000000 : ℚ) : ℝ) ≤ Real.log (554 : ℕ) / 2 := by
    have h := (log_br_554).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (554 : ℕ) / 2 ≤ ((63171647/20000000 : ℚ) : ℝ) := by
    have h := (log_br_554).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27277009/50000000) (δ := 263321/10000000000) 1053 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_555 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (555 : ℕ) / 2)) - ((-9999511/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63189681/20000000 : ℚ) : ℝ) ≤ Real.log (555 : ℕ) / 2 := by
    have h := (log_br_555).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (555 : ℕ) / 2 ≤ ((31594841/10000000 : ℚ) : ℝ) := by
    have h := (log_br_555).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 78292587/100000000) (δ := 131641/5000000000) 1053 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_556 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (556 : ℕ) / 2)) - ((-5915121/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31603841/10000000 : ℚ) : ℝ) ≤ Real.log (556 : ℕ) / 2 := by
    have h := (log_br_556).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (556 : ℕ) / 2 ≤ ((63207683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_556).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5509323/10000000) (δ := 5269/200000000) 1053 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_557 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (557 : ℕ) / 2)) - ((96279/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15806413/5000000 : ℚ) : ℝ) ≤ Real.log (557 : ℕ) / 2 := by
    have h := (log_br_557).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (557 : ℕ) / 2 ≤ ((63225653/20000000 : ℚ) : ℝ) := by
    have h := (log_br_557).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31440217/100000000) (δ := 263253/10000000000) 1053 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_558 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (558 : ℕ) / 2)) - ((4756723/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63243589/20000000 : ℚ) : ℝ) ≤ Real.log (558 : ℕ) / 2 := by
    have h := (log_br_558).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (558 : ℕ) / 2 ≤ ((6324359/2000000 : ℚ) : ℝ) := by
    have h := (log_br_558).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7830641/100000000) (δ := 5267/200000000) 1053 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_559 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (559 : ℕ) / 2)) - ((8083381/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31630747/10000000 : ℚ) : ℝ) ≤ Real.log (559 : ℕ) / 2 := by
    have h := (log_br_559).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (559 : ℕ) / 2 ≤ ((12652299/4000000 : ℚ) : ℝ) := by
    have h := (log_br_559).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3147363/20000000) (δ := 5269/200000000) 1053 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_560 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (560 : ℕ) / 2)) - ((1551/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63279367/20000000 : ℚ) : ℝ) ≤ Real.log (560 : ℕ) / 2 := by
    have h := (log_br_560).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (560 : ℕ) / 2 ≤ ((7909921/2500000 : ℚ) : ℝ) := by
    have h := (log_br_560).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4907769/12500000) (δ := 263353/10000000000) 1053 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_561 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (561 : ℕ) / 2)) - ((-8070099/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63297209/20000000 : ℚ) : ℝ) ≤ Real.log (561 : ℕ) / 2 := by
    have h := (log_br_561).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (561 : ℕ) / 2 ≤ ((6329721/2000000 : ℚ) : ℝ) := by
    have h := (log_br_561).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15686671/25000000) (δ := 5267/200000000) 1053 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_562 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (562 : ℕ) / 2)) - ((-9535707/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31657509/10000000 : ℚ) : ℝ) ≤ Real.log (562 : ℕ) / 2 := by
    have h := (log_br_562).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (562 : ℕ) / 2 ≤ ((63315019/20000000 : ℚ) : ℝ) := by
    have h := (log_br_562).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17722963/25000000) (δ := 10533/400000000) 1053 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_563 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (563 : ℕ) / 2)) - ((-3229701/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15833199/5000000 : ℚ) : ℝ) ≤ Real.log (563 : ℕ) / 2 := by
    have h := (log_br_563).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (563 : ℕ) / 2 ≤ ((63332797/20000000 : ℚ) : ℝ) := by
    have h := (log_br_563).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1187289/2500000) (δ := 131689/5000000000) 1053 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_564 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (564 : ℕ) / 2)) - ((5691411/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31675271/10000000 : ℚ) : ℝ) ≤ Real.log (564 : ℕ) / 2 := by
    have h := (log_br_564).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (564 : ℕ) / 2 ≤ ((63350543/20000000 : ℚ) : ℝ) := by
    have h := (log_br_564).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24133387/100000000) (δ := 10533/400000000) 1053 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_565 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (565 : ℕ) / 2)) - ((9994673/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63368257/20000000 : ℚ) : ℝ) ≤ Real.log (565 : ℕ) / 2 := by
    have h := (log_br_565).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (565 : ℕ) / 2 ≤ ((31684129/10000000 : ℚ) : ℝ) := by
    have h := (log_br_565).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -408009/50000000) (δ := 10537/400000000) 1053 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_566 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (566 : ℕ) / 2)) - ((3114433/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3169297/1000000 : ℚ) : ℝ) ≤ Real.log (566 : ℕ) / 2 := by
    have h := (log_br_566).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (566 : ℕ) / 2 ≤ ((63385941/20000000 : ℚ) : ℝ) := by
    have h := (log_br_566).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2245923/10000000) (δ := 131689/5000000000) 1053 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_567 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (567 : ℕ) / 2)) - ((-508367/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63403593/20000000 : ℚ) : ℝ) ≤ Real.log (567 : ℕ) / 2 := by
    have h := (log_br_567).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (567 : ℕ) / 2 ≤ ((31701797/10000000 : ℚ) : ℝ) := by
    have h := (log_br_567).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2855937/6250000) (δ := 10537/400000000) 1053 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_568 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (568 : ℕ) / 2)) - ((-4632023/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31710607/10000000 : ℚ) : ℝ) ≤ Real.log (568 : ℕ) / 2 := by
    have h := (log_br_568).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (568 : ℕ) / 2 ≤ ((12684243/4000000 : ℚ) : ℝ) := by
    have h := (log_br_568).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 68888633/100000000) (δ := 10533/400000000) 1053 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_569 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (569 : ℕ) / 2)) - ((-8576747/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15859701/5000000 : ℚ) : ℝ) ≤ Real.log (569 : ℕ) / 2 := by
    have h := (log_br_569).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (569 : ℕ) / 2 ≤ ((12687761/4000000 : ℚ) : ℝ) := by
    have h := (log_br_569).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32519081/50000000) (δ := 263397/10000000000) 1053 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_570 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (570 : ℕ) / 2)) - ((-106049/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63456363/20000000 : ℚ) : ℝ) ≤ Real.log (570 : ℕ) / 2 := by
    have h := (log_br_570).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (570 : ℕ) / 2 ≤ ((15864091/5000000 : ℚ) : ℝ) := by
    have h := (log_br_570).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41926129/100000000) (δ := 131703/5000000000) 1053 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_571 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (571 : ℕ) / 2)) - ((911073/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15868473/5000000 : ℚ) : ℝ) ≤ Real.log (571 : ℕ) / 2 := by
    have h := (log_br_571).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (571 : ℕ) / 2 ≤ ((63473893/20000000 : ℚ) : ℝ) := by
    have h := (log_br_571).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9426791/50000000) (δ := 263397/10000000000) 1053 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_572 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (572 : ℕ) / 2)) - ((2465189/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63491389/20000000 : ℚ) : ℝ) ≤ Real.log (572 : ℕ) / 2 := by
    have h := (log_br_572).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (572 : ℕ) / 2 ≤ ((6349139/2000000 : ℚ) : ℝ) := by
    have h := (log_br_572).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1044211/25000000) (δ := 263297/10000000000) 1053 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_573 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (573 : ℕ) / 2)) - ((4653521/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63508857/20000000 : ℚ) : ℝ) ≤ Real.log (573 : ℕ) / 2 := by
    have h := (log_br_573).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (573 : ℕ) / 2 ≤ ((31754429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_573).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27169099/100000000) (δ := 263297/10000000000) 1053 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_574 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (574 : ℕ) / 2)) - ((-4204789/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63526293/20000000 : ℚ) : ℝ) ≤ Real.log (574 : ℕ) / 2 := by
    have h := (log_br_574).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (574 : ℕ) / 2 ≤ ((31763147/10000000 : ℚ) : ℝ) := by
    have h := (log_br_574).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25059617/50000000) (δ := 263297/10000000000) 1053 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_575 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (575 : ℕ) / 2)) - ((-4879111/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((635437/200000 : ℚ) : ℝ) ≤ Real.log (575 : ℕ) / 2 := by
    have h := (log_br_575).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (575 : ℕ) / 2 ≤ ((63543701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_575).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36515599/50000000) (δ := 263397/10000000000) 1053 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_576 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (576 : ℕ) / 2)) - ((-7683727/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/5000000 : ℚ) : ℝ) ≤ Real.log (576 : ℕ) / 2 := by
    have h := (log_br_576).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (576 : ℕ) / 2 ≤ ((63561077/20000000 : ℚ) : ℝ) := by
    have h := (log_br_576).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2447091/4000000) (δ := 263269/10000000000) 1053 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_577 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (577 : ℕ) / 2)) - ((184819/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31789211/10000000 : ℚ) : ℝ) ≤ Real.log (577 : ℕ) / 2 := by
    have h := (log_br_577).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (577 : ℕ) / 2 ≤ ((63578423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_577).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38345603/100000000) (δ := 131717/5000000000) 1053 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_578 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (578 : ℕ) / 2)) - ((8126351/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31797869/10000000 : ℚ) : ℝ) ≤ Real.log (578 : ℕ) / 2 := by
    have h := (log_br_578).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (578 : ℕ) / 2 ≤ ((63595739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_578).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7776709/50000000) (δ := 131717/5000000000) 1053 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_579 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (579 : ℕ) / 2)) - ((479411/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1987907/625000 : ℚ) : ℝ) ≤ Real.log (579 : ℕ) / 2 := by
    have h := (log_br_579).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (579 : ℕ) / 2 ≤ ((2544521/800000 : ℚ) : ℝ) := by
    have h := (log_br_579).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 89991/1250000) (δ := 263269/10000000000) 1053 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_580 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (580 : ℕ) / 2)) - ((365569/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63630281/20000000 : ℚ) : ℝ) ≤ Real.log (580 : ℕ) / 2 := by
    have h := (log_br_580).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (580 : ℕ) / 2 ≤ ((31815141/10000000 : ℚ) : ℝ) := by
    have h := (log_br_580).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14956903/50000000) (δ := 131667/5000000000) 1053 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_581 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (581 : ℕ) / 2)) - ((-1269663/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63647507/20000000 : ℚ) : ℝ) ≤ Real.log (581 : ℕ) / 2 := by
    have h := (log_br_581).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (581 : ℕ) / 2 ≤ ((15911877/5000000 : ℚ) : ℝ) := by
    have h := (log_br_581).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52587529/100000000) (δ := 263369/10000000000) 1053 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_582 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (582 : ℕ) / 2)) - ((-9912123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((994761/312500 : ℚ) : ℝ) ≤ Real.log (582 : ℕ) / 2 := by
    have h := (log_br_582).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (582 : ℕ) / 2 ≤ ((12732941/4000000 : ℚ) : ℝ) := by
    have h := (log_br_582).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1880577/2500000) (δ := 263269/10000000000) 1053 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_583 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (583 : ℕ) / 2)) - ((-1434187/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63681871/20000000 : ℚ) : ℝ) ≤ Real.log (583 : ℕ) / 2 := by
    have h := (log_br_583).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (583 : ℕ) / 2 ≤ ((3980117/1250000 : ℚ) : ℝ) := by
    have h := (log_br_583).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59260489/100000000) (δ := 263263/10000000000) 1053 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_584 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (584 : ℕ) / 2)) - ((1025121/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63699009/20000000 : ℚ) : ℝ) ≤ Real.log (584 : ℕ) / 2 := by
    have h := (log_br_584).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (584 : ℕ) / 2 ≤ ((6369901/2000000 : ℚ) : ℝ) := by
    have h := (log_br_584).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9175649/25000000) (δ := 3293/125000000) 1053 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_585 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (585 : ℕ) / 2)) - ((8433469/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31858059/10000000 : ℚ) : ℝ) ≤ Real.log (585 : ℕ) / 2 := by
    have h := (log_br_585).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (585 : ℕ) / 2 ≤ ((63716119/20000000 : ℚ) : ℝ) := by
    have h := (log_br_585).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -113463/800000) (δ := 13167/500000000) 1053 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_586 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (586 : ℕ) / 2)) - ((2363567/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63733197/20000000 : ℚ) : ℝ) ≤ Real.log (586 : ℕ) / 2 := by
    have h := (log_br_586).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (586 : ℕ) / 2 ≤ ((31866599/10000000 : ℚ) : ℝ) := by
    have h := (log_br_586).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8297359/100000000) (δ := 3293/125000000) 1053 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_587 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (587 : ℕ) / 2)) - ((3345869/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7968781/2500000 : ℚ) : ℝ) ≤ Real.log (587 : ℕ) / 2 := by
    have h := (log_br_587).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (587 : ℕ) / 2 ≤ ((63750249/20000000 : ℚ) : ℝ) := by
    have h := (log_br_587).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30740737/100000000) (δ := 263363/10000000000) 1053 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_588 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (588 : ℕ) / 2)) - ((-2634669/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63767269/20000000 : ℚ) : ℝ) ≤ Real.log (588 : ℕ) / 2 := by
    have h := (log_br_588).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (588 : ℕ) / 2 ≤ ((6376727/2000000 : ℚ) : ℝ) := by
    have h := (log_br_588).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53144629/100000000) (δ := 3293/125000000) 1053 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_589 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (589 : ℕ) / 2)) - ((-2481667/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63784261/20000000 : ℚ) : ℝ) ≤ Real.log (589 : ℕ) / 2 := by
    have h := (log_br_589).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (589 : ℕ) / 2 ≤ ((31892131/10000000 : ℚ) : ℝ) := by
    have h := (log_br_589).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75510349/100000000) (δ := 3293/125000000) 1053 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_590 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (590 : ℕ) / 2)) - ((-3582669/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2552049/800000 : ℚ) : ℝ) ≤ Real.log (590 : ℕ) / 2 := by
    have h := (log_br_590).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (590 : ℕ) / 2 ≤ ((31900613/10000000 : ℚ) : ℝ) := by
    have h := (log_br_590).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59240419/100000000) (δ := 16457/625000000) 1053 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_591 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (591 : ℕ) / 2)) - ((463371/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((797727/250000 : ℚ) : ℝ) ≤ Real.log (591 : ℕ) / 2 := by
    have h := (log_br_591).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (591 : ℕ) / 2 ≤ ((63818161/20000000 : ℚ) : ℝ) := by
    have h := (log_br_591).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1477989/4000000) (δ := 65853/2500000000) 1053 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_592 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (592 : ℕ) / 2)) - ((4160569/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31917533/10000000 : ℚ) : ℝ) ≤ Real.log (592 : ℕ) / 2 := by
    have h := (log_br_592).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (592 : ℕ) / 2 ≤ ((63835067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_592).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14697203/100000000) (δ := 263291/10000000000) 1053 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_593 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (593 : ℕ) / 2)) - ((1193917/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31925971/10000000 : ℚ) : ℝ) ≤ Real.log (593 : ℕ) / 2 := by
    have h := (log_br_593).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (593 : ℕ) / 2 ≤ ((12770389/4000000 : ℚ) : ℝ) := by
    have h := (log_br_593).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1879287/25000000) (δ := 789891/10000000000) 1053 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_594 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (594 : ℕ) / 2)) - ((3736657/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63868793/20000000 : ℚ) : ℝ) ≤ Real.log (594 : ℕ) / 2 := by
    have h := (log_br_594).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (594 : ℕ) / 2 ≤ ((31934397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_594).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29695961/100000000) (δ := 16457/625000000) 1053 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_595 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (595 : ℕ) / 2)) - ((-96353/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31942807/10000000 : ℚ) : ℝ) ≤ Real.log (595 : ℕ) / 2 := by
    have h := (log_br_595).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (595 : ℕ) / 2 ≤ ((12777123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_595).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25918301/50000000) (δ := 263291/10000000000) 1053 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_596 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (596 : ℕ) / 2)) - ((-9831143/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31951203/10000000 : ℚ) : ℝ) ≤ Real.log (596 : ℕ) / 2 := by
    have h := (log_br_596).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (596 : ℕ) / 2 ≤ ((63902407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_596).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 577649/781250) (δ := 263291/10000000000) 1053 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_597 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (597 : ℕ) / 2)) - ((-957141/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63919171/20000000 : ℚ) : ℝ) ≤ Real.log (597 : ℕ) / 2 := by
    have h := (log_br_597).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (597 : ℕ) / 2 ≤ ((15979793/5000000 : ℚ) : ℝ) := by
    have h := (log_br_597).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61073629/100000000) (δ := 32923/1250000000) 1053 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_598 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (598 : ℕ) / 2)) - ((45007/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63935907/20000000 : ℚ) : ℝ) ≤ Real.log (598 : ℕ) / 2 := by
    have h := (log_br_598).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (598 : ℕ) / 2 ≤ ((15983977/5000000 : ℚ) : ℝ) := by
    have h := (log_br_598).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39044869/100000000) (δ := 32923/1250000000) 1053 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_599 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (599 : ℕ) / 2)) - ((1940597/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12790523/4000000 : ℚ) : ℝ) ≤ Real.log (599 : ℕ) / 2 := by
    have h := (log_br_599).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (599 : ℕ) / 2 ≤ ((7994077/2500000 : ℚ) : ℝ) := by
    have h := (log_br_599).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4263241/25000000) (δ := 32923/1250000000) 1053 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_600 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (600 : ℕ) / 2)) - ((9808269/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3998081/1250000 : ℚ) : ℝ) ≤ Real.log (600 : ℕ) / 2 := by
    have h := (log_br_600).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (600 : ℕ) / 2 ≤ ((63969297/20000000 : ℚ) : ℝ) := by
    have h := (log_br_600).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2451701/50000000) (δ := 65821/2500000000) 1053 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_601 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (601 : ℕ) / 2)) - ((2387819/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63985949/20000000 : ℚ) : ℝ) ≤ Real.log (601 : ℕ) / 2 := by
    have h := (log_br_601).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (601 : ℕ) / 2 ≤ ((1279719/400000 : ℚ) : ℝ) := by
    have h := (log_br_601).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26822913/100000000) (δ := 263319/10000000000) 1053 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_602 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (602 : ℕ) / 2)) - ((-3685293/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32001287/10000000 : ℚ) : ℝ) ≤ Real.log (602 : ℕ) / 2 := by
    have h := (log_br_602).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (602 : ℕ) / 2 ≤ ((2560103/800000 : ℚ) : ℝ) := by
    have h := (log_br_602).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48705569/100000000) (δ := 263419/10000000000) 1053 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_603 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (603 : ℕ) / 2)) - ((-9493807/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64019171/20000000 : ℚ) : ℝ) ≤ Real.log (603 : ℕ) / 2 := by
    have h := (log_br_603).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (603 : ℕ) / 2 ≤ ((16004793/5000000 : ℚ) : ℝ) := by
    have h := (log_br_603).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70551371/100000000) (δ := 32923/1250000000) 1053 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_604 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (604 : ℕ) / 2)) - ((-1702039/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64035741/20000000 : ℚ) : ℝ) ≤ Real.log (604 : ℕ) / 2 := by
    have h := (log_br_604).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (604 : ℕ) / 2 ≤ ((32017871/10000000 : ℚ) : ℝ) := by
    have h := (log_br_604).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32359/50000) (δ := 263447/10000000000) 1053 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_605 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (605 : ℕ) / 2)) - ((-732033/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16013071/5000000 : ℚ) : ℝ) ≤ Real.log (605 : ℕ) / 2 := by
    have h := (log_br_605).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (605 : ℕ) / 2 ≤ ((12810457/4000000 : ℚ) : ℝ) := by
    have h := (log_br_605).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10735819/25000000) (δ := 263347/10000000000) 1053 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_606 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (606 : ℕ) / 2)) - ((3306611/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64068799/20000000 : ℚ) : ℝ) ≤ Real.log (606 : ℕ) / 2 := by
    have h := (log_br_606).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (606 : ℕ) / 2 ≤ ((40043/12500 : ℚ) : ℝ) := by
    have h := (log_br_606).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21205407/100000000) (δ := 32907/1250000000) 1053 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_607 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (607 : ℕ) / 2)) - ((399921/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64085287/20000000 : ℚ) : ℝ) ≤ Real.log (607 : ℕ) / 2 := by
    have h := (log_br_607).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (607 : ℕ) / 2 ≤ ((8010661/2500000 : ℚ) : ℝ) := by
    have h := (log_br_607).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 496923/100000000) (δ := 32907/1250000000) 1053 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_608 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (608 : ℕ) / 2)) - ((6320903/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16025437/5000000 : ℚ) : ℝ) ≤ Real.log (608 : ℕ) / 2 := by
    have h := (log_br_608).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (608 : ℕ) / 2 ≤ ((64101749/20000000 : ℚ) : ℝ) := by
    have h := (log_br_608).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11081857/50000000) (δ := 263347/10000000000) 1053 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_609 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (609 : ℕ) / 2)) - ((-450039/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32059091/10000000 : ℚ) : ℝ) ≤ Real.log (609 : ℕ) / 2 := by
    have h := (log_br_609).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (609 : ℕ) / 2 ≤ ((64118183/20000000 : ℚ) : ℝ) := by
    have h := (log_br_609).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 43794967/100000000) (δ := 65839/2500000000) 1053 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_610 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (610 : ℕ) / 2)) - ((-2162099/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64134589/20000000 : ℚ) : ℝ) ≤ Real.log (610 : ℕ) / 2 := by
    have h := (log_br_610).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (610 : ℕ) / 2 ≤ ((6413459/2000000 : ℚ) : ℝ) := by
    have h := (log_br_610).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1634767/2500000) (δ := 263447/10000000000) 1053 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_611 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (611 : ℕ) / 2)) - ((-4719677/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64150969/20000000 : ℚ) : ℝ) ≤ Real.log (611 : ℕ) / 2 := by
    have h := (log_br_611).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (611 : ℕ) / 2 ≤ ((6415097/2000000 : ℚ) : ℝ) := by
    have h := (log_br_611).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70128777/100000000) (δ := 8229/312500000) 1053 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_612 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (612 : ℕ) / 2)) - ((-3647547/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32083661/10000000 : ℚ) : ℝ) ≤ Real.log (612 : ℕ) / 2 := by
    have h := (log_br_612).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (612 : ℕ) / 2 ≤ ((64167323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_612).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -48604141/100000000) (δ := 10531/400000000) 1053 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_613 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (613 : ℕ) / 2)) - ((2336557/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64183649/20000000 : ℚ) : ℝ) ≤ Real.log (613 : ℕ) / 2 := by
    have h := (log_br_613).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (613 : ℕ) / 2 ≤ ((1283673/400000 : ℚ) : ℝ) := by
    have h := (log_br_613).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27113727/100000000) (δ := 8229/312500000) 1053 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_614 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (614 : ℕ) / 2)) - ((9744911/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64199949/20000000 : ℚ) : ℝ) ≤ Real.log (614 : ℕ) / 2 := by
    have h := (log_br_614).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (614 : ℕ) / 2 ≤ ((1283999/400000 : ℚ) : ℝ) := by
    have h := (log_br_614).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1414713/25000000) (δ := 8229/312500000) 1053 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_615 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (615 : ℕ) / 2)) - ((2019451/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32108111/10000000 : ℚ) : ℝ) ≤ Real.log (615 : ℕ) / 2 := by
    have h := (log_br_615).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (615 : ℕ) / 2 ≤ ((64216223/20000000 : ℚ) : ℝ) := by
    have h := (log_br_615).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3940121/25000000) (δ := 10531/400000000) 1053 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_616 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (616 : ℕ) / 2)) - ((424351/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64232469/20000000 : ℚ) : ℝ) ≤ Real.log (616 : ℕ) / 2 := by
    have h := (log_br_616).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (616 : ℕ) / 2 ≤ ((6423247/2000000 : ℚ) : ℝ) := by
    have h := (log_br_616).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18572799/50000000) (δ := 8229/312500000) 1053 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_617 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (617 : ℕ) / 2)) - ((-54333/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6424869/2000000 : ℚ) : ℝ) ≤ Real.log (617 : ℕ) / 2 := by
    have h := (log_br_617).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (617 : ℕ) / 2 ≤ ((64248691/20000000 : ℚ) : ℝ) := by
    have h := (log_br_617).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58496489/100000000) (δ := 10531/400000000) 1053 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_618 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (618 : ℕ) / 2)) - ((-4993529/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16066221/5000000 : ℚ) : ℝ) ≤ Real.log (618 : ℕ) / 2 := by
    have h := (log_br_618).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (618 : ℕ) / 2 ≤ ((12852977/4000000 : ℚ) : ℝ) := by
    have h := (log_br_618).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77267791/100000000) (δ := 263299/10000000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_619 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (619 : ℕ) / 2)) - ((-619943/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16070263/5000000 : ℚ) : ℝ) ≤ Real.log (619 : ℕ) / 2 := by
    have h := (log_br_619).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (619 : ℕ) / 2 ≤ ((64281053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_619).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55986661/100000000) (δ := 263299/10000000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_620 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (620 : ℕ) / 2)) - ((1802161/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32148597/10000000 : ℚ) : ℝ) ≤ Real.log (620 : ℕ) / 2 := by
    have h := (log_br_620).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (620 : ℕ) / 2 ≤ ((12859439/4000000 : ℚ) : ℝ) := by
    have h := (log_br_620).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17369877/50000000) (δ := 65851/2500000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_621 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (621 : ℕ) / 2)) - ((1714303/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6431331/2000000 : ℚ) : ℝ) ≤ Real.log (621 : ℕ) / 2 := by
    have h := (log_br_621).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (621 : ℕ) / 2 ≤ ((64313311/20000000 : ℚ) : ℝ) := by
    have h := (log_br_621).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13527069/100000000) (δ := 65851/2500000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_622 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (622 : ℕ) / 2)) - ((4767647/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((321647/100000 : ℚ) : ℝ) ≤ Real.log (622 : ℕ) / 2 := by
    have h := (log_br_622).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (622 : ℕ) / 2 ≤ ((64329401/20000000 : ℚ) : ℝ) := by
    have h := (log_br_622).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3825697/50000000) (δ := 263299/10000000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_623 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (623 : ℕ) / 2)) - ((2033863/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12869093/4000000 : ℚ) : ℝ) ≤ Real.log (623 : ℕ) / 2 := by
    have h := (log_br_623).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (623 : ℕ) / 2 ≤ ((32172733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_623).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 575939/2000000) (δ := 32913/1250000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_624 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (624 : ℕ) / 2)) - ((-2063801/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64361503/20000000 : ℚ) : ℝ) ≤ Real.log (624 : ℕ) / 2 := by
    have h := (log_br_624).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (624 : ℕ) / 2 ≤ ((2011297/625000 : ℚ) : ℝ) := by
    have h := (log_br_624).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6238371/12500000) (δ := 263399/10000000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_625 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (625 : ℕ) / 2)) - ((-9546753/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/5000000 : ℚ) : ℝ) ≤ Real.log (625 : ℕ) / 2 := by
    have h := (log_br_625).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (625 : ℕ) / 2 ≤ ((64377517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_625).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70984079/100000000) (δ := 263299/10000000000) 1053 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_626 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (626 : ℕ) / 2)) - ((-536233/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64393503/20000000 : ℚ) : ℝ) ≤ Real.log (626 : ℕ) / 2 := by
    have h := (log_br_626).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (626 : ℕ) / 2 ≤ ((2012297/625000 : ℚ) : ℝ) := by
    have h := (log_br_626).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13010533/20000000) (δ := 263271/10000000000) 1053 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_627 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (627 : ℕ) / 2)) - ((-948767/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12881893/4000000 : ℚ) : ℝ) ≤ Real.log (627 : ℕ) / 2 := by
    have h := (log_br_627).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (627 : ℕ) / 2 ≤ ((32204733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_627).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44042683/100000000) (δ := 32929/1250000000) 1053 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_628 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (628 : ℕ) / 2)) - ((3018441/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64425401/20000000 : ℚ) : ℝ) ≤ Real.log (628 : ℕ) / 2 := by
    have h := (log_br_628).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (628 : ℕ) / 2 ≤ ((32212701/10000000 : ℚ) : ℝ) := by
    have h := (log_br_628).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23066923/100000000) (δ := 32929/1250000000) 1053 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_629 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (629 : ℕ) / 2)) - ((1245491/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2013791/625000 : ℚ) : ℝ) ≤ Real.log (629 : ℕ) / 2 := by
    have h := (log_br_629).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (629 : ℕ) / 2 ≤ ((64441313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_629).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2124069/100000000) (δ := 65833/2500000000) 1053 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_630 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (630 : ℕ) / 2)) - ((7307099/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32228599/10000000 : ℚ) : ℝ) ≤ Real.log (630 : ℕ) / 2 := by
    have h := (log_br_630).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (630 : ℕ) / 2 ≤ ((64457199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_630).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18785879/100000000) (δ := 263371/10000000000) 1053 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_631 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (631 : ℕ) / 2)) - ((-1224/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32236529/10000000 : ℚ) : ℝ) ≤ Real.log (631 : ℕ) / 2 := by
    have h := (log_br_631).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (631 : ℕ) / 2 ≤ ((64473059/20000000 : ℚ) : ℝ) := by
    have h := (log_br_631).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9915401/25000000) (δ := 263371/10000000000) 1053 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_632 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (632 : ℕ) / 2)) - ((-3754357/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64488893/20000000 : ℚ) : ℝ) ≤ Real.log (632 : ℕ) / 2 := by
    have h := (log_br_632).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (632 : ℕ) / 2 ≤ ((32244447/10000000 : ℚ) : ℝ) := by
    have h := (log_br_632).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30252211/50000000) (δ := 32929/1250000000) 1053 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_633 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (633 : ℕ) / 2)) - ((-9938421/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((503943/156250 : ℚ) : ℝ) ≤ Real.log (633 : ℕ) / 2 := by
    have h := (log_br_633).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (633 : ℕ) / 2 ≤ ((12900941/4000000 : ℚ) : ℝ) := by
    have h := (log_br_633).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75763981/100000000) (δ := 263443/10000000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_634 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (634 : ℕ) / 2)) - ((-2940399/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64520489/20000000 : ℚ) : ℝ) ≤ Real.log (634 : ℕ) / 2 := by
    have h := (log_br_634).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (634 : ℕ) / 2 ≤ ((6452049/2000000 : ℚ) : ℝ) := by
    have h := (log_br_634).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2199479/4000000) (δ := 263343/10000000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_635 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (635 : ℕ) / 2)) - ((199729/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8067031/2500000 : ℚ) : ℝ) ≤ Real.log (635 : ℕ) / 2 := by
    have h := (log_br_635).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (635 : ℕ) / 2 ≤ ((64536251/20000000 : ℚ) : ℝ) := by
    have h := (log_br_635).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -273943/800000) (δ := 789843/10000000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_636 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (636 : ℕ) / 2)) - ((2142709/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12910397/4000000 : ℚ) : ℝ) ≤ Real.log (636 : ℕ) / 2 := by
    have h := (log_br_636).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (636 : ℕ) / 2 ≤ ((32275993/10000000 : ℚ) : ℝ) := by
    have h := (log_br_636).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2706073/20000000) (δ := 263343/10000000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_637 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (637 : ℕ) / 2)) - ((4796943/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4035481/1250000 : ℚ) : ℝ) ≤ Real.log (637 : ℕ) / 2 := by
    have h := (log_br_637).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (637 : ℕ) / 2 ≤ ((64567697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_637).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7149239/100000000) (δ := 263443/10000000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_638 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (638 : ℕ) / 2)) - ((88603/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32291691/10000000 : ℚ) : ℝ) ≤ Real.log (638 : ℕ) / 2 := by
    have h := (log_br_638).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (638 : ℕ) / 2 ≤ ((64583383/20000000 : ℚ) : ℝ) := by
    have h := (log_br_638).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 868623/3125000) (δ := 13163/500000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_639 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (639 : ℕ) / 2)) - ((-3575521/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16149761/5000000 : ℚ) : ℝ) ≤ Real.log (639 : ℕ) / 2 := by
    have h := (log_br_639).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (639 : ℕ) / 2 ≤ ((12919809/4000000 : ℚ) : ℝ) := by
    have h := (log_br_639).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12102761/25000000) (δ := 263443/10000000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_640 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (640 : ℕ) / 2)) - ((-9279721/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64614681/20000000 : ℚ) : ℝ) ≤ Real.log (640 : ℕ) / 2 := by
    have h := (log_br_640).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (640 : ℕ) / 2 ≤ ((32307341/10000000 : ℚ) : ℝ) := by
    have h := (log_br_640).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13798649/20000000) (δ := 263343/10000000000) 1053 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_641 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (641 : ℕ) / 2)) - ((-2261707/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32315147/10000000 : ℚ) : ℝ) ≤ Real.log (641 : ℕ) / 2 := by
    have h := (log_br_641).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (641 : ℕ) / 2 ≤ ((12926059/4000000 : ℚ) : ℝ) := by
    have h := (log_br_641).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67535777/100000000) (δ := 65847/2500000000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_642 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (642 : ℕ) / 2)) - ((-609877/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64645883/20000000 : ℚ) : ℝ) ≤ Real.log (642 : ℕ) / 2 := by
    have h := (log_br_642).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (642 : ℕ) / 2 ≤ ((16161471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_642).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9403351/20000000) (δ := 52683/2000000000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_643 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (643 : ℕ) / 2)) - ((2439013/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64661447/20000000 : ℚ) : ℝ) ≤ Real.log (643 : ℕ) / 2 := by
    have h := (log_br_643).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (643 : ℕ) / 2 ≤ ((8082681/2500000 : ℚ) : ℝ) := by
    have h := (log_br_643).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -331633/1250000) (δ := 52683/2000000000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_644 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (644 : ℕ) / 2)) - ((4853049/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64676987/20000000 : ℚ) : ℝ) ≤ Real.log (644 : ℕ) / 2 := by
    have h := (log_br_644).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (644 : ℕ) / 2 ≤ ((16169247/5000000 : ℚ) : ℝ) := by
    have h := (log_br_644).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1215223/20000000) (δ := 52683/2000000000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_645 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (645 : ℕ) / 2)) - ((262439/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64692503/20000000 : ℚ) : ℝ) ≤ Real.log (645 : ℕ) / 2 := by
    have h := (log_br_645).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (645 : ℕ) / 2 ≤ ((8086563/2500000 : ℚ) : ℝ) := by
    have h := (log_br_645).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 717341/5000000) (δ := 52683/2000000000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_646 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (646 : ℕ) / 2)) - ((901393/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12941599/4000000 : ℚ) : ℝ) ≤ Real.log (646 : ℕ) / 2 := by
    have h := (log_br_646).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (646 : ℕ) / 2 ≤ ((16176999/5000000 : ℚ) : ℝ) := by
    have h := (log_br_646).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6947633/20000000) (δ := 52683/2000000000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_647 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (647 : ℕ) / 2)) - ((-369763/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32361731/10000000 : ℚ) : ℝ) ≤ Real.log (647 : ℕ) / 2 := by
    have h := (log_br_647).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (647 : ℕ) / 2 ≤ ((64723463/20000000 : ℚ) : ℝ) := by
    have h := (log_br_647).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 55096603/100000000) (δ := 65847/2500000000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_648 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (648 : ℕ) / 2)) - ((-1240309/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12947781/4000000 : ℚ) : ℝ) ≤ Real.log (648 : ℕ) / 2 := by
    have h := (log_br_648).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (648 : ℕ) / 2 ≤ ((16184727/5000000 : ℚ) : ℝ) := by
    have h := (log_br_648).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 294628/390625) (δ := 6171/78125000) 1053 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_649 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (649 : ℕ) / 2)) - ((-7729531/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64754327/20000000 : ℚ) : ℝ) ≤ Real.log (649 : ℕ) / 2 := by
    have h := (log_br_649).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (649 : ℕ) / 2 ≤ ((8094291/2500000 : ℚ) : ℝ) := by
    have h := (log_br_649).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61356973/100000000) (δ := 263287/10000000000) 1053 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_650 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (650 : ℕ) / 2)) - ((-728187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64769723/20000000 : ℚ) : ℝ) ≤ Real.log (650 : ℕ) / 2 := by
    have h := (log_br_650).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (650 : ℕ) / 2 ≤ ((16192431/5000000 : ℚ) : ℝ) := by
    have h := (log_br_650).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10272997/25000000) (δ := 263287/10000000000) 1053 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_651 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (651 : ℕ) / 2)) - ((671703/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8098137/2500000 : ℚ) : ℝ) ≤ Real.log (651 : ℕ) / 2 := by
    have h := (log_br_651).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (651 : ℕ) / 2 ≤ ((64785097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_651).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20857277/100000000) (δ := 65829/2500000000) 1053 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_652 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (652 : ℕ) / 2)) - ((9996577/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12960089/4000000 : ℚ) : ℝ) ≤ Real.log (652 : ℕ) / 2 := by
    have h := (log_br_652).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (652 : ℕ) / 2 ≤ ((32400223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_652).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -163539/25000000) (δ := 32927/1250000000) 1053 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_653 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (653 : ℕ) / 2)) - ((56831/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64815771/20000000 : ℚ) : ℝ) ≤ Real.log (653 : ℕ) / 2 := by
    have h := (log_br_653).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (653 : ℕ) / 2 ≤ ((16203943/5000000 : ℚ) : ℝ) := by
    have h := (log_br_653).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4879673/25000000) (δ := 263287/10000000000) 1053 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_654 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (654 : ℕ) / 2)) - ((-15601/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64831073/20000000 : ℚ) : ℝ) ≤ Real.log (654 : ℕ) / 2 := by
    have h := (log_br_654).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (654 : ℕ) / 2 ≤ ((32415537/10000000 : ℚ) : ℝ) := by
    have h := (log_br_654).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39659949/100000000) (δ := 32927/1250000000) 1053 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_655 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (655 : ℕ) / 2)) - ((-3655869/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4052897/1250000 : ℚ) : ℝ) ≤ Real.log (655 : ℕ) / 2 := by
    have h := (log_br_655).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (655 : ℕ) / 2 ≤ ((64846353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_655).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 59770933/100000000) (δ := 65829/2500000000) 1053 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_656 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (656 : ℕ) / 2)) - ((-1248283/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64861607/20000000 : ℚ) : ℝ) ≤ Real.log (656 : ℕ) / 2 := by
    have h := (log_br_656).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (656 : ℕ) / 2 ≤ ((8107701/2500000 : ℚ) : ℝ) := by
    have h := (log_br_656).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38614653/50000000) (δ := 52669/2000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_657 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (657 : ℕ) / 2)) - ((-3283213/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1621921/500000 : ℚ) : ℝ) ≤ Real.log (657 : ℕ) / 2 := by
    have h := (log_br_657).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (657 : ℕ) / 2 ≤ ((64876841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_657).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5717887/10000000) (δ := 52689/2000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_658 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (658 : ℕ) / 2)) - ((842953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64892049/20000000 : ℚ) : ℝ) ≤ Real.log (658 : ℕ) / 2 := by
    have h := (log_br_658).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (658 : ℕ) / 2 ≤ ((1297841/400000 : ℚ) : ℝ) := by
    have h := (log_br_658).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37160023/100000000) (δ := 131679/5000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_659 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (659 : ℕ) / 2)) - ((3866211/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12981447/4000000 : ℚ) : ℝ) ≤ Real.log (659 : ℕ) / 2 := by
    have h := (log_br_659).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (659 : ℕ) / 2 ≤ ((16226809/5000000 : ℚ) : ℝ) := by
    have h := (log_br_659).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17171451/100000000) (δ := 52669/2000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_660 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (660 : ℕ) / 2)) - ((2484483/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32461199/10000000 : ℚ) : ℝ) ≤ Real.log (660 : ℕ) / 2 := by
    have h := (log_br_660).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (660 : ℕ) / 2 ≤ ((64922399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_660).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 87089/3125000) (δ := 131629/5000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_661 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (661 : ℕ) / 2)) - ((1229709/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32468769/10000000 : ℚ) : ℝ) ≤ Real.log (661 : ℕ) / 2 := by
    have h := (log_br_661).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (661 : ℕ) / 2 ≤ ((64937539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_661).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22714873/100000000) (δ := 131629/5000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_662 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (662 : ℕ) / 2)) - ((-666553/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12990531/4000000 : ℚ) : ℝ) ≤ Real.log (662 : ℕ) / 2 := by
    have h := (log_br_662).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (662 : ℕ) / 2 ≤ ((4059541/1250000 : ℚ) : ℝ) := by
    have h := (log_br_662).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2663289/6250000) (δ := 52669/2000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_663 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (663 : ℕ) / 2)) - ((-800667/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64967749/20000000 : ℚ) : ℝ) ≤ Real.log (663 : ℕ) / 2 := by
    have h := (log_br_663).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (663 : ℕ) / 2 ≤ ((259871/80000 : ℚ) : ℝ) := by
    have h := (log_br_663).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31240051/50000000) (δ := 131679/5000000000) 1053 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_664 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (664 : ℕ) / 2)) - ((-4942991/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64982821/20000000 : ℚ) : ℝ) ≤ Real.log (664 : ℕ) / 2 := by
    have h := (log_br_664).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (664 : ℕ) / 2 ≤ ((32491411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_664).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74761011/100000000) (δ := 263273/10000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_665 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (665 : ℕ) / 2)) - ((-234789/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6499787/2000000 : ℚ) : ℝ) ≤ Real.log (665 : ℕ) / 2 := by
    have h := (log_br_665).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (665 : ℕ) / 2 ≤ ((64997871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_665).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10990553/20000000) (δ := 263373/10000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_666 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (666 : ℕ) / 2)) - ((1630731/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2031653/625000 : ℚ) : ℝ) ≤ Real.log (666 : ℕ) / 2 := by
    have h := (log_br_666).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (666 : ℕ) / 2 ≤ ((65012897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_666).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4396849/12500000) (δ := 26333/1000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_667 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (667 : ℕ) / 2)) - ((8155999/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((650279/200000 : ℚ) : ℝ) ≤ Real.log (667 : ℕ) / 2 := by
    have h := (log_br_667).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (667 : ℕ) / 2 ≤ ((65027901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_667).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15425777/100000000) (δ := 26333/1000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_668 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (668 : ℕ) / 2)) - ((4926463/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65042881/20000000 : ℚ) : ℝ) ≤ Real.log (668 : ℕ) / 2 := by
    have h := (log_br_668).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (668 : ℕ) / 2 ≤ ((32521441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_668).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1073241/25000000) (δ := 263273/10000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_669 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (669 : ℕ) / 2)) - ((1435213/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((813223/250000 : ℚ) : ℝ) ≤ Real.log (669 : ℕ) / 2 := by
    have h := (log_br_669).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (669 : ℕ) / 2 ≤ ((65057841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_669).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5995687/25000000) (δ := 26333/1000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_670 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (670 : ℕ) / 2)) - ((-435139/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8134097/2500000 : ℚ) : ℝ) ≤ Real.log (670 : ℕ) / 2 := by
    have h := (log_br_670).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (670 : ℕ) / 2 ≤ ((65072779/20000000 : ℚ) : ℝ) := by
    have h := (log_br_670).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21821787/50000000) (δ := 789773/10000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_671 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (671 : ℕ) / 2)) - ((-8192883/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65087691/20000000 : ℚ) : ℝ) ≤ Real.log (671 : ℕ) / 2 := by
    have h := (log_br_671).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (671 : ℕ) / 2 ≤ ((16271923/5000000 : ℚ) : ℝ) := by
    have h := (log_br_671).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 63274127/100000000) (δ := 26343/1000000000) 1053 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_672 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (672 : ℕ) / 2)) - ((-1231247/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65102583/20000000 : ℚ) : ℝ) ≤ Real.log (672 : ℕ) / 2 := by
    have h := (log_br_672).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (672 : ℕ) / 2 ≤ ((8137823/2500000 : ℚ) : ℝ) := by
    have h := (log_br_672).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74203911/100000000) (δ := 131651/5000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_673 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (673 : ℕ) / 2)) - ((-576513/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65117453/20000000 : ℚ) : ℝ) ≤ Real.log (673 : ℕ) / 2 := by
    have h := (log_br_673).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (673 : ℕ) / 2 ≤ ((32558727/10000000 : ℚ) : ℝ) := by
    have h := (log_br_673).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27315637/50000000) (δ := 263401/10000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_674 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (674 : ℕ) / 2)) - ((1665133/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((651323/200000 : ℚ) : ℝ) ≤ Real.log (674 : ℕ) / 2 := by
    have h := (log_br_674).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (674 : ℕ) / 2 ≤ ((65132303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_674).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17543797/50000000) (δ := 789901/10000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_675 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (675 : ℕ) / 2)) - ((8121507/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32573563/10000000 : ℚ) : ℝ) ≤ Real.log (675 : ℕ) / 2 := by
    have h := (log_br_675).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (675 : ℕ) / 2 ≤ ((65147127/20000000 : ℚ) : ℝ) := by
    have h := (log_br_675).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15574187/100000000) (δ := 131701/5000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_676 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (676 : ℕ) / 2)) - ((4938923/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/2000000 : ℚ) : ℝ) ≤ Real.log (676 : ℕ) / 2 := by
    have h := (log_br_676).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (676 : ℕ) / 2 ≤ ((65161931/20000000 : ℚ) : ℝ) := by
    have h := (log_br_676).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1955789/50000000) (δ := 131701/5000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_677 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (677 : ℕ) / 2)) - ((5940313/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8147089/2500000 : ℚ) : ℝ) ≤ Real.log (677 : ℕ) / 2 := by
    have h := (log_br_677).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (677 : ℕ) / 2 ≤ ((65176713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_677).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4673677/20000000) (δ := 263301/10000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_678 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (678 : ℕ) / 2)) - ((-702929/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4074467/1250000 : ℚ) : ℝ) ≤ Real.log (678 : ℕ) / 2 := by
    have h := (log_br_678).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (678 : ℕ) / 2 ≤ ((65191473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_678).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8559247/20000000) (δ := 263301/10000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_679 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (679 : ℕ) / 2)) - ((-7938179/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65206211/20000000 : ℚ) : ℝ) ≤ Real.log (679 : ℕ) / 2 := by
    have h := (log_br_679).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (679 : ℕ) / 2 ≤ ((16301553/5000000 : ℚ) : ℝ) := by
    have h := (log_br_679).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15549111/25000000) (δ := 131651/5000000000) 1053 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_680 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (680 : ℕ) / 2)) - ((-9926809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65220927/20000000 : ℚ) : ℝ) ≤ Real.log (680 : ℕ) / 2 := by
    have h := (log_br_680).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (680 : ℕ) / 2 ≤ ((1019077/312500 : ℚ) : ℝ) := by
    have h := (log_br_680).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37756627/50000000) (δ := 263329/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_681 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (681 : ℕ) / 2)) - ((-1251339/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32617811/10000000 : ℚ) : ℝ) ≤ Real.log (681 : ℕ) / 2 := by
    have h := (log_br_681).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (681 : ℕ) / 2 ≤ ((104377/32000 : ℚ) : ℝ) := by
    have h := (log_br_681).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14042411/25000000) (δ := 789829/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_682 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (682 : ℕ) / 2)) - ((963941/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8156287/2500000 : ℚ) : ℝ) ≤ Real.log (682 : ℕ) / 2 := by
    have h := (log_br_682).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (682 : ℕ) / 2 ≤ ((65250297/20000000 : ℚ) : ℝ) := by
    have h := (log_br_682).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9214077/25000000) (δ := 263429/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_683 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (683 : ℕ) / 2)) - ((1526039/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16316237/5000000 : ℚ) : ℝ) ≤ Real.log (683 : ℕ) / 2 := by
    have h := (log_br_683).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (683 : ℕ) / 2 ≤ ((65264949/20000000 : ℚ) : ℝ) := by
    have h := (log_br_683).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17570613/100000000) (δ := 263429/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_684 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (684 : ℕ) / 2)) - ((9977229/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65279579/20000000 : ℚ) : ℝ) ≤ Real.log (684 : ℕ) / 2 := by
    have h := (log_br_684).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (684 : ℕ) / 2 ≤ ((3263979/1000000 : ℚ) : ℝ) := by
    have h := (log_br_684).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1687441/100000000) (δ := 263329/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_685 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (685 : ℕ) / 2)) - ((6699451/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16323547/5000000 : ℚ) : ℝ) ≤ Real.log (685 : ℕ) / 2 := by
    have h := (log_br_685).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (685 : ℕ) / 2 ≤ ((65294189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_685).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20916537/100000000) (δ := 263429/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_686 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (686 : ℕ) / 2)) - ((-10599/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8163597/2500000 : ℚ) : ℝ) ≤ Real.log (686 : ℕ) / 2 := by
    have h := (log_br_686).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (686 : ℕ) / 2 ≤ ((65308777/20000000 : ℚ) : ℝ) := by
    have h := (log_br_686).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5014749/12500000) (δ := 263429/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_687 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (687 : ℕ) / 2)) - ((-3589647/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32661671/10000000 : ℚ) : ℝ) ≤ Real.log (687 : ℕ) / 2 := by
    have h := (log_br_687).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (687 : ℕ) / 2 ≤ ((65323343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_687).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5929049/10000000) (δ := 131637/5000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_688 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (688 : ℕ) / 2)) - ((-1999983/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2041809/625000 : ℚ) : ℝ) ≤ Real.log (688 : ℕ) / 2 := by
    have h := (log_br_688).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (688 : ℕ) / 2 ≤ ((65337889/20000000 : ℚ) : ℝ) := by
    have h := (log_br_688).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39218331/50000000) (δ := 263429/10000000000) 1053 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_689 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (689 : ℕ) / 2)) - ((-1811121/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16338103/5000000 : ℚ) : ℝ) ≤ Real.log (689 : ℕ) / 2 := by
    have h := (log_br_689).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (689 : ℕ) / 2 ≤ ((65352413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_689).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11905151/20000000) (δ := 131673/5000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_690 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (690 : ℕ) / 2)) - ((-23317/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13073383/4000000 : ℚ) : ℝ) ≤ Real.log (690 : ℕ) / 2 := by
    have h := (log_br_690).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (690 : ℕ) / 2 ≤ ((16341729/5000000 : ℚ) : ℝ) := by
    have h := (log_br_690).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40436181/100000000) (δ := 131723/5000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_691 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (691 : ℕ) / 2)) - ((6562809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32690699/10000000 : ℚ) : ℝ) ≤ Real.log (691 : ℕ) / 2 := by
    have h := (log_br_691).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (691 : ℕ) / 2 ≤ ((65381399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_691).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21372933/100000000) (δ := 263357/10000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_692 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (692 : ℕ) / 2)) - ((4978139/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65395859/20000000 : ℚ) : ℝ) ≤ Real.log (692 : ℕ) / 2 := by
    have h := (log_br_692).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (692 : ℕ) / 2 ≤ ((3269793/1000000 : ℚ) : ℝ) := by
    have h := (log_br_692).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2338641/100000000) (δ := 131723/5000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_693 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (693 : ℕ) / 2)) - ((7858541/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32705149/10000000 : ℚ) : ℝ) ≤ Real.log (693 : ℕ) / 2 := by
    have h := (log_br_693).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (693 : ℕ) / 2 ≤ ((65410301/20000000 : ℚ) : ℝ) := by
    have h := (log_br_693).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16668009/100000000) (δ := 394973/5000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_694 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (694 : ℕ) / 2)) - ((90223/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65424719/20000000 : ℚ) : ℝ) ≤ Real.log (694 : ℕ) / 2 := by
    have h := (log_br_694).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (694 : ℕ) / 2 ≤ ((817809/250000 : ℚ) : ℝ) := by
    have h := (log_br_694).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17824167/50000000) (δ := 131723/5000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_695 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (695 : ℕ) / 2)) - ((-5755237/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32719559/10000000 : ℚ) : ℝ) ≤ Real.log (695 : ℕ) / 2 := by
    have h := (log_br_695).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (695 : ℕ) / 2 ≤ ((65439119/20000000 : ℚ) : ℝ) := by
    have h := (log_br_695).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54601017/100000000) (δ := 263357/10000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_696 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (696 : ℕ) / 2)) - ((-9799571/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8181687/2500000 : ℚ) : ℝ) ≤ Real.log (696 : ℕ) / 2 := by
    have h := (log_br_696).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (696 : ℕ) / 2 ≤ ((65453497/20000000 : ℚ) : ℝ) := by
    have h := (log_br_696).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3676303/5000000) (δ := 131673/5000000000) 1053 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_697 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (697 : ℕ) / 2)) - ((-1062113/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32733927/10000000 : ℚ) : ℝ) ≤ Real.log (697 : ℕ) / 2 := by
    have h := (log_br_697).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (697 : ℕ) / 2 ≤ ((13093571/4000000 : ℚ) : ℝ) := by
    have h := (log_br_697).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12930971/20000000) (δ := 263417/10000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_698 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (698 : ℕ) / 2)) - ((-2576167/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6548219/2000000 : ℚ) : ℝ) ≤ Real.log (698 : ℕ) / 2 := by
    have h := (log_br_698).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (698 : ℕ) / 2 ≤ ((65482193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_698).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -45783779/100000000) (δ := 789817/10000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_699 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (699 : ℕ) / 2)) - ((1183579/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65496507/20000000 : ℚ) : ℝ) ≤ Real.log (699 : ℕ) / 2 := by
    have h := (log_br_699).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (699 : ℕ) / 2 ≤ ((16374127/5000000 : ℚ) : ℝ) := by
    have h := (log_br_699).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3367543/12500000) (δ := 263317/10000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_700 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (700 : ℕ) / 2)) - ((9476733/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65510803/20000000 : ℚ) : ℝ) ≤ Real.log (700 : ℕ) / 2 := by
    have h := (log_br_700).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (700 : ℕ) / 2 ≤ ((16377701/5000000 : ℚ) : ℝ) := by
    have h := (log_br_700).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4061617/50000000) (δ := 263317/10000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_701 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (701 : ℕ) / 2)) - ((4551787/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32762539/10000000 : ℚ) : ℝ) ≤ Real.log (701 : ℕ) / 2 := by
    have h := (log_br_701).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (701 : ℕ) / 2 ≤ ((65525079/20000000 : ℚ) : ℝ) := by
    have h := (log_br_701).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2133247/20000000) (δ := 263417/10000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_702 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (702 : ℕ) / 2)) - ((1917433/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65539333/20000000 : ℚ) : ℝ) ≤ Real.log (702 : ℕ) / 2 := by
    have h := (log_br_702).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (702 : ℕ) / 2 ≤ ((8192417/2500000 : ℚ) : ℝ) := by
    have h := (log_br_702).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5886139/20000000) (δ := 789917/10000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_703 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (703 : ℕ) / 2)) - ((-3483887/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2048549/625000 : ℚ) : ℝ) ≤ Real.log (703 : ℕ) / 2 := by
    have h := (log_br_703).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (703 : ℕ) / 2 ≤ ((65553569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_703).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 48166197/100000000) (δ := 131643/5000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_704 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (704 : ℕ) / 2)) - ((-8931367/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65567783/20000000 : ℚ) : ℝ) ≤ Real.log (704 : ℕ) / 2 := by
    have h := (log_br_704).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (704 : ℕ) / 2 ≤ ((8195973/2500000 : ℚ) : ℝ) := by
    have h := (log_br_704).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66876691/100000000) (δ := 263317/10000000000) 1053 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_705 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (705 : ℕ) / 2)) - ((-384329/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65581977/20000000 : ℚ) : ℝ) ≤ Real.log (705 : ℕ) / 2 := by
    have h := (log_br_705).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (705 : ℕ) / 2 ≤ ((3279099/1000000 : ℚ) : ℝ) := by
    have h := (log_br_705).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -71518773/100000000) (δ := 789789/10000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_706 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (706 : ℕ) / 2)) - ((-1293251/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8199519/2500000 : ℚ) : ℝ) ≤ Real.log (706 : ℕ) / 2 := by
    have h := (log_br_706).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (706 : ℕ) / 2 ≤ ((65596153/20000000 : ℚ) : ℝ) := by
    have h := (log_br_706).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26431123/50000000) (δ := 131707/5000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_707 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (707 : ℕ) / 2)) - ((400307/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32805153/10000000 : ℚ) : ℝ) ≤ Real.log (707 : ℕ) / 2 := by
    have h := (log_br_707).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (707 : ℕ) / 2 ≤ ((65610307/20000000 : ℚ) : ℝ) := by
    have h := (log_br_707).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34232043/100000000) (δ := 263289/10000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_708 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (708 : ℕ) / 2)) - ((810889/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1640611/500000 : ℚ) : ℝ) ≤ Real.log (708 : ℕ) / 2 := by
    have h := (log_br_708).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (708 : ℕ) / 2 ≤ ((65624441/20000000 : ℚ) : ℝ) := by
    have h := (log_br_708).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7814083/50000000) (δ := 131707/5000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_709 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (709 : ℕ) / 2)) - ((2482607/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13127711/4000000 : ℚ) : ℝ) ≤ Real.log (709 : ℕ) / 2 := by
    have h := (log_br_709).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (709 : ℕ) / 2 ≤ ((16409639/5000000 : ℚ) : ℝ) := by
    have h := (log_br_709).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2950703/100000000) (δ := 131657/5000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_710 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (710 : ℕ) / 2)) - ((6523789/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65652649/20000000 : ℚ) : ℝ) ≤ Real.log (710 : ℕ) / 2 := by
    have h := (log_br_710).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (710 : ℕ) / 2 ≤ ((1313053/400000 : ℚ) : ℝ) := by
    have h := (log_br_710).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21501931/100000000) (δ := 263389/10000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_711 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (711 : ℕ) / 2)) - ((-1213/40000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16416681/5000000 : ℚ) : ℝ) ≤ Real.log (711 : ℕ) / 2 := by
    have h := (log_br_711).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (711 : ℕ) / 2 ≤ ((2626669/800000 : ℚ) : ℝ) := by
    have h := (log_br_711).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40028149/100000000) (δ := 131707/5000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_712 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (712 : ℕ) / 2)) - ((-870461/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65680779/20000000 : ℚ) : ℝ) ≤ Real.log (712 : ℕ) / 2 := by
    have h := (log_br_712).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (712 : ℕ) / 2 ≤ ((3284039/1000000 : ℚ) : ℝ) := by
    have h := (log_br_712).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58528043/100000000) (δ := 131657/5000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_713 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (713 : ℕ) / 2)) - ((-9981077/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32847407/10000000 : ℚ) : ℝ) ≤ Real.log (713 : ℕ) / 2 := by
    have h := (log_br_713).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (713 : ℕ) / 2 ≤ ((13138963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_713).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19250403/25000000) (δ := 263289/10000000000) 1053 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_714 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (714 : ℕ) / 2)) - ((-3899277/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65708829/20000000 : ℚ) : ℝ) ≤ Real.log (714 : ℕ) / 2 := by
    have h := (log_br_714).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (714 : ℕ) / 2 ≤ ((6570883/2000000 : ℚ) : ℝ) := by
    have h := (log_br_714).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61630777/100000000) (δ := 263261/10000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_715 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (715 : ℕ) / 2)) - ((-98059/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2628913/800000 : ℚ) : ℝ) ≤ Real.log (715 : ℕ) / 2 := by
    have h := (log_br_715).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (715 : ℕ) / 2 ≤ ((32861413/10000000 : ℚ) : ℝ) := by
    have h := (log_br_715).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21604271/50000000) (δ := 263261/10000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_716 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (716 : ℕ) / 2)) - ((5465937/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65736801/20000000 : ℚ) : ℝ) ≤ Real.log (716 : ℕ) / 2 := by
    have h := (log_br_716).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (716 : ℕ) / 2 ≤ ((32868401/10000000 : ℚ) : ℝ) := by
    have h := (log_br_716).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3101579/12500000) (δ := 263261/10000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_717 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (717 : ℕ) / 2)) - ((1933973/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32875379/10000000 : ℚ) : ℝ) ≤ Real.log (717 : ℕ) / 2 := by
    have h := (log_br_717).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (717 : ℕ) / 2 ≤ ((65750759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_717).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6441731/100000000) (δ := 131671/5000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_718 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (718 : ℕ) / 2)) - ((2221957/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13152939/4000000 : ℚ) : ℝ) ≤ Real.log (718 : ℕ) / 2 := by
    have h := (log_br_718).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (718 : ℕ) / 2 ≤ ((8220587/2500000 : ℚ) : ℝ) := by
    have h := (log_br_718).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2380569/20000000) (δ := 131721/5000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_719 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (719 : ℕ) / 2)) - ((885129/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65778613/20000000 : ℚ) : ℝ) ≤ Real.log (719 : ℕ) / 2 := by
    have h := (log_br_719).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (719 : ℕ) / 2 ≤ ((32889307/10000000 : ℚ) : ℝ) := by
    have h := (log_br_719).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30222413/100000000) (δ := 263261/10000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_720 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (720 : ℕ) / 2)) - ((-3615059/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((257002/78125 : ℚ) : ℝ) ≤ Real.log (720 : ℕ) / 2 := by
    have h := (log_br_720).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (720 : ℕ) / 2 ≤ ((65792513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_720).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12129243/25000000) (δ := 263361/10000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_721 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (721 : ℕ) / 2)) - ((-8914847/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65806391/20000000 : ℚ) : ℝ) ≤ Real.log (721 : ℕ) / 2 := by
    have h := (log_br_721).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (721 : ℕ) / 2 ≤ ((8225799/2500000 : ℚ) : ℝ) := by
    have h := (log_br_721).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13357041/20000000) (δ := 131721/5000000000) 1053 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_722 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (722 : ℕ) / 2)) - ((-966507/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65820251/20000000 : ℚ) : ℝ) ≤ Real.log (722 : ℕ) / 2 := by
    have h := (log_br_722).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (722 : ℕ) / 2 ≤ ((16455063/5000000 : ℚ) : ℝ) := by
    have h := (log_br_722).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36025601/50000000) (δ := 263333/10000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_723 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (723 : ℕ) / 2)) - ((-5501327/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16458523/5000000 : ℚ) : ℝ) ≤ Real.log (723 : ℕ) / 2 := by
    have h := (log_br_723).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (723 : ℕ) / 2 ≤ ((65834093/20000000 : ℚ) : ℝ) := by
    have h := (log_br_723).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26916493/50000000) (δ := 26327/1000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_724 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (724 : ℕ) / 2)) - ((723217/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65847913/20000000 : ℚ) : ℝ) ≤ Real.log (724 : ℕ) / 2 := by
    have h := (log_br_724).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (724 : ℕ) / 2 ≤ ((32923957/10000000 : ℚ) : ℝ) := by
    have h := (log_br_724).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7128219/20000000) (δ := 26337/1000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_725 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (725 : ℕ) / 2)) - ((3827701/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16465429/5000000 : ℚ) : ℝ) ≤ Real.log (725 : ℕ) / 2 := by
    have h := (log_br_725).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (725 : ℕ) / 2 ≤ ((65861717/20000000 : ℚ) : ℝ) := by
    have h := (log_br_725).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -136507/781250) (δ := 26327/1000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_726 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (726 : ℕ) / 2)) - ((4998203/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((131751/40000 : ℚ) : ℝ) ≤ Real.log (726 : ℕ) / 2 := by
    have h := (log_br_726).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (726 : ℕ) / 2 ≤ ((65875501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_726).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 335147/50000000) (δ := 26327/1000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_727 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (727 : ℕ) / 2)) - ((7306749/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4118079/1250000 : ℚ) : ℝ) ≤ Real.log (727 : ℕ) / 2 := by
    have h := (log_br_727).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (727 : ℕ) / 2 ≤ ((13177853/4000000 : ℚ) : ℝ) := by
    have h := (log_br_727).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18787159/100000000) (δ := 26327/1000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_728 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (728 : ℕ) / 2)) - ((119297/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6590301/2000000 : ℚ) : ℝ) ≤ Real.log (728 : ℕ) / 2 := by
    have h := (log_br_728).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (728 : ℕ) / 2 ≤ ((65903011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_728).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9220083/25000000) (δ := 263433/10000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_729 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (729 : ℕ) / 2)) - ((-2934171/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65916737/20000000 : ℚ) : ℝ) ≤ Real.log (729 : ℕ) / 2 := by
    have h := (log_br_729).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (729 : ℕ) / 2 ≤ ((32958369/10000000 : ℚ) : ℝ) := by
    have h := (log_br_729).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10989699/20000000) (δ := 26337/1000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_730 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (730 : ℕ) / 2)) - ((-76209/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13186089/4000000 : ℚ) : ℝ) ≤ Real.log (730 : ℕ) / 2 := by
    have h := (log_br_730).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (730 : ℕ) / 2 ≤ ((32965223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_730).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1459833/2000000) (δ := 26337/1000000000) 1053 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_731 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (731 : ℕ) / 2)) - ((-1097697/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32972067/10000000 : ℚ) : ℝ) ≤ Real.log (731 : ℕ) / 2 := by
    have h := (log_br_731).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (731 : ℕ) / 2 ≤ ((13188827/4000000 : ℚ) : ℝ) := by
    have h := (log_br_731).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16517459/25000000) (δ := 52661/2000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_732 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (732 : ℕ) / 2)) - ((-1724907/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13191561/4000000 : ℚ) : ℝ) ≤ Real.log (732 : ℕ) / 2 := by
    have h := (log_br_732).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (732 : ℕ) / 2 ≤ ((32978903/10000000 : ℚ) : ℝ) := by
    have h := (log_br_732).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24037691/50000000) (δ := 52681/2000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_733 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (733 : ℕ) / 2)) - ((71681/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((257701/78125 : ℚ) : ℝ) ≤ Real.log (733 : ℕ) / 2 := by
    have h := (log_br_733).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (733 : ℕ) / 2 ≤ ((65971459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_733).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30105937/100000000) (δ := 157981/2000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_734 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (734 : ℕ) / 2)) - ((8839933/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6598509/2000000 : ℚ) : ℝ) ≤ Real.log (734 : ℕ) / 2 := by
    have h := (log_br_734).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (734 : ℕ) / 2 ≤ ((65985091/20000000 : ℚ) : ℝ) := by
    have h := (log_br_734).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12161501/100000000) (δ := 52661/2000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_735 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (735 : ℕ) / 2)) - ((9735941/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4124919/1250000 : ℚ) : ℝ) ≤ Real.log (735 : ℕ) / 2 := by
    have h := (log_br_735).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (735 : ℕ) / 2 ≤ ((13199741/4000000 : ℚ) : ℝ) := by
    have h := (log_br_735).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2878963/50000000) (δ := 131699/5000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_736 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (736 : ℕ) / 2)) - ((2923853/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66012301/20000000 : ℚ) : ℝ) ≤ Real.log (736 : ℕ) / 2 := by
    have h := (log_br_736).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (736 : ℕ) / 2 ≤ ((33006151/10000000 : ℚ) : ℝ) := by
    have h := (log_br_736).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11827489/50000000) (δ := 52681/2000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_737 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (737 : ℕ) / 2)) - ((-450547/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33012939/10000000 : ℚ) : ℝ) ≤ Real.log (737 : ℕ) / 2 := by
    have h := (log_br_737).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (737 : ℕ) / 2 ≤ ((66025879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_737).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5190713/12500000) (δ := 52661/2000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_738 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (738 : ℕ) / 2)) - ((-3601261/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33019719/10000000 : ℚ) : ℝ) ≤ Real.log (738 : ℕ) / 2 := by
    have h := (log_br_738).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (738 : ℕ) / 2 ≤ ((66039439/20000000 : ℚ) : ℝ) := by
    have h := (log_br_738).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29687027/50000000) (δ := 52661/2000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_739 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (739 : ℕ) / 2)) - ((-9985587/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66052979/20000000 : ℚ) : ℝ) ≤ Real.log (739 : ℕ) / 2 := by
    have h := (log_br_739).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (739 : ℕ) / 2 ≤ ((3302649/1000000 : ℚ) : ℝ) := by
    have h := (log_br_739).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15439479/20000000) (δ := 131649/5000000000) 1053 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_740 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (740 : ℕ) / 2)) - ((-7910723/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66066501/20000000 : ℚ) : ℝ) ≤ Real.log (740 : ℕ) / 2 := by
    have h := (log_br_740).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (740 : ℕ) / 2 ≤ ((33033251/10000000 : ℚ) : ℝ) := by
    have h := (log_br_740).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12416781/20000000) (δ := 65819/2500000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_741 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (741 : ℕ) / 2)) - ((-500401/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33040003/10000000 : ℚ) : ℝ) ≤ Real.log (741 : ℕ) / 2 := by
    have h := (log_br_741).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (741 : ℕ) / 2 ≤ ((66080007/20000000 : ℚ) : ℝ) := by
    have h := (log_br_741).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44307949/100000000) (δ := 263327/10000000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_742 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (742 : ℕ) / 2)) - ((2434409/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16523373/5000000 : ℚ) : ℝ) ≤ Real.log (742 : ℕ) / 2 := by
    have h := (log_br_742).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (742 : ℕ) / 2 ≤ ((66093493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_742).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26557001/100000000) (δ := 16461/625000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_743 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (743 : ℕ) / 2)) - ((9382741/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((826337/250000 : ℚ) : ℝ) ≤ Real.log (743 : ℕ) / 2 := by
    have h := (log_br_743).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (743 : ℕ) / 2 ≤ ((66106961/20000000 : ℚ) : ℝ) := by
    have h := (log_br_743).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4414873/50000000) (δ := 16461/625000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_744 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (744 : ℕ) / 2)) - ((9376629/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6612041/2000000 : ℚ) : ℝ) ≤ Real.log (744 : ℕ) / 2 := by
    have h := (log_br_744).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (744 : ℕ) / 2 ≤ ((66120411/20000000 : ℚ) : ℝ) := by
    have h := (log_br_744).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1109227/12500000) (δ := 263327/10000000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_745 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (745 : ℕ) / 2)) - ((608747/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33066921/10000000 : ℚ) : ℝ) ≤ Real.log (745 : ℕ) / 2 := by
    have h := (log_br_745).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (745 : ℕ) / 2 ≤ ((66133843/20000000 : ℚ) : ℝ) := by
    have h := (log_br_745).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13276843/50000000) (δ := 263327/10000000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_746 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (746 : ℕ) / 2)) - ((-1963149/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13229451/4000000 : ℚ) : ℝ) ≤ Real.log (746 : ℕ) / 2 := by
    have h := (log_br_746).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (746 : ℕ) / 2 ≤ ((33073629/10000000 : ℚ) : ℝ) := by
    have h := (log_br_746).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5526233/12500000) (δ := 197469/2500000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_747 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (747 : ℕ) / 2)) - ((-3925461/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66160651/20000000 : ℚ) : ℝ) ≤ Real.log (747 : ℕ) / 2 := by
    have h := (log_br_747).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (747 : ℕ) / 2 ≤ ((16540163/5000000 : ℚ) : ℝ) := by
    have h := (log_br_747).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7730129/12500000) (δ := 263427/10000000000) 1053 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_748 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (748 : ℕ) / 2)) - ((-312293/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66174029/20000000 : ℚ) : ℝ) ≤ Real.log (748 : ℕ) / 2 := by
    have h := (log_br_748).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (748 : ℕ) / 2 ≤ ((6617403/2000000 : ℚ) : ℝ) := by
    have h := (log_br_748).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4851863/6250000) (δ := 52671/2000000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_749 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (749 : ℕ) / 2)) - ((-1477201/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66187389/20000000 : ℚ) : ℝ) ≤ Real.log (749 : ℕ) / 2 := by
    have h := (log_br_749).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (749 : ℕ) / 2 ≤ ((6618739/2000000 : ℚ) : ℝ) := by
    have h := (log_br_749).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15011177/25000000) (δ := 52671/2000000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_750 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (750 : ℕ) / 2)) - ((-640649/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16550183/5000000 : ℚ) : ℝ) ≤ Real.log (750 : ℕ) / 2 := by
    have h := (log_br_750).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (750 : ℕ) / 2 ≤ ((66200733/20000000 : ℚ) : ℝ) := by
    have h := (log_br_750).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -663781/1562500) (δ := 52651/2000000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_751 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (751 : ℕ) / 2)) - ((677721/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8276757/2500000 : ℚ) : ℝ) ≤ Real.log (751 : ℕ) / 2 := by
    have h := (log_br_751).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (751 : ℕ) / 2 ≤ ((66214057/20000000 : ℚ) : ℝ) := by
    have h := (log_br_751).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24944269/100000000) (δ := 52651/2000000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_752 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (752 : ℕ) / 2)) - ((9561727/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66227363/20000000 : ℚ) : ℝ) ≤ Real.log (752 : ℕ) / 2 := by
    have h := (log_br_752).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (752 : ℕ) / 2 ≤ ((16556841/5000000 : ℚ) : ℝ) := by
    have h := (log_br_752).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -742893/10000000) (δ := 65837/2500000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_753 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (753 : ℕ) / 2)) - ((2300203/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16560163/5000000 : ℚ) : ℝ) ≤ Real.log (753 : ℕ) / 2 := by
    have h := (log_br_753).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (753 : ℕ) / 2 ≤ ((66240653/20000000 : ℚ) : ℝ) := by
    have h := (log_br_753).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2515679/25000000) (δ := 52651/2000000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_754 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (754 : ℕ) / 2)) - ((141407/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66253923/20000000 : ℚ) : ℝ) ≤ Real.log (754 : ℕ) / 2 := by
    have h := (log_br_754).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (754 : ℕ) / 2 ≤ ((16563481/5000000 : ℚ) : ℝ) := by
    have h := (log_br_754).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2753067/10000000) (δ := 65837/2500000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_755 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (755 : ℕ) / 2)) - ((-2262767/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66267177/20000000 : ℚ) : ℝ) ≤ Real.log (755 : ℕ) / 2 := by
    have h := (log_br_755).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (755 : ℕ) / 2 ≤ ((33133589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_755).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44976247/100000000) (δ := 52671/2000000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_756 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (756 : ℕ) / 2)) - ((-998373/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66280413/20000000 : ℚ) : ℝ) ≤ Real.log (756 : ℕ) / 2 := by
    have h := (log_br_756).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (756 : ℕ) / 2 ≤ ((33140207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_756).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15599533/25000000) (δ := 52671/2000000000) 1053 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_757 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (757 : ℕ) / 2)) - ((-4993673/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((517919/156250 : ℚ) : ℝ) ≤ Real.log (757 : ℕ) / 2 := by
    have h := (log_br_757).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (757 : ℕ) / 2 ≤ ((66293633/20000000 : ℚ) : ℝ) := by
    have h := (log_br_757).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9660249/12500000) (δ := 263383/10000000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_758 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (758 : ℕ) / 2)) - ((-1469707/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66306833/20000000 : ℚ) : ℝ) ≤ Real.log (758 : ℕ) / 2 := by
    have h := (log_br_758).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (758 : ℕ) / 2 ≤ ((33153417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_758).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2396247/4000000) (δ := 13171/500000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_759 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (759 : ℕ) / 2)) - ((-16367/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66320017/20000000 : ℚ) : ℝ) ≤ Real.log (759 : ℕ) / 2 := by
    have h := (log_br_759).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (759 : ℕ) / 2 ≤ ((33160009/10000000 : ℚ) : ℝ) := by
    have h := (log_br_759).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8510547/20000000) (δ := 13171/500000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_760 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (760 : ℕ) / 2)) - ((5328199/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((259114/78125 : ℚ) : ℝ) ≤ Real.log (760 : ℕ) / 2 := by
    have h := (log_br_760).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (760 : ℕ) / 2 ≤ ((13266637/4000000 : ℚ) : ℝ) := by
    have h := (log_br_760).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3152709/12500000) (δ := 263383/10000000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_761 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (761 : ℕ) / 2)) - ((4751541/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66346333/20000000 : ℚ) : ℝ) ≤ Real.log (761 : ℕ) / 2 := by
    have h := (log_br_761).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (761 : ℕ) / 2 ≤ ((33173167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_761).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -79143/1000000) (δ := 13171/500000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_762 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (762 : ℕ) / 2)) - ((9305707/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13271893/4000000 : ℚ) : ℝ) ≤ Real.log (762 : ℕ) / 2 := by
    have h := (log_br_762).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (762 : ℕ) / 2 ≤ ((33179733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_762).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1874139/20000000) (δ := 13171/500000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_763 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (763 : ℕ) / 2)) - ((4842133/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3318629/1000000 : ℚ) : ℝ) ≤ Real.log (763 : ℕ) / 2 := by
    have h := (log_br_763).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (763 : ℕ) / 2 ≤ ((66372581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_763).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26633313/100000000) (δ := 263383/10000000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_764 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (764 : ℕ) / 2)) - ((-228819/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66385677/20000000 : ℚ) : ℝ) ≤ Real.log (764 : ℕ) / 2 := by
    have h := (log_br_764).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (764 : ℕ) / 2 ≤ ((33192839/10000000 : ℚ) : ℝ) := by
    have h := (log_br_764).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 548403/1250000) (δ := 13171/500000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_765 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (765 : ℕ) / 2)) - ((-1532273/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33199379/10000000 : ℚ) : ℝ) ≤ Real.log (765 : ℕ) / 2 := by
    have h := (log_br_765).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (765 : ℕ) / 2 ≤ ((66398759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_765).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30545053/50000000) (δ := 6583/250000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_766 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (766 : ℕ) / 2)) - ((-4999739/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66411821/20000000 : ℚ) : ℝ) ≤ Real.log (766 : ℕ) / 2 := by
    have h := (log_br_766).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (766 : ℕ) / 2 ≤ ((33205911/10000000 : ℚ) : ℝ) := by
    have h := (log_br_766).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1957107/2500000) (δ := 13171/500000000) 1053 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_767 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (767 : ℕ) / 2)) - ((-121819/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16606217/5000000 : ℚ) : ℝ) ≤ Real.log (767 : ℕ) / 2 := by
    have h := (log_br_767).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (767 : ℕ) / 2 ≤ ((66424869/20000000 : ℚ) : ℝ) := by
    have h := (log_br_767).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61622239/100000000) (δ := 8231/312500000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_768 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (768 : ℕ) / 2)) - ((-2066173/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66437897/20000000 : ℚ) : ℝ) ≤ Real.log (768 : ℕ) / 2 := by
    have h := (log_br_768).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (768 : ℕ) / 2 ≤ ((33218949/10000000 : ℚ) : ℝ) := by
    have h := (log_br_768).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22236409/50000000) (δ := 65823/2500000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_769 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (769 : ℕ) / 2)) - ((2295427/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66450909/20000000 : ℚ) : ℝ) ≤ Real.log (769 : ℕ) / 2 := by
    have h := (log_br_769).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (769 : ℕ) / 2 ≤ ((6645091/2000000 : ℚ) : ℝ) := by
    have h := (log_br_769).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27345773/100000000) (δ := 65823/2500000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_770 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (770 : ℕ) / 2)) - ((2293209/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13292781/4000000 : ℚ) : ℝ) ≤ Real.log (770 : ℕ) / 2 := by
    have h := (log_br_770).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (770 : ℕ) / 2 ≤ ((33231953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_770).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2559947/25000000) (δ := 65823/2500000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_771 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (771 : ℕ) / 2)) - ((4813887/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66476883/20000000 : ℚ) : ℝ) ≤ Real.log (771 : ℕ) / 2 := by
    have h := (log_br_771).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (771 : ℕ) / 2 ≤ ((16619221/5000000 : ℚ) : ℝ) := by
    have h := (log_br_771).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 855313/12500000) (δ := 263411/10000000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_772 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (772 : ℕ) / 2)) - ((57667/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13297969/4000000 : ℚ) : ℝ) ≤ Real.log (772 : ℕ) / 2 := by
    have h := (log_br_772).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (772 : ℕ) / 2 ≤ ((33244923/10000000 : ℚ) : ℝ) := by
    have h := (log_br_772).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23903737/100000000) (δ := 65823/2500000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_773 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (773 : ℕ) / 2)) - ((-26743/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6650279/2000000 : ℚ) : ℝ) ≤ Real.log (773 : ℕ) / 2 := by
    have h := (log_br_773).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (773 : ℕ) / 2 ≤ ((66502791/20000000 : ℚ) : ℝ) := by
    have h := (log_br_773).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40942593/100000000) (δ := 263311/10000000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_774 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (774 : ℕ) / 2)) - ((-3399281/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33257859/10000000 : ℚ) : ℝ) ≤ Real.log (774 : ℕ) / 2 := by
    have h := (log_br_774).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (774 : ℕ) / 2 ≤ ((66515719/20000000 : ℚ) : ℝ) := by
    have h := (log_br_774).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 57959073/100000000) (δ := 263311/10000000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_775 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (775 : ℕ) / 2)) - ((-494867/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6652863/2000000 : ℚ) : ℝ) ≤ Real.log (775 : ℕ) / 2 := by
    have h := (log_br_775).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (775 : ℕ) / 2 ≤ ((66528631/20000000 : ℚ) : ℝ) := by
    have h := (log_br_775).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 74954493/100000000) (δ := 263311/10000000000) 1053 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_776 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (776 : ℕ) / 2)) - ((-8600091/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2661661/800000 : ℚ) : ℝ) ≤ Real.log (776 : ℕ) / 2 := by
    have h := (log_br_776).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (776 : ℕ) / 2 ≤ ((33270763/10000000 : ℚ) : ℝ) := by
    have h := (log_br_776).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2036003/3125000) (δ := 263339/10000000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_777 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (777 : ℕ) / 2)) - ((-3497093/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66554403/20000000 : ℚ) : ℝ) ≤ Real.log (777 : ℕ) / 2 := by
    have h := (log_br_777).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (777 : ℕ) / 2 ≤ ((16638601/5000000 : ℚ) : ℝ) := by
    have h := (log_br_777).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12050357/25000000) (δ := 65841/2500000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_778 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (778 : ℕ) / 2)) - ((3144939/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13313453/4000000 : ℚ) : ℝ) ≤ Real.log (778 : ℕ) / 2 := by
    have h := (log_br_778).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (778 : ℕ) / 2 ≤ ((33283633/10000000 : ℚ) : ℝ) := by
    have h := (log_br_778).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31271821/100000000) (δ := 263339/10000000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_779 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (779 : ℕ) / 2)) - ((8394187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6658011/2000000 : ℚ) : ℝ) ≤ Real.log (779 : ℕ) / 2 := by
    have h := (log_br_779).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (779 : ℕ) / 2 ≤ ((66580111/20000000 : ℚ) : ℝ) := by
    have h := (log_br_779).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1436459/10000000) (δ := 263439/10000000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_780 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (780 : ℕ) / 2)) - ((1243647/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66592939/20000000 : ℚ) : ℝ) ≤ Real.log (780 : ℕ) / 2 := by
    have h := (log_br_780).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (780 : ℕ) / 2 ≤ ((3329647/1000000 : ℚ) : ℝ) := by
    have h := (log_br_780).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1260791/50000000) (δ := 65841/2500000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_781 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (781 : ℕ) / 2)) - ((1428261/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66605751/20000000 : ℚ) : ℝ) ≤ Real.log (781 : ℕ) / 2 := by
    have h := (log_br_781).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (781 : ℕ) / 2 ≤ ((8325719/2500000 : ℚ) : ℝ) := by
    have h := (log_br_781).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19385377/100000000) (δ := 65841/2500000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_782 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (782 : ℕ) / 2)) - ((1213719/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66618547/20000000 : ℚ) : ℝ) ≤ Real.log (782 : ℕ) / 2 := by
    have h := (log_br_782).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (782 : ℕ) / 2 ≤ ((16654637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_782).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2264257/6250000) (δ := 65841/2500000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_783 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (783 : ℕ) / 2)) - ((-5236609/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33315663/10000000 : ℚ) : ℝ) ≤ Real.log (783 : ℕ) / 2 := by
    have h := (log_br_783).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (783 : ℕ) / 2 ≤ ((66631327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_783).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5304847/10000000) (δ := 263439/10000000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_784 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (784 : ℕ) / 2)) - ((-940183/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/2000000 : ℚ) : ℝ) ≤ Real.log (784 : ℕ) / 2 := by
    have h := (log_br_784).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (784 : ℕ) / 2 ≤ ((66644091/20000000 : ℚ) : ℝ) := by
    have h := (log_br_784).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13969817/20000000) (δ := 263439/10000000000) 1053 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_785 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (785 : ℕ) / 2)) - ((-1896257/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66656837/20000000 : ℚ) : ℝ) ≤ Real.log (785 : ℕ) / 2 := by
    have h := (log_br_785).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (785 : ℕ) / 2 ≤ ((33328419/10000000 : ℚ) : ℝ) := by
    have h := (log_br_785).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17613077/25000000) (δ := 52687/2000000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_786 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (786 : ℕ) / 2)) - ((-1363909/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66669567/20000000 : ℚ) : ℝ) ≤ Real.log (786 : ℕ) / 2 := by
    have h := (log_br_786).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (786 : ℕ) / 2 ≤ ((260428/78125 : ℚ) : ℝ) := by
    have h := (log_br_786).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26848223/50000000) (δ := 65817/2500000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_787 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (787 : ℕ) / 2)) - ((922519/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33341141/10000000 : ℚ) : ℝ) ≤ Real.log (787 : ℕ) / 2 := by
    have h := (log_br_787).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (787 : ℕ) / 2 ≤ ((66682283/20000000 : ℚ) : ℝ) := by
    have h := (log_br_787).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36960327/100000000) (δ := 52667/2000000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_788 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (788 : ℕ) / 2)) - ((3447987/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3334749/1000000 : ℚ) : ℝ) ≤ Real.log (788 : ℕ) / 2 := by
    have h := (log_br_788).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (788 : ℕ) / 2 ≤ ((66694981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_788).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4049317/20000000) (δ := 32921/1250000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_789 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (789 : ℕ) / 2)) - ((9899203/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66707663/20000000 : ℚ) : ℝ) ≤ Real.log (789 : ℕ) / 2 := by
    have h := (log_br_789).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (789 : ℕ) / 2 ≤ ((4169229/1250000 : ℚ) : ℝ) := by
    have h := (log_br_789).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1776293/50000000) (δ := 65817/2500000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_790 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (790 : ℕ) / 2)) - ((1730887/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66720329/20000000 : ℚ) : ℝ) ≤ Real.log (790 : ℕ) / 2 := by
    have h := (log_br_790).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (790 : ℕ) / 2 ≤ ((6672033/2000000 : ℚ) : ℝ) := by
    have h := (log_br_790).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13119037/100000000) (δ := 52687/2000000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_791 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (791 : ℕ) / 2)) - ((92733/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66732979/20000000 : ℚ) : ℝ) ≤ Real.log (791 : ℕ) / 2 := by
    have h := (log_br_791).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (791 : ℕ) / 2 ≤ ((3336649/1000000 : ℚ) : ℝ) := by
    have h := (log_br_791).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29769599/100000000) (δ := 65817/2500000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_792 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (792 : ℕ) / 2)) - ((-21978/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66745613/20000000 : ℚ) : ℝ) ≤ Real.log (792 : ℕ) / 2 := by
    have h := (log_br_792).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (792 : ℕ) / 2 ≤ ((33372807/10000000 : ℚ) : ℝ) := by
    have h := (log_br_792).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23199551/50000000) (δ := 52687/2000000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_793 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (793 : ℕ) / 2)) - ((-63528/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8344779/2500000 : ℚ) : ℝ) ≤ Real.log (793 : ℕ) / 2 := by
    have h := (log_br_793).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (793 : ℕ) / 2 ≤ ((66758233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_793).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3150443/5000000) (δ := 32921/1250000000) 1053 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_794 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (794 : ℕ) / 2)) - ((-9991073/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33385417/10000000 : ℚ) : ℝ) ≤ Real.log (794 : ℕ) / 2 := by
    have h := (log_br_794).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (794 : ℕ) / 2 ≤ ((13354167/4000000 : ℚ) : ℝ) := by
    have h := (log_br_794).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7748339/10000000) (δ := 2057/78125000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_795 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (795 : ℕ) / 2)) - ((-3808179/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66783421/20000000 : ℚ) : ℝ) ≤ Real.log (795 : ℕ) / 2 := by
    have h := (log_br_795).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (795 : ℕ) / 2 ≤ ((33391711/10000000 : ℚ) : ℝ) := by
    have h := (log_br_795).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60915751/100000000) (δ := 263307/10000000000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_796 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (796 : ℕ) / 2)) - ((-2026107/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66795991/20000000 : ℚ) : ℝ) ≤ Real.log (796 : ℕ) / 2 := by
    have h := (log_br_796).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (796 : ℕ) / 2 ≤ ((8349499/2500000 : ℚ) : ℝ) := by
    have h := (log_br_796).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44370489/100000000) (δ := 65849/2500000000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_797 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (797 : ℕ) / 2)) - ((4412557/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33404273/10000000 : ℚ) : ℝ) ≤ Real.log (797 : ℕ) / 2 := by
    have h := (log_br_797).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (797 : ℕ) / 2 ≤ ((66808547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_797).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2784497/10000000) (δ := 2057/78125000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_798 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (798 : ℕ) / 2)) - ((1123583/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13364217/4000000 : ℚ) : ℝ) ≤ Real.log (798 : ℕ) / 2 := by
    have h := (log_br_798).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (798 : ℕ) / 2 ≤ ((33410543/10000000 : ℚ) : ℝ) := by
    have h := (log_br_798).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11340511/100000000) (δ := 263307/10000000000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_799 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (799 : ℕ) / 2)) - ((9789043/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66833609/20000000 : ℚ) : ℝ) ≤ Real.log (799 : ℕ) / 2 := by
    have h := (log_br_799).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (799 : ℕ) / 2 ≤ ((6683361/2000000 : ℚ) : ℝ) := by
    have h := (log_br_799).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1286051/25000000) (δ := 263307/10000000000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_800 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (800 : ℕ) / 2)) - ((3245809/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66846117/20000000 : ℚ) : ℝ) ≤ Real.log (800 : ℕ) / 2 := by
    have h := (log_br_800).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (800 : ℕ) / 2 ≤ ((33423059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_800).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21607859/100000000) (δ := 263307/10000000000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_801 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (801 : ℕ) / 2)) - ((121897/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66858609/20000000 : ℚ) : ℝ) ≤ Real.log (801 : ℕ) / 2 := by
    have h := (log_br_801).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (801 : ℕ) / 2 ≤ ((6685861/2000000 : ℚ) : ℝ) := by
    have h := (log_br_801).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19025227/50000000) (δ := 263307/10000000000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_802 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (802 : ℕ) / 2)) - ((-1142677/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33435543/10000000 : ℚ) : ℝ) ≤ Real.log (802 : ℕ) / 2 := by
    have h := (log_br_802).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (802 : ℕ) / 2 ≤ ((66871087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_802).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10894661/20000000) (δ := 2057/78125000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_803 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (803 : ℕ) / 2)) - ((-4766843/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66883547/20000000 : ℚ) : ℝ) ≤ Real.log (803 : ℕ) / 2 := by
    have h := (log_br_803).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (803 : ℕ) / 2 ≤ ((16720887/5000000 : ℚ) : ℝ) := by
    have h := (log_br_803).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8859387/12500000) (δ := 65849/2500000000) 1053 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_804 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (804 : ℕ) / 2)) - ((-469919/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8361999/2500000 : ℚ) : ℝ) ≤ Real.log (804 : ℕ) / 2 := by
    have h := (log_br_804).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (804 : ℕ) / 2 ≤ ((66895993/20000000 : ℚ) : ℝ) := by
    have h := (log_br_804).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13964761/20000000) (δ := 263279/10000000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_805 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (805 : ℕ) / 2)) - ((-5377081/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33454211/10000000 : ℚ) : ℝ) ≤ Real.log (805 : ℕ) / 2 := by
    have h := (log_br_805).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (805 : ℕ) / 2 ≤ ((66908423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_805).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26731409/50000000) (δ := 1029/39062500) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_806 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (806 : ℕ) / 2)) - ((214569/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66920837/20000000 : ℚ) : ℝ) ≤ Real.log (806 : ℕ) / 2 := by
    have h := (log_br_806).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (806 : ℕ) / 2 ≤ ((33460419/10000000 : ℚ) : ℝ) := by
    have h := (log_br_806).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18560787/50000000) (δ := 65831/2500000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_807 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (807 : ℕ) / 2)) - ((3366787/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16733309/5000000 : ℚ) : ℝ) ≤ Real.log (807 : ℕ) / 2 := by
    have h := (log_br_807).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (807 : ℕ) / 2 ≤ ((66933237/20000000 : ℚ) : ℝ) := by
    have h := (log_br_807).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2080139/10000000) (δ := 263279/10000000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_808 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (808 : ℕ) / 2)) - ((9838369/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3347281/1000000 : ℚ) : ℝ) ≤ Real.log (808 : ℕ) / 2 := by
    have h := (log_br_808).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (808 : ℕ) / 2 ≤ ((66945621/20000000 : ℚ) : ℝ) := by
    have h := (log_br_808).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -90019/2000000) (δ := 263279/10000000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_809 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (809 : ℕ) / 2)) - ((556893/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66957989/20000000 : ℚ) : ℝ) ≤ Real.log (809 : ℕ) / 2 := by
    have h := (log_br_809).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (809 : ℕ) / 2 ≤ ((6695799/2000000 : ℚ) : ℝ) := by
    have h := (log_br_809).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5889873/50000000) (δ := 65831/2500000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_810 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (810 : ℕ) / 2)) - ((54283/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33485171/10000000 : ℚ) : ℝ) ≤ Real.log (810 : ℕ) / 2 := by
    have h := (log_br_810).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (810 : ℕ) / 2 ≤ ((66970343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_810).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14019691/50000000) (δ := 1029/39062500) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_811 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (811 : ℕ) / 2)) - ((-398073/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1674567/500000 : ℚ) : ℝ) ≤ Real.log (811 : ℕ) / 2 := by
    have h := (log_br_811).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (811 : ℕ) / 2 ≤ ((66982681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_811).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1771171/4000000) (δ := 263279/10000000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_812 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (812 : ℕ) / 2)) - ((-3753697/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66995003/20000000 : ℚ) : ℝ) ≤ Real.log (812 : ℕ) / 2 := by
    have h := (log_br_812).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (812 : ℕ) / 2 ≤ ((16748751/5000000 : ℚ) : ℝ) := by
    have h := (log_br_812).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1890607/3125000) (δ := 263379/10000000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_813 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (813 : ℕ) / 2)) - ((-155827/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67007311/20000000 : ℚ) : ℝ) ≤ Real.log (813 : ℕ) / 2 := by
    have h := (log_br_813).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (813 : ℕ) / 2 ≤ ((4187957/1250000 : ℚ) : ℝ) := by
    have h := (log_br_813).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76699829/100000000) (δ := 263379/10000000000) 1053 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_814 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (814 : ℕ) / 2)) - ((-2099917/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67019603/20000000 : ℚ) : ℝ) ≤ Real.log (814 : ℕ) / 2 := by
    have h := (log_br_814).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (814 : ℕ) / 2 ≤ ((16754901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_814).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -64200459/100000000) (δ := 65813/2500000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_815 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (815 : ℕ) / 2)) - ((-1718177/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67031881/20000000 : ℚ) : ℝ) ≤ Real.log (815 : ℕ) / 2 := by
    have h := (log_br_815).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (815 : ℕ) / 2 ≤ ((33515941/10000000 : ℚ) : ℝ) := by
    have h := (log_br_815).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -48039541/100000000) (δ := 263451/10000000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_816 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (816 : ℕ) / 2)) - ((2905571/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67044143/20000000 : ℚ) : ℝ) ≤ Real.log (816 : ℕ) / 2 := by
    have h := (log_br_816).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (816 : ℕ) / 2 ≤ ((4190259/1250000 : ℚ) : ℝ) := by
    have h := (log_br_816).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7974921/25000000) (δ := 65813/2500000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_817 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (817 : ℕ) / 2)) - ((8073301/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6705639/2000000 : ℚ) : ℝ) ≤ Real.log (817 : ℕ) / 2 := by
    have h := (log_br_817).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (817 : ℕ) / 2 ≤ ((67056391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_817).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1577957/10000000) (δ := 263351/10000000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_818 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (818 : ℕ) / 2)) - ((999917/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67068623/20000000 : ℚ) : ℝ) ≤ Real.log (818 : ℕ) / 2 := by
    have h := (log_br_818).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (818 : ℕ) / 2 ≤ ((4191789/1250000 : ℚ) : ℝ) := by
    have h := (log_br_818).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 80529/25000000) (δ := 65813/2500000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_819 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (819 : ℕ) / 2)) - ((1584743/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1677021/500000 : ℚ) : ℝ) ≤ Real.log (819 : ℕ) / 2 := by
    have h := (log_br_819).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (819 : ℕ) / 2 ≤ ((67080841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_819).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8201371/50000000) (δ := 32919/1250000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_820 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (820 : ℕ) / 2)) - ((1344249/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67093043/20000000 : ℚ) : ℝ) ≤ Real.log (820 : ℕ) / 2 := by
    have h := (log_br_820).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (820 : ℕ) / 2 ≤ ((16773261/5000000 : ℚ) : ℝ) := by
    have h := (log_br_820).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32464941/100000000) (δ := 65813/2500000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_821 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (821 : ℕ) / 2)) - ((-112859/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67105231/20000000 : ℚ) : ℝ) ≤ Real.log (821 : ℕ) / 2 := by
    have h := (log_br_821).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (821 : ℕ) / 2 ≤ ((4194077/1250000 : ℚ) : ℝ) := by
    have h := (log_br_821).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12126849/25000000) (δ := 65813/2500000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_822 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (822 : ℕ) / 2)) - ((-132347/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67117403/20000000 : ℚ) : ℝ) ≤ Real.log (822 : ℕ) / 2 := by
    have h := (log_br_822).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (822 : ℕ) / 2 ≤ ((16779351/5000000 : ℚ) : ℝ) := by
    have h := (log_br_822).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64528791/100000000) (δ := 65813/2500000000) 1053 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_823 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (823 : ℕ) / 2)) - ((-1246029/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33564781/10000000 : ℚ) : ℝ) ≤ Real.log (823 : ℕ) / 2 := by
    have h := (log_br_823).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (823 : ℕ) / 2 ≤ ((67129563/20000000 : ℚ) : ℝ) := by
    have h := (log_br_823).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38273279/50000000) (δ := 3291/125000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_824 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (824 : ℕ) / 2)) - ((-7524257/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13428341/4000000 : ℚ) : ℝ) ≤ Real.log (824 : ℕ) / 2 := by
    have h := (log_br_824).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (824 : ℕ) / 2 ≤ ((33570853/10000000 : ℚ) : ℝ) := by
    have h := (log_br_824).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30281667/50000000) (δ := 263323/10000000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_825 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (825 : ℕ) / 2)) - ((-264483/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67153833/20000000 : ℚ) : ℝ) ≤ Real.log (825 : ℕ) / 2 := by
    have h := (log_br_825).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (825 : ℕ) / 2 ≤ ((33576917/10000000 : ℚ) : ℝ) := by
    have h := (log_br_825).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22299927/50000000) (δ := 263323/10000000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_826 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (826 : ℕ) / 2)) - ((2059801/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67165947/20000000 : ℚ) : ℝ) ≤ Real.log (826 : ℕ) / 2 := by
    have h := (log_br_826).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (826 : ℕ) / 2 ≤ ((16791487/5000000 : ℚ) : ℝ) := by
    have h := (log_br_826).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14327401/50000000) (δ := 13169/500000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_827 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (827 : ℕ) / 2)) - ((8731447/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33589023/10000000 : ℚ) : ℝ) ≤ Real.log (827 : ℕ) / 2 := by
    have h := (log_br_827).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (827 : ℕ) / 2 ≤ ((67178047/20000000 : ℚ) : ℝ) := by
    have h := (log_br_827).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12729493/100000000) (δ := 3291/125000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_828 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (828 : ℕ) / 2)) - ((4959671/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67190131/20000000 : ℚ) : ℝ) ≤ Real.log (828 : ℕ) / 2 := by
    have h := (log_br_828).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (828 : ℕ) / 2 ≤ ((16797533/5000000 : ℚ) : ℝ) := by
    have h := (log_br_828).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 794347/25000000) (δ := 13169/500000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_829 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (829 : ℕ) / 2)) - ((1446111/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67202201/20000000 : ℚ) : ℝ) ≤ Real.log (829 : ℕ) / 2 := by
    have h := (log_br_829).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (829 : ℕ) / 2 ≤ ((33601101/10000000 : ℚ) : ℝ) := by
    have h := (log_br_829).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9532263/50000000) (δ := 263323/10000000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_830 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (830 : ℕ) / 2)) - ((862991/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67214257/20000000 : ℚ) : ℝ) ≤ Real.log (830 : ℕ) / 2 := by
    have h := (log_br_830).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (830 : ℕ) / 2 ≤ ((33607129/10000000 : ℚ) : ℝ) := by
    have h := (log_br_830).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8733309/25000000) (δ := 263323/10000000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_831 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (831 : ℕ) / 2)) - ((-888683/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67226297/20000000 : ℚ) : ℝ) ≤ Real.log (831 : ℕ) / 2 := by
    have h := (log_br_831).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (831 : ℕ) / 2 ≤ ((33613149/10000000 : ℚ) : ℝ) := by
    have h := (log_br_831).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25390443/50000000) (δ := 263323/10000000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_832 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (832 : ℕ) / 2)) - ((-444157/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16809581/5000000 : ℚ) : ℝ) ≤ Real.log (832 : ℕ) / 2 := by
    have h := (log_br_832).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (832 : ℕ) / 2 ≤ ((2689533/800000 : ℚ) : ℝ) := by
    have h := (log_br_832).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2664457/4000000) (δ := 263423/10000000000) 1053 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_833 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (833 : ℕ) / 2)) - ((-4939829/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2101573/625000 : ℚ) : ℝ) ≤ Real.log (833 : ℕ) / 2 := by
    have h := (log_br_833).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (833 : ℕ) / 2 ≤ ((67250337/20000000 : ℚ) : ℝ) := by
    have h := (log_br_833).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74657413/100000000) (δ := 131647/5000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_834 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (834 : ℕ) / 2)) - ((-7059797/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33631167/10000000 : ℚ) : ℝ) ≤ Real.log (834 : ℕ) / 2 := by
    have h := (log_br_834).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (834 : ℕ) / 2 ≤ ((13452467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_834).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29432523/50000000) (δ := 263409/10000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_835 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (835 : ℕ) / 2)) - ((-304611/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67274317/20000000 : ℚ) : ℝ) ≤ Real.log (835 : ℕ) / 2 := by
    have h := (log_br_835).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (835 : ℕ) / 2 ≤ ((33637159/10000000 : ℚ) : ℝ) := by
    have h := (log_br_835).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21546211/50000000) (δ := 263309/10000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_836 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (836 : ℕ) / 2)) - ((35887/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33643143/10000000 : ℚ) : ℝ) ≤ Real.log (836 : ℕ) / 2 := by
    have h := (log_br_836).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (836 : ℕ) / 2 ≤ ((67286287/20000000 : ℚ) : ℝ) := by
    have h := (log_br_836).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13669113/50000000) (δ := 263409/10000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_837 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (837 : ℕ) / 2)) - ((447101/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((210307/62500 : ℚ) : ℝ) ≤ Real.log (837 : ℕ) / 2 := by
    have h := (log_br_837).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (837 : ℕ) / 2 ≤ ((67298241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_837).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11603773/100000000) (δ := 131647/5000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_838 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (838 : ℕ) / 2)) - ((4932467/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67310181/20000000 : ℚ) : ℝ) ≤ Real.log (838 : ℕ) / 2 := by
    have h := (log_br_838).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (838 : ℕ) / 2 ≤ ((33655091/10000000 : ℚ) : ℝ) := by
    have h := (log_br_838).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 128549/3125000) (δ := 263309/10000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_839 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (839 : ℕ) / 2)) - ((1755263/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67322107/20000000 : ℚ) : ℝ) ≤ Real.log (839 : ℕ) / 2 := by
    have h := (log_br_839).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (839 : ℕ) / 2 ≤ ((16830527/5000000 : ℚ) : ℝ) := by
    have h := (log_br_839).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9905583/50000000) (δ := 131697/5000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_840 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (840 : ℕ) / 2)) - ((1506597/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33667009/10000000 : ℚ) : ℝ) ≤ Real.log (840 : ℕ) / 2 := by
    have h := (log_br_840).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (840 : ℕ) / 2 ≤ ((67334019/20000000 : ℚ) : ℝ) := by
    have h := (log_br_840).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35489019/100000000) (δ := 263409/10000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_841 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (841 : ℕ) / 2)) - ((-4575111/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/5000000 : ℚ) : ℝ) ≤ Real.log (841 : ℕ) / 2 := by
    have h := (log_br_841).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (841 : ℕ) / 2 ≤ ((67345917/20000000 : ℚ) : ℝ) := by
    have h := (log_br_841).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25574881/50000000) (δ := 131647/5000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_842 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (842 : ℕ) / 2)) - ((-2229023/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((336789/100000 : ℚ) : ℝ) ≤ Real.log (842 : ℕ) / 2 := by
    have h := (log_br_842).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (842 : ℕ) / 2 ≤ ((67357801/20000000 : ℚ) : ℝ) := by
    have h := (log_br_842).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 66792077/100000000) (δ := 131647/5000000000) 1053 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_843 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (843 : ℕ) / 2)) - ((-4940063/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67369669/20000000 : ℚ) : ℝ) ≤ Real.log (843 : ℕ) / 2 := by
    have h := (log_br_843).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (843 : ℕ) / 2 ≤ ((6736967/2000000 : ℚ) : ℝ) := by
    have h := (log_br_843).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14932997/20000000) (δ := 263437/10000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_844 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (844 : ℕ) / 2)) - ((-7115047/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16845381/5000000 : ℚ) : ℝ) ≤ Real.log (844 : ℕ) / 2 := by
    have h := (log_br_844).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (844 : ℕ) / 2 ≤ ((2695261/800000 : ℚ) : ℝ) := by
    have h := (log_br_844).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59060841/100000000) (δ := 263337/10000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_845 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (845 : ℕ) / 2)) - ((-836823/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33696683/10000000 : ℚ) : ℝ) ≤ Real.log (845 : ℕ) / 2 := by
    have h := (log_br_845).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (845 : ℕ) / 2 ≤ ((67393367/20000000 : ℚ) : ℝ) := by
    have h := (log_br_845).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2717113/6250000) (δ := 131683/5000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_846 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (846 : ℕ) / 2)) - ((87809/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67405193/20000000 : ℚ) : ℝ) ≤ Real.log (846 : ℕ) / 2 := by
    have h := (log_br_846).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (846 : ℕ) / 2 ≤ ((33702597/10000000 : ℚ) : ℝ) := by
    have h := (log_br_846).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -697663/2500000) (δ := 263437/10000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_847 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (847 : ℕ) / 2)) - ((440149/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33708503/10000000 : ℚ) : ℝ) ≤ Real.log (847 : ℕ) / 2 := by
    have h := (log_br_847).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (847 : ℕ) / 2 ≤ ((67417007/20000000 : ℚ) : ℝ) := by
    have h := (log_br_847).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6178829/50000000) (δ := 131683/5000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_848 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (848 : ℕ) / 2)) - ((9919509/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33714403/10000000 : ℚ) : ℝ) ≤ Real.log (848 : ℕ) / 2 := by
    have h := (log_br_848).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (848 : ℕ) / 2 ≤ ((67428807/20000000 : ℚ) : ℝ) := by
    have h := (log_br_848).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 793523/25000000) (δ := 131683/5000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_849 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (849 : ℕ) / 2)) - ((458393/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67440591/20000000 : ℚ) : ℝ) ≤ Real.log (849 : ℕ) / 2 := by
    have h := (log_br_849).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (849 : ℕ) / 2 ≤ ((4215037/1250000 : ℚ) : ℝ) := by
    have h := (log_br_849).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9343049/50000000) (δ := 131633/5000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_850 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (850 : ℕ) / 2)) - ((1010769/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67452363/20000000 : ℚ) : ℝ) ≤ Real.log (850 : ℕ) / 2 := by
    have h := (log_br_850).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (850 : ℕ) / 2 ≤ ((16863091/5000000 : ℚ) : ℝ) := by
    have h := (log_br_850).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34180993/100000000) (δ := 131633/5000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_851 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (851 : ℕ) / 2)) - ((-4036493/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67464121/20000000 : ℚ) : ℝ) ≤ Real.log (851 : ℕ) / 2 := by
    have h := (log_br_851).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (851 : ℕ) / 2 ≤ ((33732061/10000000 : ℚ) : ℝ) := by
    have h := (log_br_851).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2482873/5000000) (δ := 263437/10000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_852 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (852 : ℕ) / 2)) - ((-2148153/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13495173/4000000 : ℚ) : ℝ) ≤ Real.log (852 : ℕ) / 2 := by
    have h := (log_br_852).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (852 : ℕ) / 2 ≤ ((33737933/10000000 : ℚ) : ℝ) := by
    have h := (log_br_852).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 130231/200000) (δ := 263437/10000000000) 1053 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_853 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (853 : ℕ) / 2)) - ((-4983763/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13497519/4000000 : ℚ) : ℝ) ≤ Real.log (853 : ℕ) / 2 := by
    have h := (log_br_853).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (853 : ℕ) / 2 ≤ ((16871899/5000000 : ℚ) : ℝ) := by
    have h := (log_br_853).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1913113/2500000) (δ := 52673/2000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_854 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (854 : ℕ) / 2)) - ((-1532953/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67499311/20000000 : ℚ) : ℝ) ≤ Real.log (854 : ℕ) / 2 := by
    have h := (log_br_854).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (854 : ℕ) / 2 ≤ ((4218707/1250000 : ℚ) : ℝ) := by
    have h := (log_br_854).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12220667/20000000) (δ := 52673/2000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_855 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (855 : ℕ) / 2)) - ((-1271743/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33755507/10000000 : ℚ) : ℝ) ≤ Real.log (855 : ℕ) / 2 := by
    have h := (log_br_855).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (855 : ℕ) / 2 ≤ ((13502203/4000000 : ℚ) : ℝ) := by
    have h := (log_br_855).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -45699261/100000000) (δ := 52653/2000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_856 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (856 : ℕ) / 2)) - ((28051/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67522703/20000000 : ℚ) : ℝ) ≤ Real.log (856 : ℕ) / 2 := by
    have h := (log_br_856).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (856 : ℕ) / 2 ≤ ((4220169/1250000 : ℚ) : ℝ) := by
    have h := (log_br_856).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6062723/20000000) (δ := 52673/2000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_857 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (857 : ℕ) / 2)) - ((413287/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67534379/20000000 : ℚ) : ℝ) ≤ Real.log (857 : ℕ) / 2 := by
    have h := (log_br_857).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (857 : ℕ) / 2 ≤ ((3376719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_857).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -373627/2500000) (δ := 52673/2000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_858 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (858 : ℕ) / 2)) - ((1249837/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1688651/500000 : ℚ) : ℝ) ≤ Real.log (858 : ℕ) / 2 := by
    have h := (log_br_858).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (858 : ℕ) / 2 ≤ ((67546041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_858).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1577/390625) (δ := 131719/5000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_859 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (859 : ℕ) / 2)) - ((4041703/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67557689/20000000 : ℚ) : ℝ) ≤ Real.log (859 : ℕ) / 2 := by
    have h := (log_br_859).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (859 : ℕ) / 2 ≤ ((6755769/2000000 : ℚ) : ℝ) := by
    have h := (log_br_859).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3934177/25000000) (δ := 131669/5000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_860 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (860 : ℕ) / 2)) - ((25227/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67569323/20000000 : ℚ) : ℝ) ≤ Real.log (860 : ℕ) / 2 := by
    have h := (log_br_860).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (860 : ℕ) / 2 ≤ ((16892331/5000000 : ℚ) : ℝ) := by
    have h := (log_br_860).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 776249/2500000) (δ := 52673/2000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_861 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (861 : ℕ) / 2)) - ((-139667/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13516189/4000000 : ℚ) : ℝ) ≤ Real.log (861 : ℕ) / 2 := by
    have h := (log_br_861).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (861 : ℕ) / 2 ≤ ((33790473/10000000 : ℚ) : ℝ) := by
    have h := (log_br_861).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23173709/50000000) (δ := 131669/5000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_862 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (862 : ℕ) / 2)) - ((-389857/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8449069/2500000 : ℚ) : ℝ) ≤ Real.log (862 : ℕ) / 2 := by
    have h := (log_br_862).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (862 : ℕ) / 2 ≤ ((67592553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_862).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15406283/25000000) (δ := 131719/5000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_863 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (863 : ℕ) / 2)) - ((-249453/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33802073/10000000 : ℚ) : ℝ) ≤ Real.log (863 : ℕ) / 2 := by
    have h := (log_br_863).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (863 : ℕ) / 2 ≤ ((67604147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_863).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38442867/50000000) (δ := 52653/2000000000) 1053 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_864 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (864 : ℕ) / 2)) - ((-1711729/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67615727/20000000 : ℚ) : ℝ) ≤ Real.log (864 : ℕ) / 2 := by
    have h := (log_br_864).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (864 : ℕ) / 2 ≤ ((4225983/1250000 : ℚ) : ℝ) := by
    have h := (log_br_864).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -64950407/100000000) (δ := 26341/1000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_865 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (865 : ℕ) / 2)) - ((-101521/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13525459/4000000 : ℚ) : ℝ) ≤ Real.log (865 : ℕ) / 2 := by
    have h := (log_br_865).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (865 : ℕ) / 2 ≤ ((2113353/625000 : ℚ) : ℝ) := by
    have h := (log_br_865).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49724027/100000000) (δ := 26341/1000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_866 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (866 : ℕ) / 2)) - ((378019/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67638849/20000000 : ℚ) : ℝ) ≤ Real.log (866 : ℕ) / 2 := by
    have h := (log_br_866).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (866 : ℕ) / 2 ≤ ((1352777/400000 : ℚ) : ℝ) := by
    have h := (log_br_866).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1380643/4000000) (δ := 263293/10000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_867 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (867 : ℕ) / 2)) - ((7157757/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67650389/20000000 : ℚ) : ℝ) ≤ Real.log (867 : ℕ) / 2 := by
    have h := (log_br_867).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (867 : ℕ) / 2 ≤ ((6765039/2000000 : ℚ) : ℝ) := by
    have h := (log_br_867).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -386531/2000000) (δ := 263293/10000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_868 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (868 : ℕ) / 2)) - ((197247/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67661917/20000000 : ℚ) : ℝ) ≤ Real.log (868 : ℕ) / 2 := by
    have h := (log_br_868).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (868 : ℕ) / 2 ≤ ((33830959/10000000 : ℚ) : ℝ) := by
    have h := (log_br_868).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -207641/5000000) (δ := 263293/10000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_869 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (869 : ℕ) / 2)) - ((4523547/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67673431/20000000 : ℚ) : ℝ) ≤ Real.log (869 : ℕ) / 2 := by
    have h := (log_br_869).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (869 : ℕ) / 2 ≤ ((8459179/2500000 : ℚ) : ℝ) := by
    have h := (log_br_869).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11002483/100000000) (δ := 26341/1000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_870 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (870 : ℕ) / 2)) - ((1253399/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16921233/5000000 : ℚ) : ℝ) ≤ Real.log (870 : ℕ) / 2 := by
    have h := (log_br_870).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (870 : ℕ) / 2 ≤ ((67684933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_870).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13070337/50000000) (δ := 26331/1000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_871 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (871 : ℕ) / 2)) - ((-795371/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67696419/20000000 : ℚ) : ℝ) ≤ Real.log (871 : ℕ) / 2 := by
    have h := (log_br_871).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (871 : ℕ) / 2 ≤ ((3384821/1000000 : ℚ) : ℝ) := by
    have h := (log_br_871).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20630219/50000000) (δ := 26341/1000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_872 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (872 : ℕ) / 2)) - ((-6317277/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33853947/10000000 : ℚ) : ℝ) ≤ Real.log (872 : ℕ) / 2 := by
    have h := (log_br_872).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (872 : ℕ) / 2 ≤ ((13541579/4000000 : ℚ) : ℝ) := by
    have h := (log_br_872).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28182203/50000000) (δ := 263393/10000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_873 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (873 : ℕ) / 2)) - ((-4800279/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13543871/4000000 : ℚ) : ℝ) ≤ Real.log (873 : ℕ) / 2 := by
    have h := (log_br_873).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (873 : ℕ) / 2 ≤ ((16929839/5000000 : ℚ) : ℝ) := by
    have h := (log_br_873).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17862487/25000000) (δ := 26341/1000000000) 1053 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_874 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (874 : ℕ) / 2)) - ((-1186881/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67730803/20000000 : ℚ) : ℝ) ≤ Real.log (874 : ℕ) / 2 := by
    have h := (log_br_874).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (874 : ℕ) / 2 ≤ ((16932701/5000000 : ℚ) : ℝ) := by
    have h := (log_br_874).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14112251/20000000) (δ := 131641/5000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_875 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (875 : ℕ) / 2)) - ((-378043/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33871119/10000000 : ℚ) : ℝ) ≤ Real.log (875 : ℕ) / 2 := by
    have h := (log_br_875).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (875 : ℕ) / 2 ≤ ((67742239/20000000 : ℚ) : ℝ) := by
    have h := (log_br_875).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3469371/6250000) (δ := 131691/5000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_876 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (876 : ℕ) / 2)) - ((-482141/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3387683/1000000 : ℚ) : ℝ) ≤ Real.log (876 : ℕ) / 2 := by
    have h := (log_br_876).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (876 : ℕ) / 2 ≤ ((67753661/20000000 : ℚ) : ℝ) := by
    have h := (log_br_876).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40475729/100000000) (δ := 263321/10000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_877 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (877 : ℕ) / 2)) - ((655969/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67765069/20000000 : ℚ) : ℝ) ≤ Real.log (877 : ℕ) / 2 := by
    have h := (log_br_877).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (877 : ℕ) / 2 ≤ ((6776507/2000000 : ℚ) : ℝ) := by
    have h := (log_br_877).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25458633/100000000) (δ := 263421/10000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_878 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (878 : ℕ) / 2)) - ((4568811/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13555293/4000000 : ℚ) : ℝ) ≤ Real.log (878 : ℕ) / 2 := by
    have h := (log_br_878).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (878 : ℕ) / 2 ≤ ((33888233/10000000 : ℚ) : ℝ) := by
    have h := (log_br_878).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1307331/12500000) (δ := 263421/10000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_879 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (879 : ℕ) / 2)) - ((9836697/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8473481/2500000 : ℚ) : ℝ) ≤ Real.log (879 : ℕ) / 2 := by
    have h := (log_br_879).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (879 : ℕ) / 2 ≤ ((67787849/20000000 : ℚ) : ℝ) := by
    have h := (log_br_879).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2262113/50000000) (δ := 263321/10000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_880 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (880 : ℕ) / 2)) - ((7111581/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67799219/20000000 : ℚ) : ℝ) ≤ Real.log (880 : ℕ) / 2 := by
    have h := (log_br_880).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (880 : ℕ) / 2 ≤ ((3389961/1000000 : ℚ) : ℝ) := by
    have h := (log_br_880).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3898261/20000000) (δ := 131641/5000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_881 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (881 : ℕ) / 2)) - ((383997/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4238161/1250000 : ℚ) : ℝ) ≤ Real.log (881 : ℕ) / 2 := by
    have h := (log_br_881).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (881 : ℕ) / 2 ≤ ((67810577/20000000 : ℚ) : ℝ) := by
    have h := (log_br_881).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8609989/25000000) (δ := 263321/10000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_882 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (882 : ℕ) / 2)) - ((-3931579/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((423887/125000 : ℚ) : ℝ) ≤ Real.log (882 : ℕ) / 2 := by
    have h := (log_br_882).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (882 : ℕ) / 2 ≤ ((67821921/20000000 : ℚ) : ℝ) := by
    have h := (log_br_882).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6171437/12500000) (δ := 263321/10000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_883 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (883 : ℕ) / 2)) - ((-4209227/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16958313/5000000 : ℚ) : ℝ) ≤ Real.log (883 : ℕ) / 2 := by
    have h := (log_br_883).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (883 : ℕ) / 2 ≤ ((67833253/20000000 : ℚ) : ℝ) := by
    have h := (log_br_883).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64287241/100000000) (δ := 263321/10000000000) 1053 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_884 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (884 : ℕ) / 2)) - ((-399867/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6784457/2000000 : ℚ) : ℝ) ≤ Real.log (884 : ℕ) / 2 := by
    have h := (log_br_884).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (884 : ℕ) / 2 ≤ ((67844571/20000000 : ℚ) : ℝ) := by
    have h := (log_br_884).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38947537/50000000) (δ := 263253/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_885 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (885 : ℕ) / 2)) - ((-2033169/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16963969/5000000 : ℚ) : ℝ) ≤ Real.log (885 : ℕ) / 2 := by
    have h := (log_br_885).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (885 : ℕ) / 2 ≤ ((67855877/20000000 : ℚ) : ℝ) := by
    have h := (log_br_885).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3938347/6250000) (δ := 5269/200000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_886 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (886 : ℕ) / 2)) - ((-3477491/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67867169/20000000 : ℚ) : ℝ) ≤ Real.log (886 : ℕ) / 2 := by
    have h := (log_br_886).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (886 : ℕ) / 2 ≤ ((6786717/2000000 : ℚ) : ℝ) := by
    have h := (log_br_886).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2407457/5000000) (δ := 263353/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_887 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (887 : ℕ) / 2)) - ((1182309/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67878449/20000000 : ℚ) : ℝ) ≤ Real.log (887 : ℕ) / 2 := by
    have h := (log_br_887).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (887 : ℕ) / 2 ≤ ((1357569/400000 : ℚ) : ℝ) := by
    have h := (log_br_887).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -416273/1250000) (δ := 263353/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_888 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (888 : ℕ) / 2)) - ((7392681/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67889717/20000000 : ℚ) : ℝ) ≤ Real.log (888 : ℕ) / 2 := by
    have h := (log_br_888).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (888 : ℕ) / 2 ≤ ((33944859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_888).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3694067/20000000) (δ := 263353/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_889 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (889 : ℕ) / 2)) - ((9893263/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16975243/5000000 : ℚ) : ℝ) ≤ Real.log (889 : ℕ) / 2 := by
    have h := (log_br_889).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (889 : ℕ) / 2 ≤ ((67900973/20000000 : ℚ) : ℝ) := by
    have h := (log_br_889).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1827971/50000000) (δ := 5269/200000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_890 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (890 : ℕ) / 2)) - ((9023291/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33956107/10000000 : ℚ) : ℝ) ≤ Real.log (890 : ℕ) / 2 := by
    have h := (log_br_890).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (890 : ℕ) / 2 ≤ ((13582443/4000000 : ℚ) : ℝ) := by
    have h := (log_br_890).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11141341/100000000) (δ := 263253/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_891 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (891 : ℕ) / 2)) - ((6361/12500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16980861/5000000 : ℚ) : ℝ) ≤ Real.log (891 : ℕ) / 2 := by
    have h := (log_br_891).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (891 : ℕ) / 2 ≤ ((13584689/4000000 : ℚ) : ℝ) := by
    have h := (log_br_891).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6480707/25000000) (δ := 5269/200000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_892 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (892 : ℕ) / 2)) - ((-113323/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67934661/20000000 : ℚ) : ℝ) ≤ Real.log (892 : ℕ) / 2 := by
    have h := (log_br_892).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (892 : ℕ) / 2 ≤ ((33967331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_892).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8137441/20000000) (δ := 263353/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_893 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (893 : ℕ) / 2)) - ((-3012311/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13589173/4000000 : ℚ) : ℝ) ≤ Real.log (893 : ℕ) / 2 := by
    have h := (log_br_893).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (893 : ℕ) / 2 ≤ ((33972933/10000000 : ℚ) : ℝ) := by
    have h := (log_br_893).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5543447/10000000) (δ := 263353/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_894 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (894 : ℕ) / 2)) - ((-9444251/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67957057/20000000 : ℚ) : ℝ) ≤ Real.log (894 : ℕ) / 2 := by
    have h := (log_br_894).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (894 : ℕ) / 2 ≤ ((33978529/10000000 : ℚ) : ℝ) := by
    have h := (log_br_894).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3508297/5000000) (δ := 263353/10000000000) 1053 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_895 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (895 : ℕ) / 2)) - ((-4839987/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67968237/20000000 : ℚ) : ℝ) ≤ Real.log (895 : ℕ) / 2 := by
    have h := (log_br_895).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (895 : ℕ) / 2 ≤ ((33984119/10000000 : ℚ) : ℝ) := by
    have h := (log_br_895).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36099009/50000000) (δ := 131639/5000000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_896 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (896 : ℕ) / 2)) - ((-6662597/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16994851/5000000 : ℚ) : ℝ) ≤ Real.log (896 : ℕ) / 2 := by
    have h := (log_br_896).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (896 : ℕ) / 2 ≤ ((13595881/4000000 : ℚ) : ℝ) := by
    have h := (log_br_896).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28749727/50000000) (δ := 10533/400000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_897 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (897 : ℕ) / 2)) - ((-707239/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33995279/10000000 : ℚ) : ℝ) ≤ Real.log (897 : ℕ) / 2 := by
    have h := (log_br_897).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (897 : ℕ) / 2 ≤ ((67990559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_897).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21409001/50000000) (δ := 131689/5000000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_898 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (898 : ℕ) / 2)) - ((2150947/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((680017/200000 : ℚ) : ℝ) ≤ Real.log (898 : ℕ) / 2 := by
    have h := (log_br_898).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (898 : ℕ) / 2 ≤ ((68001701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_898).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3519043/12500000) (δ := 10533/400000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_899 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (899 : ℕ) / 2)) - ((134009/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6801283/2000000 : ℚ) : ℝ) ≤ Real.log (899 : ℕ) / 2 := by
    have h := (log_br_899).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (899 : ℕ) / 2 ≤ ((68012831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_899).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6751241/50000000) (δ := 131689/5000000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_900 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (900 : ℕ) / 2)) - ((4994891/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68023947/20000000 : ℚ) : ℝ) ≤ Real.log (900 : ℕ) / 2 := by
    have h := (log_br_900).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (900 : ℕ) / 2 ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := (log_br_900).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 113027/10000000) (δ := 10537/400000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_901 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (901 : ℕ) / 2)) - ((8080929/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17008763/5000000 : ℚ) : ℝ) ≤ Real.log (901 : ℕ) / 2 := by
    have h := (log_br_901).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (901 : ℕ) / 2 ≤ ((68035053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_901).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7873613/50000000) (δ := 10533/400000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_902 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (902 : ℕ) / 2)) - ((1746673/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13609229/4000000 : ℚ) : ℝ) ≤ Real.log (902 : ℕ) / 2 := by
    have h := (log_br_902).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (902 : ℕ) / 2 ≤ ((34023073/10000000 : ℚ) : ℝ) := by
    have h := (log_br_902).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30348387/100000000) (δ := 131639/5000000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_903 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (903 : ℕ) / 2)) - ((-1122847/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722289/800000 : ℚ) : ℝ) ≤ Real.log (903 : ℕ) / 2 := by
    have h := (log_br_903).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (903 : ℕ) / 2 ≤ ((34028613/10000000 : ℚ) : ℝ) := by
    have h := (log_br_903).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44932437/100000000) (δ := 131639/5000000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_904 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (904 : ℕ) / 2)) - ((-723757/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68068293/20000000 : ℚ) : ℝ) ≤ Real.log (904 : ℕ) / 2 := by
    have h := (log_br_904).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (904 : ℕ) / 2 ≤ ((34034147/10000000 : ℚ) : ℝ) := by
    have h := (log_br_904).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14875173/25000000) (δ := 131639/5000000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_905 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (905 : ℕ) / 2)) - ((-9839391/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68079349/20000000 : ℚ) : ℝ) ≤ Real.log (905 : ℕ) / 2 := by
    have h := (log_br_905).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (905 : ℕ) / 2 ≤ ((1361587/400000 : ℚ) : ℝ) := by
    have h := (log_br_905).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2314161/3125000) (δ := 131639/5000000000) 1053 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_906 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (906 : ℕ) / 2)) - ((-9202803/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68090393/20000000 : ℚ) : ℝ) ≤ Real.log (906 : ℕ) / 2 := by
    have h := (log_br_906).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (906 : ℕ) / 2 ≤ ((34045197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_906).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8561227/12500000) (δ := 131703/5000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_907 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (907 : ℕ) / 2)) - ((-2773549/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4256339/1250000 : ℚ) : ℝ) ≤ Real.log (907 : ℕ) / 2 := by
    have h := (log_br_907).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (907 : ℕ) / 2 ≤ ((2724057/800000 : ℚ) : ℝ) := by
    have h := (log_br_907).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26985131/50000000) (δ := 131653/5000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_908 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (908 : ℕ) / 2)) - ((-78637/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68112443/20000000 : ℚ) : ℝ) ≤ Real.log (908 : ℕ) / 2 := by
    have h := (log_br_908).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (908 : ℕ) / 2 ≤ ((17028111/5000000 : ℚ) : ℝ) := by
    have h := (log_br_908).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39466503/100000000) (δ := 263297/10000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_909 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (909 : ℕ) / 2)) - ((1082049/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1362469/400000 : ℚ) : ℝ) ≤ Real.log (909 : ℕ) / 2 := by
    have h := (log_br_909).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (909 : ℕ) / 2 ≤ ((68123451/20000000 : ℚ) : ℝ) := by
    have h := (log_br_909).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24978539/100000000) (δ := 263397/10000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_910 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (910 : ℕ) / 2)) - ((182597/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13626889/4000000 : ℚ) : ℝ) ≤ Real.log (910 : ℕ) / 2 := by
    have h := (log_br_910).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (910 : ℕ) / 2 ≤ ((34067223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_910).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10506371/100000000) (δ := 131703/5000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_911 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (911 : ℕ) / 2)) - ((9875439/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17036357/5000000 : ℚ) : ℝ) ≤ Real.log (911 : ℕ) / 2 := by
    have h := (log_br_911).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (911 : ℕ) / 2 ≤ ((68145429/20000000 : ℚ) : ℝ) := by
    have h := (log_br_911).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3950003/100000000) (δ := 131653/5000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_912 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (912 : ℕ) / 2)) - ((3707063/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68156399/20000000 : ℚ) : ℝ) ≤ Real.log (912 : ℕ) / 2 := by
    have h := (log_br_912).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (912 : ℕ) / 2 ≤ ((170391/50000 : ℚ) : ℝ) := by
    have h := (log_br_912).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9195291/50000000) (δ := 263297/10000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_913 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (913 : ℕ) / 2)) - ((2553229/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34083679/10000000 : ℚ) : ℝ) ≤ Real.log (913 : ℕ) / 2 := by
    have h := (log_br_913).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (913 : ℕ) / 2 ≤ ((68167359/20000000 : ℚ) : ℝ) := by
    have h := (log_br_913).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16407683/50000000) (δ := 263397/10000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_914 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (914 : ℕ) / 2)) - ((-782091/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13635661/4000000 : ℚ) : ℝ) ≤ Real.log (914 : ℕ) / 2 := by
    have h := (log_br_914).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (914 : ℕ) / 2 ≤ ((34089153/10000000 : ℚ) : ℝ) := by
    have h := (log_br_914).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23612177/50000000) (δ := 131703/5000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_915 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (915 : ℕ) / 2)) - ((-194881/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1704731/500000 : ℚ) : ℝ) ≤ Real.log (915 : ℕ) / 2 := by
    have h := (log_br_915).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (915 : ℕ) / 2 ≤ ((68189241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_915).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15404387/25000000) (δ := 131653/5000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_916 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (916 : ℕ) / 2)) - ((-4974117/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68200163/20000000 : ℚ) : ℝ) ≤ Real.log (916 : ℕ) / 2 := by
    have h := (log_br_916).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (916 : ℕ) / 2 ≤ ((17050041/5000000 : ℚ) : ℝ) := by
    have h := (log_br_916).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75994947/100000000) (δ := 263297/10000000000) 1053 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_917 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (917 : ℕ) / 2)) - ((-4451781/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34105537/10000000 : ℚ) : ℝ) ≤ Real.log (917 : ℕ) / 2 := by
    have h := (log_br_917).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (917 : ℕ) / 2 ≤ ((2728443/800000 : ℚ) : ℝ) := by
    have h := (log_br_917).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33361541/50000000) (δ := 263269/10000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_918 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (918 : ℕ) / 2)) - ((-200241/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68221973/20000000 : ℚ) : ℝ) ≤ Real.log (918 : ℕ) / 2 := by
    have h := (log_br_918).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (918 : ℕ) / 2 ≤ ((34110987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_918).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -52377273/100000000) (δ := 263369/10000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_919 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (919 : ℕ) / 2)) - ((489391/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68232861/20000000 : ℚ) : ℝ) ≤ Real.log (919 : ℕ) / 2 := by
    have h := (log_br_919).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (919 : ℕ) / 2 ≤ ((34116431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_919).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38045943/100000000) (δ := 263369/10000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_920 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (920 : ℕ) / 2)) - ((232911/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8530467/2500000 : ℚ) : ℝ) ≤ Real.log (920 : ℕ) / 2 := by
    have h := (log_br_920).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (920 : ℕ) / 2 ≤ ((68243737/20000000 : ℚ) : ℝ) := by
    have h := (log_br_920).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -949269/4000000) (δ := 131717/5000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_921 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (921 : ℕ) / 2)) - ((9296703/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((341273/100000 : ℚ) : ℝ) ≤ Real.log (921 : ℕ) / 2 := by
    have h := (log_br_921).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (921 : ℕ) / 2 ≤ ((68254601/20000000 : ℚ) : ℝ) := by
    have h := (log_br_921).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1886397/20000000) (δ := 131717/5000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_922 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (922 : ℕ) / 2)) - ((4906129/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17066363/5000000 : ℚ) : ℝ) ≤ Real.log (922 : ℕ) / 2 := by
    have h := (log_br_922).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (922 : ℕ) / 2 ≤ ((68265453/20000000 : ℚ) : ℝ) := by
    have h := (log_br_922).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 121299/2500000) (δ := 131717/5000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_923 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (923 : ℕ) / 2)) - ((3607589/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17069073/5000000 : ℚ) : ℝ) ≤ Real.log (923 : ℕ) / 2 := by
    have h := (log_br_923).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (923 : ℕ) / 2 ≤ ((68276293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_923).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1912011/10000000) (δ := 131717/5000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_924 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (924 : ℕ) / 2)) - ((2337159/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((853589/250000 : ℚ) : ℝ) ≤ Real.log (924 : ℕ) / 2 := by
    have h := (log_br_924).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (924 : ℕ) / 2 ≤ ((68287121/20000000 : ℚ) : ℝ) := by
    have h := (log_br_924).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6674493/20000000) (δ := 131717/5000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_925 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (925 : ℕ) / 2)) - ((-3274631/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68297937/20000000 : ℚ) : ℝ) ≤ Real.log (925 : ℕ) / 2 := by
    have h := (log_br_925).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (925 : ℕ) / 2 ≤ ((34148969/10000000 : ℚ) : ℝ) := by
    have h := (log_br_925).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23805171/50000000) (δ := 263369/10000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_926 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (926 : ℕ) / 2)) - ((-7848789/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34154371/10000000 : ℚ) : ℝ) ≤ Real.log (926 : ℕ) / 2 := by
    have h := (log_br_926).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (926 : ℕ) / 2 ≤ ((68308743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_926).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61832423/100000000) (δ := 263269/10000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_927 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (927 : ℕ) / 2)) - ((-9949997/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13663907/4000000 : ℚ) : ℝ) ≤ Real.log (927 : ℕ) / 2 := by
    have h := (log_br_927).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (927 : ℕ) / 2 ≤ ((4269971/1250000 : ℚ) : ℝ) := by
    have h := (log_br_927).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76038709/100000000) (δ := 131667/5000000000) 1053 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_928 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (928 : ℕ) / 2)) - ((-5579/6250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68330317/20000000 : ℚ) : ℝ) ≤ Real.log (928 : ℕ) / 2 := by
    have h := (log_br_928).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (928 : ℕ) / 2 ≤ ((34165159/10000000 : ℚ) : ℝ) := by
    have h := (log_br_928).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16712279/25000000) (δ := 131631/5000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_929 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (929 : ℕ) / 2)) - ((-5108109/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68341087/20000000 : ℚ) : ℝ) ≤ Real.log (929 : ℕ) / 2 := by
    have h := (log_br_929).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (929 : ℕ) / 2 ≤ ((2135659/625000 : ℚ) : ℝ) := by
    have h := (log_br_929).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -52673103/100000000) (δ := 263441/10000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_930 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (930 : ℕ) / 2)) - ((302763/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13670369/4000000 : ℚ) : ℝ) ≤ Real.log (930 : ℕ) / 2 := by
    have h := (log_br_930).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (930 : ℕ) / 2 ≤ ((34175923/10000000 : ℚ) : ℝ) := by
    have h := (log_br_930).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19256443/50000000) (δ := 131631/5000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_931 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (931 : ℕ) / 2)) - ((140357/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2136331/625000 : ℚ) : ℝ) ≤ Real.log (931 : ℕ) / 2 := by
    have h := (log_br_931).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (931 : ℕ) / 2 ≤ ((68362593/20000000 : ℚ) : ℝ) := by
    have h := (log_br_931).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24367147/100000000) (δ := 263341/10000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_932 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (932 : ℕ) / 2)) - ((9173457/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4273333/1250000 : ℚ) : ℝ) ≤ Real.log (932 : ℕ) / 2 := by
    have h := (log_br_932).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (932 : ℕ) / 2 ≤ ((68373329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_932).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10235887/100000000) (δ := 263341/10000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_933 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (933 : ℕ) / 2)) - ((1234979/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17096013/5000000 : ℚ) : ℝ) ≤ Real.log (933 : ℕ) / 2 := by
    have h := (log_br_933).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (933 : ℕ) / 2 ≤ ((68384053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_933).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1939789/50000000) (δ := 263341/10000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_934 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (934 : ℕ) / 2)) - ((940441/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17098691/5000000 : ℚ) : ℝ) ≤ Real.log (934 : ℕ) / 2 := by
    have h := (log_br_934).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (934 : ℕ) / 2 ≤ ((13678953/4000000 : ℚ) : ℝ) := by
    have h := (log_br_934).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1123703/6250000) (δ := 263341/10000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_935 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (935 : ℕ) / 2)) - ((2842449/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13681093/4000000 : ℚ) : ℝ) ≤ Real.log (935 : ℕ) / 2 := by
    have h := (log_br_935).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (935 : ℕ) / 2 ≤ ((34202733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_935).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32064439/100000000) (δ := 131631/5000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_936 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (936 : ℕ) / 2)) - ((-1355603/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34208077/10000000 : ℚ) : ℝ) ≤ Real.log (936 : ℕ) / 2 := by
    have h := (log_br_936).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (936 : ℕ) / 2 ≤ ((13683231/4000000 : ℚ) : ℝ) := by
    have h := (log_br_936).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9226767/20000000) (δ := 131681/5000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_937 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (937 : ℕ) / 2)) - ((-296989/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4276677/1250000 : ℚ) : ℝ) ≤ Real.log (937 : ℕ) / 2 := by
    have h := (log_br_937).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (937 : ℕ) / 2 ≤ ((68426833/20000000 : ℚ) : ℝ) := by
    have h := (log_br_937).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60188753/100000000) (δ := 263341/10000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_938 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (938 : ℕ) / 2)) - ((-2462929/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68437499/20000000 : ℚ) : ℝ) ≤ Real.log (938 : ℕ) / 2 := by
    have h := (log_br_938).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (938 : ℕ) / 2 ≤ ((219/64 : ℚ) : ℝ) := by
    have h := (log_br_938).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9278649/12500000) (δ := 263441/10000000000) 1053 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_939 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (939 : ℕ) / 2)) - ((-9254553/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34224077/10000000 : ℚ) : ℝ) ≤ Real.log (939 : ℕ) / 2 := by
    have h := (log_br_939).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (939 : ℕ) / 2 ≤ ((13689631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_939).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -68825797/100000000) (δ := 65853/2500000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_940 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (940 : ℕ) / 2)) - ((-5825227/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34229399/10000000 : ℚ) : ℝ) ≤ Real.log (940 : ℕ) / 2 := by
    have h := (log_br_940).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (940 : ℕ) / 2 ≤ ((68458799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_940).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3425977/6250000) (δ := 65853/2500000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_941 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (941 : ℕ) / 2)) - ((-309809/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68469431/20000000 : ℚ) : ℝ) ≤ Real.log (941 : ℕ) / 2 := by
    have h := (log_br_941).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (941 : ℕ) / 2 ≤ ((8558679/2500000 : ℚ) : ℝ) := by
    have h := (log_br_941).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20409973/50000000) (δ := 16457/625000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_942 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (942 : ℕ) / 2)) - ((4769613/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17120013/5000000 : ℚ) : ℝ) ≤ Real.log (942 : ℕ) / 2 := by
    have h := (log_br_942).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (942 : ℕ) / 2 ≤ ((68480053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_942).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5368011/20000000) (δ := 263291/10000000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_943 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (943 : ℕ) / 2)) - ((4351499/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34245331/10000000 : ℚ) : ℝ) ≤ Real.log (943 : ℕ) / 2 := by
    have h := (log_br_943).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (943 : ℕ) / 2 ≤ ((68490663/20000000 : ℚ) : ℝ) := by
    have h := (log_br_943).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6437321/50000000) (δ := 65853/2500000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_944 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (944 : ℕ) / 2)) - ((4995367/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68501261/20000000 : ℚ) : ℝ) ≤ Real.log (944 : ℕ) / 2 := by
    have h := (log_br_944).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (944 : ℕ) / 2 ≤ ((34250631/10000000 : ℚ) : ℝ) := by
    have h := (log_br_944).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1076291/100000000) (δ := 263391/10000000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_945 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (945 : ℕ) / 2)) - ((2062619/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68511849/20000000 : ℚ) : ℝ) ≤ Real.log (945 : ℕ) / 2 := by
    have h := (log_br_945).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (945 : ℕ) / 2 ≤ ((1370237/400000 : ℚ) : ℝ) := by
    have h := (log_br_945).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7506373/50000000) (δ := 263391/10000000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_946 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (946 : ℕ) / 2)) - ((4017803/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2740897/800000 : ℚ) : ℝ) ≤ Real.log (946 : ℕ) / 2 := by
    have h := (log_br_946).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (946 : ℕ) / 2 ≤ ((34261213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_946).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14466703/50000000) (δ := 263391/10000000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_947 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (947 : ℕ) / 2)) - ((-56921/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6853299/2000000 : ℚ) : ℝ) ≤ Real.log (947 : ℕ) / 2 := by
    have h := (log_br_947).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (947 : ℕ) / 2 ≤ ((68532991/20000000 : ℚ) : ℝ) := by
    have h := (log_br_947).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10709897/25000000) (δ := 65853/2500000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_948 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (948 : ℕ) / 2)) - ((-3215379/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13708709/4000000 : ℚ) : ℝ) ≤ Real.log (948 : ℕ) / 2 := by
    have h := (log_br_948).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (948 : ℕ) / 2 ≤ ((34271773/10000000 : ℚ) : ℝ) := by
    have h := (log_br_948).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28366303/50000000) (δ := 263391/10000000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_949 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (949 : ℕ) / 2)) - ((-4750481/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68554087/20000000 : ℚ) : ℝ) ≤ Real.log (949 : ℕ) / 2 := by
    have h := (log_br_949).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (949 : ℕ) / 2 ≤ ((8569261/2500000 : ℚ) : ℝ) := by
    have h := (log_br_949).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35304257/50000000) (δ := 16457/625000000) 1053 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_950 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (950 : ℕ) / 2)) - ((-4859931/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68564619/20000000 : ℚ) : ℝ) ≤ Real.log (950 : ℕ) / 2 := by
    have h := (log_br_950).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (950 : ℕ) / 2 ≤ ((3428231/1000000 : ℚ) : ℝ) := by
    have h := (log_br_950).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36304187/50000000) (δ := 263319/10000000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_951 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (951 : ℕ) / 2)) - ((-7030007/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3428757/1000000 : ℚ) : ℝ) ≤ Real.log (951 : ℕ) / 2 := by
    have h := (log_br_951).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (951 : ℕ) / 2 ≤ ((68575141/20000000 : ℚ) : ℝ) := by
    have h := (log_br_951).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14690027/25000000) (δ := 263419/10000000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_952 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (952 : ℕ) / 2)) - ((-224331/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1371713/400000 : ℚ) : ℝ) ≤ Real.log (952 : ℕ) / 2 := by
    have h := (log_br_952).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (952 : ℕ) / 2 ≤ ((68585651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_952).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -561579/1250000) (δ := 65821/2500000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_953 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (953 : ℕ) / 2)) - ((3207449/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68596149/20000000 : ℚ) : ℝ) ≤ Real.log (953 : ℕ) / 2 := by
    have h := (log_br_953).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (953 : ℕ) / 2 ≤ ((1371923/400000 : ℚ) : ℝ) := by
    have h := (log_br_953).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31107011/100000000) (δ := 32923/1250000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_954 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (954 : ℕ) / 2)) - ((7698821/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17151659/5000000 : ℚ) : ℝ) ≤ Real.log (954 : ℕ) / 2 := by
    have h := (log_br_954).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (954 : ℕ) / 2 ≤ ((68606637/20000000 : ℚ) : ℝ) := by
    have h := (log_br_954).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8651749/50000000) (δ := 263419/10000000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_955 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (955 : ℕ) / 2)) - ((396057/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68617113/20000000 : ℚ) : ℝ) ≤ Real.log (955 : ℕ) / 2 := by
    have h := (log_br_955).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (955 : ℕ) / 2 ≤ ((34308557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_955).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1756573/50000000) (δ := 32923/1250000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_956 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (956 : ℕ) / 2)) - ((4584589/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68627579/20000000 : ℚ) : ℝ) ≤ Real.log (956 : ℕ) / 2 := by
    have h := (log_br_956).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (956 : ℕ) / 2 ≤ ((3431379/1000000 : ℚ) : ℝ) := by
    have h := (log_br_956).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5131363/50000000) (δ := 263319/10000000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_957 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (957 : ℕ) / 2)) - ((229109/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68638033/20000000 : ℚ) : ℝ) ≤ Real.log (957 : ℕ) / 2 := by
    have h := (log_br_957).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (957 : ℕ) / 2 ≤ ((34319017/10000000 : ℚ) : ℝ) := by
    have h := (log_br_957).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6005701/25000000) (δ := 32923/1250000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_958 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (958 : ℕ) / 2)) - ((149929/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68648477/20000000 : ℚ) : ℝ) ≤ Real.log (958 : ℕ) / 2 := by
    have h := (log_br_958).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (958 : ℕ) / 2 ≤ ((34324239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_958).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37769719/100000000) (δ := 32923/1250000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_959 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (959 : ℕ) / 2)) - ((-587499/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6865891/2000000 : ℚ) : ℝ) ≤ Real.log (959 : ℕ) / 2 := by
    have h := (log_br_959).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (959 : ℕ) / 2 ≤ ((68658911/20000000 : ℚ) : ℝ) := by
    have h := (log_br_959).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10300431/20000000) (δ := 65821/2500000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_960 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (960 : ℕ) / 2)) - ((-4306971/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17167333/5000000 : ℚ) : ℝ) ≤ Real.log (960 : ℕ) / 2 := by
    have h := (log_br_960).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (960 : ℕ) / 2 ≤ ((68669333/20000000 : ℚ) : ℝ) := by
    have h := (log_br_960).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4076257/6250000) (δ := 263419/10000000000) 1053 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_961 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (961 : ℕ) / 2)) - ((-4999407/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/312500 : ℚ) : ℝ) ≤ Real.log (961 : ℕ) / 2 := by
    have h := (log_br_961).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (961 : ℕ) / 2 ≤ ((13735949/4000000 : ℚ) : ℝ) := by
    have h := (log_br_961).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3126189/4000000) (δ := 65839/2500000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_962 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (962 : ℕ) / 2)) - ((-8456771/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2146567/625000 : ℚ) : ℝ) ≤ Real.log (962 : ℕ) / 2 := by
    have h := (log_br_962).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (962 : ℕ) / 2 ≤ ((13738029/4000000 : ℚ) : ℝ) := by
    have h := (log_br_962).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2578629/4000000) (δ := 65839/2500000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_963 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (963 : ℕ) / 2)) - ((-4446641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34350267/10000000 : ℚ) : ℝ) ≤ Real.log (963 : ℕ) / 2 := by
    have h := (log_br_963).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (963 : ℕ) / 2 ≤ ((13740107/4000000 : ℚ) : ℝ) := by
    have h := (log_br_963).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -198398/390625) (δ := 263347/10000000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_964 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (964 : ℕ) / 2)) - ((42749/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((268402/78125 : ℚ) : ℝ) ≤ Real.log (964 : ℕ) / 2 := by
    have h := (log_br_964).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (964 : ℕ) / 2 ≤ ((68710913/20000000 : ℚ) : ℝ) := by
    have h := (log_br_964).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7425969/20000000) (δ := 65839/2500000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_965 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (965 : ℕ) / 2)) - ((2951903/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68721281/20000000 : ℚ) : ℝ) ≤ Real.log (965 : ℕ) / 2 := by
    have h := (log_br_965).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (965 : ℕ) / 2 ≤ ((34360641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_965).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23481649/100000000) (δ := 32907/1250000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_966 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (966 : ℕ) / 2)) - ((369357/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34365819/10000000 : ℚ) : ℝ) ≤ Real.log (966 : ℕ) / 2 := by
    have h := (log_br_966).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (966 : ℕ) / 2 ≤ ((68731639/20000000 : ℚ) : ℝ) := by
    have h := (log_br_966).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -307789/3125000) (δ := 263347/10000000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_967 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (967 : ℕ) / 2)) - ((77239/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2148187/625000 : ℚ) : ℝ) ≤ Real.log (967 : ℕ) / 2 := by
    have h := (log_br_967).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (967 : ℕ) / 2 ≤ ((13748397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_967).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 150747/4000000) (δ := 65839/2500000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_968 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (968 : ℕ) / 2)) - ((3840469/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((214851/62500 : ℚ) : ℝ) ≤ Real.log (968 : ℕ) / 2 := by
    have h := (log_br_968).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (968 : ℕ) / 2 ≤ ((68752321/20000000 : ℚ) : ℝ) := by
    have h := (log_br_968).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3474687/20000000) (δ := 65839/2500000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_969 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (969 : ℕ) / 2)) - ((3261189/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34381323/10000000 : ℚ) : ℝ) ≤ Real.log (969 : ℕ) / 2 := by
    have h := (log_br_969).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (969 : ℕ) / 2 ≤ ((68762647/20000000 : ℚ) : ℝ) := by
    have h := (log_br_969).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3870629/12500000) (δ := 263347/10000000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_970 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (970 : ℕ) / 2)) - ((-418557/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((429831/125000 : ℚ) : ℝ) ≤ Real.log (970 : ℕ) / 2 := by
    have h := (log_br_970).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (970 : ℕ) / 2 ≤ ((68772961/20000000 : ℚ) : ℝ) := by
    have h := (log_br_970).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8908167/20000000) (δ := 65839/2500000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_971 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (971 : ℕ) / 2)) - ((-6840807/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2149477/625000 : ℚ) : ℝ) ≤ Real.log (971 : ℕ) / 2 := by
    have h := (log_br_971).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (971 : ℕ) / 2 ≤ ((13756653/4000000 : ℚ) : ℝ) := by
    have h := (log_br_971).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2324139/4000000) (δ := 65839/2500000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_972 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (972 : ℕ) / 2)) - ((-4811481/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34396779/10000000 : ℚ) : ℝ) ≤ Real.log (972 : ℕ) / 2 := by
    have h := (log_br_972).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (972 : ℕ) / 2 ≤ ((68793559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_972).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8956619/12500000) (δ := 263347/10000000000) 1053 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_973 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (973 : ℕ) / 2)) - ((-2412159/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53753/15625 : ℚ) : ℝ) ≤ Real.log (973 : ℕ) / 2 := by
    have h := (log_br_973).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (973 : ℕ) / 2 ≤ ((68803841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_973).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35946499/50000000) (δ := 10531/400000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_974 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (974 : ℕ) / 2)) - ((-1383703/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68814113/20000000 : ℚ) : ℝ) ≤ Real.log (974 : ℕ) / 2 := by
    have h := (log_br_974).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (974 : ℕ) / 2 ≤ ((34407057/10000000 : ℚ) : ℝ) := by
    have h := (log_br_974).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29185581/50000000) (δ := 2107/80000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_975 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (975 : ℕ) / 2)) - ((-2219447/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34412187/10000000 : ℚ) : ℝ) ≤ Real.log (975 : ℕ) / 2 := by
    have h := (log_br_975).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (975 : ℕ) / 2 ≤ ((110119/32000 : ℚ) : ℝ) := by
    have h := (log_br_975).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -280407/625000) (δ := 65857/2500000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_976 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (976 : ℕ) / 2)) - ((97087/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((550677/160000 : ℚ) : ℝ) ≤ Real.log (976 : ℕ) / 2 := by
    have h := (log_br_976).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (976 : ℕ) / 2 ≤ ((34417313/10000000 : ℚ) : ℝ) := by
    have h := (log_br_976).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15686121/50000000) (δ := 2107/80000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_977 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (977 : ℕ) / 2)) - ((1509267/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34422433/10000000 : ℚ) : ℝ) ≤ Real.log (977 : ℕ) / 2 := by
    have h := (log_br_977).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (977 : ℕ) / 2 ≤ ((68844867/20000000 : ℚ) : ℝ) := by
    have h := (log_br_977).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -715701/4000000) (δ := 65857/2500000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_978 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (978 : ℕ) / 2)) - ((4921801/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8606887/2500000 : ℚ) : ℝ) ≤ Real.log (978 : ℕ) / 2 := by
    have h := (log_br_978).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (978 : ℕ) / 2 ≤ ((68855097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_978).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -553411/12500000) (δ := 10531/400000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_979 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (979 : ℕ) / 2)) - ((9355471/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17216329/5000000 : ℚ) : ℝ) ≤ Real.log (979 : ℕ) / 2 := by
    have h := (log_br_979).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (979 : ℕ) / 2 ≤ ((68865317/20000000 : ℚ) : ℝ) := by
    have h := (log_br_979).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9024787/100000000) (δ := 10531/400000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_980 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (980 : ℕ) / 2)) - ((6227879/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2755021/800000 : ℚ) : ℝ) ≤ Real.log (980 : ℕ) / 2 := by
    have h := (log_br_980).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (980 : ℕ) / 2 ≤ ((34437763/10000000 : ℚ) : ℝ) := by
    have h := (log_br_980).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22462383/100000000) (δ := 2107/80000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_981 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (981 : ℕ) / 2)) - ((134911/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17221431/5000000 : ℚ) : ℝ) ≤ Real.log (981 : ℕ) / 2 := by
    have h := (log_br_981).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (981 : ℕ) / 2 ≤ ((2755429/800000 : ℚ) : ℝ) := by
    have h := (log_br_981).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35886817/100000000) (δ := 10531/400000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_982 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (982 : ℕ) / 2)) - ((-3904563/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68895913/20000000 : ℚ) : ℝ) ≤ Real.log (982 : ℕ) / 2 := by
    have h := (log_br_982).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (982 : ℕ) / 2 ≤ ((34447957/10000000 : ℚ) : ℝ) := by
    have h := (log_br_982).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6162261/12500000) (δ := 2107/80000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_983 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (983 : ℕ) / 2)) - ((-1611569/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68906091/20000000 : ℚ) : ℝ) ≤ Real.log (983 : ℕ) / 2 := by
    have h := (log_br_983).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (983 : ℕ) / 2 ≤ ((17226523/5000000 : ℚ) : ℝ) := by
    have h := (log_br_983).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 62694881/100000000) (δ := 8229/312500000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_984 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (984 : ℕ) / 2)) - ((-9951523/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34458129/10000000 : ℚ) : ℝ) ≤ Real.log (984 : ℕ) / 2 := by
    have h := (log_br_984).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (984 : ℕ) / 2 ≤ ((68916259/20000000 : ℚ) : ℝ) := by
    have h := (log_br_984).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15215439/20000000) (δ := 65857/2500000000) 1053 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_985 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (985 : ℕ) / 2)) - ((-2265789/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4307901/1250000 : ℚ) : ℝ) ≤ Real.log (985 : ℕ) / 2 := by
    have h := (log_br_985).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (985 : ℕ) / 2 ≤ ((68926417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_985).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67631971/100000000) (δ := 263403/10000000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_986 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (986 : ℕ) / 2)) - ((-564843/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68936563/20000000 : ℚ) : ℝ) ≤ Real.log (986 : ℕ) / 2 := by
    have h := (log_br_986).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (986 : ℕ) / 2 ≤ ((17234141/5000000 : ℚ) : ℝ) := by
    have h := (log_br_986).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27137991/50000000) (δ := 263303/10000000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_987 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (987 : ℕ) / 2)) - ((-83101/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((689467/200000 : ℚ) : ℝ) ≤ Real.log (987 : ℕ) / 2 := by
    have h := (log_br_987).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (987 : ℕ) / 2 ≤ ((68946701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_987).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10233289/25000000) (δ := 263403/10000000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_988 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (988 : ℕ) / 2)) - ((4498559/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34478413/10000000 : ℚ) : ℝ) ≤ Real.log (988 : ℕ) / 2 := by
    have h := (log_br_988).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (988 : ℕ) / 2 ≤ ((68956827/20000000 : ℚ) : ℝ) := by
    have h := (log_br_988).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3450601/12500000) (δ := 2633/100000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_989 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (989 : ℕ) / 2)) - ((8410731/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68966943/20000000 : ℚ) : ℝ) ≤ Real.log (989 : ℕ) / 2 := by
    have h := (log_br_989).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (989 : ℕ) / 2 ≤ ((2155217/625000 : ℚ) : ℝ) := by
    have h := (log_br_989).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14288307/100000000) (δ := 263303/10000000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_990 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (990 : ℕ) / 2)) - ((9992219/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68977049/20000000 : ℚ) : ℝ) ≤ Real.log (990 : ℕ) / 2 := by
    have h := (log_br_990).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (990 : ℕ) / 2 ≤ ((1379541/400000 : ℚ) : ℝ) := by
    have h := (log_br_990).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -246571/25000000) (δ := 1317/50000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_991 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (991 : ℕ) / 2)) - ((2203353/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13797429/4000000 : ℚ) : ℝ) ≤ Real.log (991 : ℕ) / 2 := by
    have h := (log_br_991).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (991 : ℕ) / 2 ≤ ((34493573/10000000 : ℚ) : ℝ) := by
    have h := (log_br_991).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 768911/6250000) (δ := 1317/50000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_992 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (992 : ℕ) / 2)) - ((1041391/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68997231/20000000 : ℚ) : ℝ) ≤ Real.log (992 : ℕ) / 2 := by
    have h := (log_br_992).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (992 : ℕ) / 2 ≤ ((4312327/1250000 : ℚ) : ℝ) := by
    have h := (log_br_992).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25578273/100000000) (δ := 263303/10000000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_993 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (993 : ℕ) / 2)) - ((86079/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34503653/10000000 : ℚ) : ℝ) ≤ Real.log (993 : ℕ) / 2 := by
    have h := (log_br_993).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (993 : ℕ) / 2 ≤ ((69007307/20000000 : ℚ) : ℝ) := by
    have h := (log_br_993).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9709873/25000000) (δ := 2633/100000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_994 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (994 : ℕ) / 2)) - ((-2452913/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17254343/5000000 : ℚ) : ℝ) ≤ Real.log (994 : ℕ) / 2 := by
    have h := (log_br_994).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (994 : ℕ) / 2 ≤ ((69017373/20000000 : ℚ) : ℝ) := by
    have h := (log_br_994).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1627777/3125000) (δ := 263403/10000000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_995 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (995 : ℕ) / 2)) - ((-4317463/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69027427/20000000 : ℚ) : ℝ) ≤ Real.log (995 : ℕ) / 2 := by
    have h := (log_br_995).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (995 : ℕ) / 2 ≤ ((17256857/5000000 : ℚ) : ℝ) := by
    have h := (log_br_995).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32661879/50000000) (δ := 263303/10000000000) 1053 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_996 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (996 : ℕ) / 2)) - ((-1 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157421/625000 : ℚ) : ℝ) ≤ Real.log (996 : ℕ) / 2 := by
    have h := (log_br_996).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (996 : ℕ) / 2 ≤ ((69037473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_996).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -78534143/100000000) (δ := 263371/10000000000) 1053 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_997 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (997 : ℕ) / 2)) - ((-8635293/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69047507/20000000 : ℚ) : ℝ) ≤ Real.log (997 : ℕ) / 2 := by
    have h := (log_br_997).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (997 : ℕ) / 2 ≤ ((17261877/5000000 : ℚ) : ℝ) := by
    have h := (log_br_997).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2613023/4000000) (δ := 32929/1250000000) 1053 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_998 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (998 : ℕ) / 2)) - ((-615027/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17264383/5000000 : ℚ) : ℝ) ≤ Real.log (998 : ℕ) / 2 := by
    have h := (log_br_998).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (998 : ℕ) / 2 ≤ ((69057533/20000000 : ℚ) : ℝ) := by
    have h := (log_br_998).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6516271/12500000) (δ := 263371/10000000000) 1053 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_999 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (999 : ℕ) / 2)) - ((12879/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69067547/20000000 : ℚ) : ℝ) ≤ Real.log (999 : ℕ) / 2 := by
    have h := (log_br_999).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (999 : ℕ) / 2 ≤ ((17266887/5000000 : ℚ) : ℝ) := by
    have h := (log_br_999).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1557917/4000000) (δ := 32929/1250000000) 1053 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1053o2_br_1000 :
    |Real.cos (((1053 : ℕ) : ℝ) * (Real.log (1000 : ℕ) / 2)) - ((2569147/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4317347/1250000 : ℚ) : ℝ) ≤ Real.log (1000 : ℕ) / 2 := by
    have h := (log_br_1000).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (1000 : ℕ) / 2 ≤ ((69077553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_1000).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25778843/100000000) (δ := 263371/10000000000) 1053 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos1053o2_br_1000
end AxiomAudit
