import RequestProject.DVPCosSinEval
import RequestProject.DVPLog200Table
import RequestProject.DVPLog250Table
import RequestProject.DVPLog500Table
import RequestProject.DVPLog1000Table

/-!
# The cosine table at `t = 1269/2` (rung-634.5; halved brackets, N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos1269o2_br_2 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (2 : ℕ) / 2)) - ((9997773/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (2 : ℕ) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -527621/100000000) (δ := 4959/156250000) 1269 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_3 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (3 : ℕ) / 2)) - ((9344459/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log (3 : ℕ) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (3 : ℕ) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2275603/25000000) (δ := 79333/2500000000) 1269 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_4 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (4 : ℕ) / 2)) - ((4995553/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log (4 : ℕ) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (4 : ℕ) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65903/6250000) (δ := 317353/10000000000) 1269 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_5 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (5 : ℕ) / 2)) - ((-9854547/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log (5 : ℕ) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (5 : ℕ) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14854129/20000000) (δ := 317299/10000000000) 1269 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_6 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (6 : ℕ) / 2)) - ((9267347/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log (6 : ℕ) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (6 : ℕ) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9629239/100000000) (δ := 317397/10000000000) 1269 181
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_7 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (7 : ℕ) / 2)) - ((-4997097/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log (7 : ℕ) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (7 : ℕ) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77687883/100000000) (δ := 63489/2000000000) 1269 197
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_8 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (8 : ℕ) / 2)) - ((9980003/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log (8 : ℕ) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (8 : ℕ) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -395319/25000000) (δ := 79331/2500000000) 1269 210
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_9 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (9 : ℕ) / 2)) - ((3731997/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log (9 : ℕ) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (9 : ℕ) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1820403/10000000) (δ := 62/1953125) 1269 222
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_10 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (10 : ℕ) / 2)) - ((-9888263/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log (10 : ℕ) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (10 : ℕ) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74799059/100000000) (δ := 317373/10000000000) 1269 233
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_11 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (11 : ℕ) / 2)) - ((1189741/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log (11 : ℕ) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (11 : ℕ) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4668459/20000000) (δ := 4959/156250000) 1269 242
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_12 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (12 : ℕ) / 2)) - ((229653/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log (12 : ℕ) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (12 : ℕ) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10156067/100000000) (δ := 317281/10000000000) 1269 251
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_13 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (13 : ℕ) / 2)) - ((397341/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log (13 : ℕ) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (13 : ℕ) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14421/500000) (δ := 158703/5000000000) 1269 259
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_14 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (14 : ℕ) / 2)) - ((-4999577/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log (14 : ℕ) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (14 : ℕ) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -78214711/100000000) (δ := 317271/10000000000) 1269 267
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_15 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (15 : ℕ) / 2)) - ((-9813761/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log (15 : ℕ) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (15 : ℕ) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73707369/100000000) (δ := 317301/10000000000) 1269 273
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_16 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (16 : ℕ) / 2)) - ((2491117/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log (16 : ℕ) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (16 : ℕ) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2108103/100000000) (δ := 79351/2500000000) 1269 280
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_17 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (17 : ℕ) / 2)) - ((121213/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log (17 : ℕ) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (17 : ℕ) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8535909/50000000) (δ := 79317/2500000000) 1269 286
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_18 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (18 : ℕ) / 2)) - ((3661053/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log (18 : ℕ) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (18 : ℕ) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9365429/50000000) (δ := 158633/5000000000) 1269 292
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_19 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (19 : ℕ) / 2)) - ((-5393637/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log (19 : ℕ) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (19 : ℕ) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53511939/100000000) (δ := 12697/400000000) 1269 297
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_20 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (20 : ℕ) / 2)) - ((-9917479/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log (20 : ℕ) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (20 : ℕ) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37662943/50000000) (δ := 79339/2500000000) 1269 303
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_21 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (21 : ℕ) / 2)) - ((-591279/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log (21 : ℕ) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (21 : ℕ) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70290131/100000000) (δ := 317443/10000000000) 1269 307
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_22 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (22 : ℕ) / 2)) - ((3058381/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log (22 : ℕ) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (22 : ℕ) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22815467/100000000) (δ := 317301/10000000000) 1269 312
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_23 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (23 : ℕ) / 2)) - ((-3326309/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log (23 : ℕ) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (23 : ℕ) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57466019/100000000) (δ := 158671/5000000000) 1269 317
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_24 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (24 : ℕ) / 2)) - ((1820163/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log (24 : ℕ) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (24 : ℕ) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5341447/50000000) (δ := 39681/1250000000) 1269 321
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_25 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (25 : ℕ) / 2)) - ((9422527/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log (25 : ℕ) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (25 : ℕ) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 170751/2000000) (δ := 63467/2000000000) 1269 325
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_26 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (26 : ℕ) / 2)) - ((398223/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log (26 : ℕ) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (26 : ℕ) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2357373/100000000) (δ := 158661/5000000000) 1269 329
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_27 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (27 : ℕ) / 2)) - ((2302553/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log (27 : ℕ) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (27 : ℕ) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27305649/100000000) (δ := 31731/1000000000) 1269 333
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_28 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (28 : ℕ) / 2)) - ((-4999837/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log (28 : ℕ) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (28 : ℕ) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39169047/50000000) (δ := 158639/5000000000) 1269 336
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_29 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (29 : ℕ) / 2)) - ((9647743/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log (29 : ℕ) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (29 : ℕ) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 665531/10000000) (δ := 79353/2500000000) 1269 340
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_30 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (30 : ℕ) / 2)) - ((-9770969/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log (30 : ℕ) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (30 : ℕ) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14635791/20000000) (δ := 4959/156250000) 1269 343
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_31 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (31 : ℕ) / 2)) - ((1695813/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log (31 : ℕ) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (31 : ℕ) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35009787/100000000) (δ := 79347/2500000000) 1269 347
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_32 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (32 : ℕ) / 2)) - ((9944509/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log (32 : ℕ) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (32 : ℕ) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2634931/100000000) (δ := 317273/10000000000) 1269 350
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_33 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (33 : ℕ) / 2)) - ((4210511/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log (33 : ℕ) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (33 : ℕ) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3560169/25000000) (δ := 158629/5000000000) 1269 353
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_34 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (34 : ℕ) / 2)) - ((1972219/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log (34 : ℕ) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (34 : ℕ) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1654499/10000000) (δ := 158721/5000000000) 1269 356
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_35 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (35 : ℕ) / 2)) - ((9790991/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log (35 : ℕ) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (35 : ℕ) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5120311/100000000) (δ := 317327/10000000000) 1269 359
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_36 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (36 : ℕ) / 2)) - ((3588483/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log (36 : ℕ) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (36 : ℕ) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9628843/50000000) (δ := 317411/10000000000) 1269 362
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_37 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (37 : ℕ) / 2)) - ((-6165881/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log (37 : ℕ) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (37 : ℕ) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27939973/50000000) (δ := 317307/10000000000) 1269 365
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_38 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (38 : ℕ) / 2)) - ((-5215001/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log (38 : ℕ) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (38 : ℕ) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52985111/100000000) (δ := 79313/2500000000) 1269 367
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_39 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (39 : ℕ) / 2)) - ((484617/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log (39 : ℕ) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (39 : ℕ) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3108709/50000000) (δ := 158683/5000000000) 1269 370
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_40 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (40 : ℕ) / 2)) - ((-9942291/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log (40 : ℕ) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (40 : ℕ) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37926357/50000000) (δ := 158661/5000000000) 1269 373
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_41 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (41 : ℕ) / 2)) - ((498879/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log (41 : ℕ) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (41 : ℕ) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 418597/25000000) (δ := 158689/5000000000) 1269 375
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_42 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (42 : ℕ) / 2)) - ((-1878017/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log (42 : ℕ) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (42 : ℕ) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 69763303/100000000) (δ := 317269/10000000000) 1269 377
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_43 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (43 : ℕ) / 2)) - ((4276349/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log (43 : ℕ) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (43 : ℕ) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28223039/100000000) (δ := 317319/10000000000) 1269 380
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_44 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (44 : ℕ) / 2)) - ((3141051/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log (44 : ℕ) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (44 : ℕ) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17413/78125) (δ := 79357/2500000000) 1269 382
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_45 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (45 : ℕ) / 2)) - ((-1697239/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log (45 : ℕ) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (45 : ℕ) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16151041/25000000) (δ := 79333/2500000000) 1269 384
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_46 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (46 : ℕ) / 2)) - ((-212779/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log (46 : ℕ) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (46 : ℕ) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57994433/100000000) (δ := 317417/10000000000) 1269 387
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_47 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (47 : ℕ) / 2)) - ((1622087/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log (47 : ℕ) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (47 : ℕ) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15505007/50000000) (δ := 31733/1000000000) 1269 389
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_48 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (48 : ℕ) / 2)) - ((9011467/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log (48 : ℕ) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (48 : ℕ) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5604861/50000000) (δ := 158637/5000000000) 1269 391
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_49 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (49 : ℕ) / 2)) - ((1995361/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log (49 : ℕ) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (49 : ℕ) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1703073/100000000) (δ := 317417/10000000000) 1269 393
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_50 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (50 : ℕ) / 2)) - ((2372751/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log (50 : ℕ) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (50 : ℕ) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4005361/50000000) (δ := 158671/5000000000) 1269 395
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_51 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (51 : ℕ) / 2)) - ((9496097/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log (51 : ℕ) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (51 : ℕ) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7970199/100000000) (δ := 317399/10000000000) 1269 397
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_52 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (52 : ℕ) / 2)) - ((1994641/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log (52 : ℕ) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (52 : ℕ) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 366109/20000000) (δ := 63471/2000000000) 1269 399
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_53 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (53 : ℕ) / 2)) - ((573929/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log (53 : ℕ) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (53 : ℕ) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1272081/12500000) (δ := 317411/10000000000) 1269 401
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_54 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (54 : ℕ) / 2)) - ((4417041/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log (54 : ℕ) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (54 : ℕ) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27832477/100000000) (δ := 39671/1250000000) 1269 403
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_55 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (55 : ℕ) / 2)) - ((-281029/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log (55 : ℕ) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (55 : ℕ) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -50929143/100000000) (δ := 317379/10000000000) 1269 405
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_56 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (56 : ℕ) / 2)) - ((-1249467/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log (56 : ℕ) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (56 : ℕ) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 972621/1250000) (δ := 39669/1250000000) 1269 406
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_57 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (57 : ℕ) / 2)) - ((-2041707/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log (57 : ℕ) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (57 : ℕ) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 555129/1250000) (δ := 158647/5000000000) 1269 408
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_58 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (58 : ℕ) / 2)) - ((1940207/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log (58 : ℕ) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (58 : ℕ) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3064241/50000000) (δ := 63453/2000000000) 1269 410
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_59 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (59 : ℕ) / 2)) - ((479073/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log (59 : ℕ) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (59 : ℕ) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36870863/100000000) (δ := 317381/10000000000) 1269 412
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_60 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (60 : ℕ) / 2)) - ((-243099/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log (60 : ℕ) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (60 : ℕ) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2270379/3125000) (δ := 317353/10000000000) 1269 413
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_61 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (61 : ℕ) / 2)) - ((6766777/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log (61 : ℕ) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (61 : ℕ) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5172221/25000000) (δ := 317397/10000000000) 1269 415
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_62 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (62 : ℕ) / 2)) - ((743573/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log (62 : ℕ) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (62 : ℕ) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -177691/500000) (δ := 62/1953125) 1269 417
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_63 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (63 : ℕ) / 2)) - ((-7686603/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log (63 : ℕ) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (63 : ℕ) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1912141/3125000) (δ := 2479/78125000) 1269 418
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_64 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (64 : ℕ) / 2)) - ((9920053/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log (64 : ℕ) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (64 : ℕ) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -632669/20000000) (δ := 317347/10000000000) 1269 420
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_65 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (65 : ℕ) / 2)) - ((-9593509/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log (65 : ℕ) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (65 : ℕ) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35693619/50000000) (δ := 79351/2500000000) 1269 422
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_66 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (66 : ℕ) / 2)) - ((1706559/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log (66 : ℕ) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (66 : ℕ) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1714231/12500000) (δ := 39679/1250000000) 1269 423
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_67 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (67 : ℕ) / 2)) - ((-7867171/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log (67 : ℕ) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (67 : ℕ) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7738341/12500000) (δ := 63463/2000000000) 1269 425
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_68 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (68 : ℕ) / 2)) - ((8016617/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log (68 : ℕ) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (68 : ℕ) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16018163/100000000) (δ := 317287/10000000000) 1269 426
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_69 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (69 : ℕ) / 2)) - ((-8875083/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log (69 : ℕ) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (69 : ℕ) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66567637/100000000) (δ := 31743/1000000000) 1269 428
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_70 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (70 : ℕ) / 2)) - ((4915837/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log (70 : ℕ) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (70 : ℕ) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1148371/25000000) (δ := 158701/5000000000) 1269 429
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_71 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (71 : ℕ) / 2)) - ((-9711213/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log (71 : ℕ) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (71 : ℕ) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18129267/25000000) (δ := 317429/10000000000) 1269 430
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_72 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (72 : ℕ) / 2)) - ((43929/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log (72 : ℕ) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (72 : ℕ) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19784513/100000000) (δ := 317317/10000000000) 1269 432
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_73 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (73 : ℕ) / 2)) - ((-212571/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log (73 : ℕ) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (73 : ℕ) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1677283/4000000) (δ := 158707/5000000000) 1269 433
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_74 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (74 : ℕ) / 2)) - ((-395681/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log (74 : ℕ) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (74 : ℕ) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1410209/2500000) (δ := 31727/1000000000) 1269 435
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_75 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (75 : ℕ) / 2)) - ((1999491/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log (75 : ℕ) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (75 : ℕ) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -564069/100000000) (δ := 317299/10000000000) 1269 436
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_76 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (76 : ℕ) / 2)) - ((-100681/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log (76 : ℕ) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (76 : ℕ) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52458283/100000000) (δ := 317427/10000000000) 1269 437
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_77 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (77 : ℕ) / 2)) - ((-2835561/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log (77 : ℕ) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (77 : ℕ) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13586199/25000000) (δ := 317383/10000000000) 1269 439
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_78 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (78 : ℕ) / 2)) - ((9638323/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log (78 : ℕ) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (78 : ℕ) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3372123/50000000) (δ := 317311/10000000000) 1269 440
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_79 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (79 : ℕ) / 2)) - ((204223/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log (79 : ℕ) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (79 : ℕ) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38248509/100000000) (δ := 317263/10000000000) 1269 441
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_80 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (80 : ℕ) / 2)) - ((-9962689/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log (80 : ℕ) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (80 : ℕ) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -76379541/100000000) (δ := 317407/10000000000) 1269 443
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_81 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (81 : ℕ) / 2)) - ((228511/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log (81 : ℕ) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (81 : ℕ) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9101817/25000000) (δ := 79331/2500000000) 1269 444
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_82 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (82 : ℕ) / 2)) - ((9989467/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log (82 : ℕ) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (82 : ℕ) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1147561/100000000) (δ := 317351/10000000000) 1269 445
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_83 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (83 : ℕ) / 2)) - ((583919/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log (83 : ℕ) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (83 : ℕ) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9085909/25000000) (δ := 158711/5000000000) 1269 446
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_84 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (84 : ℕ) / 2)) - ((-9315421/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log (84 : ℕ) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (84 : ℕ) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34617841/50000000) (δ := 634609/10000000000) 1269 447
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_85 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (85 : ℕ) / 2)) - ((-6572683/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log (85 : ℕ) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (85 : ℕ) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2859981/5000000) (δ := 63453/2000000000) 1269 449
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_86 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (86 : ℕ) / 2)) - ((510543/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log (86 : ℕ) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (86 : ℕ) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28751453/100000000) (δ := 317393/10000000000) 1269 450
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_87 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (87 : ℕ) / 2)) - ((9952163/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log (87 : ℕ) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (87 : ℕ) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2446309/100000000) (δ := 317281/10000000000) 1269 451
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_88 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (88 : ℕ) / 2)) - ((6444653/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log (88 : ℕ) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (88 : ℕ) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5440453/25000000) (δ := 317253/10000000000) 1269 452
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_89 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (89 : ℕ) / 2)) - ((-924763/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log (89 : ℕ) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (89 : ℕ) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21960249/50000000) (δ := 158639/5000000000) 1269 453
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_90 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (90 : ℕ) / 2)) - ((-4186421/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log (90 : ℕ) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (90 : ℕ) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64077337/100000000) (δ := 317397/10000000000) 1269 454
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_91 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (91 : ℕ) / 2)) - ((-4944269/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log (91 : ℕ) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (91 : ℕ) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74803683/100000000) (δ := 31727/500000000) 1269 456
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_92 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (92 : ℕ) / 2)) - ((-6961741/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log (92 : ℕ) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (92 : ℕ) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2926063/5000000) (δ := 2479/78125000) 1269 457
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_93 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (93 : ℕ) / 2)) - ((-1925139/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log (93 : ℕ) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (93 : ℕ) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1378531/3125000) (δ := 317419/10000000000) 1269 458
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_94 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (94 : ℕ) / 2)) - ((3043531/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log (94 : ℕ) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (94 : ℕ) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7884607/25000000) (δ := 39657/1250000000) 1269 459
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_95 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (95 : ℕ) / 2)) - ((6745953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log (95 : ℕ) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (95 : ℕ) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20759499/100000000) (δ := 79357/2500000000) 1269 460
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_96 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (96 : ℕ) / 2)) - ((8917831/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log (96 : ℕ) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (96 : ℕ) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1467267/12500000) (δ := 39663/1250000000) 1269 461
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_97 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (97 : ℕ) / 2)) - ((9842857/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log (97 : ℕ) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (97 : ℕ) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2218927/50000000) (δ := 39679/1250000000) 1269 462
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_98 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (98 : ℕ) / 2)) - ((4994467/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log (98 : ℕ) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (98 : ℕ) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 235249/20000000) (δ := 15863/500000000) 1269 463
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_99 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (99 : ℕ) / 2)) - ((1223683/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log (99 : ℕ) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (99 : ℕ) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5139057/100000000) (δ := 79347/2500000000) 1269 464
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_100 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (100 : ℕ) / 2)) - ((4777727/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log (100 : ℕ) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (100 : ℕ) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1870577/25000000) (δ := 39677/1250000000) 1269 465
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_101 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (101 : ℕ) / 2)) - ((9461603/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log (101 : ℕ) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (101 : ℕ) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32191/390625) (δ := 158679/5000000000) 1269 466
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_102 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (102 : ℕ) / 2)) - ((4780017/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log (102 : ℕ) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (102 : ℕ) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1860843/25000000) (δ := 31733/1000000000) 1269 467
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_103 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (103 : ℕ) / 2)) - ((9791027/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log (103 : ℕ) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (103 : ℕ) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40959/800000) (δ := 317401/10000000000) 1269 468
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_104 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (104 : ℕ) / 2)) - ((9986439/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log (104 : ℕ) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (104 : ℕ) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1302131/100000000) (δ := 317429/10000000000) 1269 469
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_105 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (105 : ℕ) / 2)) - ((9873461/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log (105 : ℕ) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (105 : ℕ) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3981307/100000000) (δ := 158723/5000000000) 1269 470
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_106 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (106 : ℕ) / 2)) - ((568571/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log (106 : ℕ) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (106 : ℕ) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10705061/100000000) (δ := 317417/10000000000) 1269 471
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_107 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (107 : ℕ) / 2)) - ((3646289/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log (107 : ℕ) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (107 : ℕ) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1177437/6250000) (δ := 158707/5000000000) 1269 472
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_108 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (108 : ℕ) / 2)) - ((845403/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log (108 : ℕ) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (108 : ℕ) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3544913/12500000) (δ := 317361/10000000000) 1269 473
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_109 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (109 : ℕ) / 2)) - ((2929/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log (109 : ℕ) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (109 : ℕ) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39240619/100000000) (δ := 317433/10000000000) 1269 474
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_110 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (110 : ℕ) / 2)) - ((-2341839/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log (110 : ℕ) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (110 : ℕ) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -51455971/100000000) (δ := 158649/5000000000) 1269 475
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_111 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (111 : ℕ) / 2)) - ((-2141271/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log (111 : ℕ) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (111 : ℕ) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12996313/20000000) (δ := 317327/10000000000) 1269 476
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_112 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (112 : ℕ) / 2)) - ((-9987363/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log (112 : ℕ) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (112 : ℕ) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 77282853/100000000) (δ := 4959/156250000) 1269 476
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_113 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (113 : ℕ) / 2)) - ((-120169/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log (113 : ℕ) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (113 : ℕ) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61204983/100000000) (δ := 39681/1250000000) 1269 477
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_114 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (114 : ℕ) / 2)) - ((-1834977/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log (114 : ℕ) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (114 : ℕ) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10970873/25000000) (δ := 317383/10000000000) 1269 478
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_115 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (115 : ℕ) / 2)) - ((1321837/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log (115 : ℕ) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (115 : ℕ) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 791943/3125000) (δ := 79323/2500000000) 1269 479
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_116 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (116 : ℕ) / 2)) - ((9750161/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log (116 : ℕ) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (116 : ℕ) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1400017/25000000) (δ := 317339/10000000000) 1269 480
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_117 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (117 : ℕ) / 2)) - ((8180629/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log (117 : ℕ) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (117 : ℕ) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15319037/100000000) (δ := 79317/2500000000) 1269 481
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_118 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (118 : ℕ) / 2)) - ((748187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log (118 : ℕ) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (118 : ℕ) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37397691/100000000) (δ := 19831/625000000) 1269 482
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_119 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (119 : ℕ) / 2)) - ((-3769171/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log (119 : ℕ) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (119 : ℕ) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60616859/100000000) (δ := 19839/625000000) 1269 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_120 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (120 : ℕ) / 2)) - ((-4836317/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log (120 : ℕ) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (120 : ℕ) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 721253/1000000) (δ := 79331/2500000000) 1269 483
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_121 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (121 : ℕ) / 2)) - ((-584577/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log (121 : ℕ) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (121 : ℕ) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46685383/100000000) (δ := 317451/10000000000) 1269 484
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_122 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (122 : ℕ) / 2)) - ((346021/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log (122 : ℕ) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (122 : ℕ) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2520257/12500000) (δ := 317281/10000000000) 1269 485
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_123 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (123 : ℕ) / 2)) - ((4780963/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log (123 : ℕ) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (123 : ℕ) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -742723/10000000) (δ := 158697/5000000000) 1269 486
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_124 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (124 : ℕ) / 2)) - ((319611/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log (124 : ℕ) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (124 : ℕ) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9016257/25000000) (δ := 158633/5000000000) 1269 487
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_125 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (125 : ℕ) / 2)) - ((-4358251/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log (125 : ℕ) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (125 : ℕ) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -256773/390625) (δ := 158669/5000000000) 1269 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_126 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (126 : ℕ) / 2)) - ((-7550111/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log (126 : ℕ) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (126 : ℕ) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15165421/25000000) (δ := 63473/2000000000) 1269 488
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_127 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (127 : ℕ) / 2)) - ((2000969/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log (127 : ℕ) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (127 : ℕ) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 289767/1000000) (δ := 317393/10000000000) 1269 489
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_128 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (128 : ℕ) / 2)) - ((9891259/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log (128 : ℕ) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (128 : ℕ) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -922543/25000000) (δ := 317381/10000000000) 1269 490
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_129 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (129 : ℕ) / 2)) - ((155463/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log (129 : ℕ) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (129 : ℕ) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18662329/50000000) (δ := 6349/200000000) 1269 491
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_130 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (130 : ℕ) / 2)) - ((-4825423/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log (130 : ℕ) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (130 : ℕ) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14382813/20000000) (δ := 12693/400000000) 1269 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_131 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (131 : ℕ) / 2)) - ((-2014811/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log (131 : ℕ) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (131 : ℕ) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24819343/50000000) (δ := 158639/5000000000) 1269 492
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_132 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (132 : ℕ) / 2)) - ((8640779/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log (132 : ℕ) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (132 : ℕ) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13187021/100000000) (δ := 317297/10000000000) 1269 493
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_133 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (133 : ℕ) / 2)) - ((2838833/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log (133 : ℕ) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (133 : ℕ) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1510947/6250000) (δ := 158667/5000000000) 1269 494
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_134 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (134 : ℕ) / 2)) - ((-1998923/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log (134 : ℕ) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (134 : ℕ) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62434349/100000000) (δ := 634563/10000000000) 1269 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_135 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (135 : ℕ) / 2)) - ((-3023167/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log (135 : ℕ) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (135 : ℕ) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27751273/50000000) (δ := 62/1953125) 1269 495
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_136 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (136 : ℕ) / 2)) - ((4070583/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log (136 : ℕ) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (136 : ℕ) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15489749/100000000) (δ := 317291/10000000000) 1269 496
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_137 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (137 : ℕ) / 2)) - ((5274629/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log (137 : ℕ) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (137 : ℕ) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12689811/50000000) (δ := 39673/1250000000) 1269 497
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_138 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (138 : ℕ) / 2)) - ((-1121311/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log (138 : ℕ) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (138 : ℕ) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67096051/100000000) (δ := 79339/2500000000) 1269 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_139 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (139 : ℕ) / 2)) - ((-802161/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log (139 : ℕ) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (139 : ℕ) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 47435957/100000000) (δ := 317447/10000000000) 1269 498
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_140 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (140 : ℕ) / 2)) - ((986799/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log (140 : ℕ) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (140 : ℕ) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 127083/3125000) (δ := 12691/400000000) 1269 499
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_141 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (141 : ℕ) / 2)) - ((-16863/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log (141 : ℕ) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (141 : ℕ) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40113219/100000000) (δ := 317299/10000000000) 1269 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_142 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (142 : ℕ) / 2)) - ((-9658783/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log (142 : ℕ) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (142 : ℕ) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 71990241/100000000) (δ := 317299/10000000000) 1269 500
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_143 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (143 : ℕ) / 2)) - ((4983589/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log (143 : ℕ) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (143 : ℕ) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3278411/12500000) (δ := 79333/2500000000) 1269 501
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_144 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (144 : ℕ) / 2)) - ((1719183/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log (144 : ℕ) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (144 : ℕ) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20312927/100000000) (δ := 15863/500000000) 1269 502
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_145 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (145 : ℕ) / 2)) - ((-2265119/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log (145 : ℕ) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (145 : ℕ) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -528251/781250) (δ := 63483/2000000000) 1269 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_146 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (146 : ℕ) / 2)) - ((-426549/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log (146 : ℕ) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (146 : ℕ) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 646957/1562500) (δ := 63463/2000000000) 1269 503
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_147 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (147 : ℕ) / 2)) - ((9565279/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log (147 : ℕ) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (147 : ℕ) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3699273/50000000) (δ := 317287/10000000000) 1269 504
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_148 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (148 : ℕ) / 2)) - ((-6492601/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log (148 : ℕ) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (148 : ℕ) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14233797/25000000) (δ := 63489/2000000000) 1269 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_149 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (149 : ℕ) / 2)) - ((-823881/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log (149 : ℕ) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (149 : ℕ) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24942237/50000000) (δ := 158679/5000000000) 1269 505
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_150 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (150 : ℕ) / 2)) - ((9990453/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log (150 : ℕ) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (150 : ℕ) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1092483/100000000) (δ := 317373/10000000000) 1269 506
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_151 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (151 : ℕ) / 2)) - ((-321383/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log (151 : ℕ) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (151 : ℕ) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13193037/25000000) (δ := 317301/10000000000) 1269 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_152 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (152 : ℕ) / 2)) - ((-303179/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log (152 : ℕ) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (152 : ℕ) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 811429/1562500) (δ := 158651/5000000000) 1269 507
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_153 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (153 : ℕ) / 2)) - ((9989761/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log (153 : ℕ) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (153 : ℕ) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1131419/100000000) (δ := 158687/5000000000) 1269 508
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_154 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (154 : ℕ) / 2)) - ((-5843417/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log (154 : ℕ) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (154 : ℕ) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -54871623/100000000) (δ := 158673/5000000000) 1269 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_155 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (155 : ℕ) / 2)) - ((-209101/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log (155 : ℕ) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (155 : ℕ) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5974801/12500000) (δ := 317257/10000000000) 1269 509
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_156 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (156 : ℕ) / 2)) - ((383201/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log (156 : ℕ) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (156 : ℕ) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7271073/100000000) (δ := 317417/10000000000) 1269 510
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_157 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (157 : ℕ) / 2)) - ((-4063887/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log (157 : ℕ) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (157 : ℕ) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7874063/12500000) (δ := 158707/5000000000) 1269 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_158 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (158 : ℕ) / 2)) - ((123779/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log (158 : ℕ) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (158 : ℕ) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37721681/100000000) (δ := 158707/5000000000) 1269 511
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_159 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (159 : ℕ) / 2)) - ((7171231/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log (159 : ℕ) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (159 : ℕ) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9639133/50000000) (δ := 317361/10000000000) 1269 512
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_160 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (160 : ℕ) / 2)) - ((-4989331/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log (160 : ℕ) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (160 : ℕ) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -76906369/100000000) (δ := 31727/1000000000) 1269 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_161 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (161 : ℕ) / 2)) - ((49958/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log (161 : ℕ) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (161 : ℕ) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21924937/100000000) (δ := 31737/1000000000) 1269 513
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_162 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (162 : ℕ) / 2)) - ((466483/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log (162 : ℕ) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (162 : ℕ) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7386819/20000000) (δ := 63481/2000000000) 1269 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_163 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (163 : ℕ) / 2)) - ((-3777737/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log (163 : ℕ) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (163 : ℕ) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60682143/100000000) (δ := 158699/5000000000) 1269 514
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_164 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (164 : ℕ) / 2)) - ((4998459/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log (164 : ℕ) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (164 : ℕ) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 620733/100000000) (δ := 317327/10000000000) 1269 515
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_165 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (165 : ℕ) / 2)) - ((-7382243/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log (165 : ℕ) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (165 : ℕ) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30015381/50000000) (δ := 63451/2000000000) 1269 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_166 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (166 : ℕ) / 2)) - ((1377481/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log (166 : ℕ) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (166 : ℕ) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17907611/50000000) (δ := 79337/2500000000) 1269 516
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_167 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (167 : ℕ) / 2)) - ((2532369/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log (167 : ℕ) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (167 : ℕ) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -519853/2000000) (δ := 317383/10000000000) 1269 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_168 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (168 : ℕ) / 2)) - ((-72161/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log (168 : ℕ) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (168 : ℕ) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34354031/50000000) (δ := 15871/500000000) 1269 517
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_169 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (169 : ℕ) / 2)) - ((9734911/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log (169 : ℕ) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (169 : ℕ) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2884597/50000000) (δ := 79323/2500000000) 1269 518
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_170 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (170 : ℕ) / 2)) - ((-6730031/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log (170 : ℕ) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (170 : ℕ) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3607903/6250000) (δ := 317439/10000000000) 1269 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_171 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (171 : ℕ) / 2)) - ((1577861/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log (171 : ℕ) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (171 : ℕ) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35308701/100000000) (δ := 317339/10000000000) 1269 519
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_172 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (172 : ℕ) / 2)) - ((3891099/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log (172 : ℕ) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (172 : ℕ) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -731957/2500000) (δ := 63467/2000000000) 1269 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_173 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (173 : ℕ) / 2)) - ((-1006737/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log (173 : ℕ) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (173 : ℕ) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 62678219/100000000) (δ := 63487/2000000000) 1269 520
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_174 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (174 : ℕ) / 2)) - ((2482323/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log (174 : ℕ) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (174 : ℕ) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2974723/100000000) (δ := 19831/625000000) 1269 521
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_175 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (175 : ℕ) / 2)) - ((-9303069/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log (175 : ℕ) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (175 : ℕ) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69151127/100000000) (δ := 79331/2500000000) 1269 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_176 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (176 : ℕ) / 2)) - ((6604819/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log (176 : ℕ) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (176 : ℕ) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10616699/50000000) (δ := 79331/2500000000) 1269 522
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_177 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (177 : ℕ) / 2)) - ((-1324513/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log (177 : ℕ) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (177 : ℕ) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22986241/50000000) (δ := 79313/2500000000) 1269 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_178 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (178 : ℕ) / 2)) - ((-328407/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log (178 : ℕ) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (178 : ℕ) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 43393671/100000000) (δ := 317451/10000000000) 1269 523
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_179 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (179 : ℕ) / 2)) - ((5463643/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log (179 : ℕ) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (179 : ℕ) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12409739/50000000) (δ := 317423/10000000000) 1269 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_180 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (180 : ℕ) / 2)) - ((-825577/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log (180 : ℕ) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (180 : ℕ) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 63550509/100000000) (δ := 1983/62500000) 1269 524
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_181 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (181 : ℕ) / 2)) - ((9745911/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log (181 : ℕ) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (181 : ℕ) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5647701/100000000) (δ := 158647/5000000000) 1269 525
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_182 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (182 : ℕ) / 2)) - ((-9917757/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log (182 : ℕ) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (182 : ℕ) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9416413/12500000) (δ := 317337/10000000000) 1269 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_183 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (183 : ℕ) / 2)) - ((4472487/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log (183 : ℕ) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (183 : ℕ) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2317453/20000000) (δ := 158633/5000000000) 1269 526
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_184 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (184 : ℕ) / 2)) - ((-3555731/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log (184 : ℕ) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (184 : ℕ) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7381011/12500000) (δ := 63473/2000000000) 1269 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_185 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (185 : ℕ) / 2)) - ((4738577/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log (185 : ℕ) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (185 : ℕ) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26928249/100000000) (δ := 158719/5000000000) 1269 527
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_186 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (186 : ℕ) / 2)) - ((-426297/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log (186 : ℕ) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (186 : ℕ) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44639819/100000000) (δ := 31731/1000000000) 1269 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_187 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (187 : ℕ) / 2)) - ((-457839/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log (187 : ℕ) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (187 : ℕ) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20207453/50000000) (δ := 31731/1000000000) 1269 528
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_188 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (188 : ℕ) / 2)) - ((355267/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log (188 : ℕ) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (188 : ℕ) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4008157/12500000) (δ := 317421/10000000000) 1269 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_189 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (189 : ℕ) / 2)) - ((-4905139/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log (189 : ℕ) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (189 : ℕ) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 52086893/100000000) (δ := 317321/10000000000) 1269 529
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_190 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (190 : ℕ) / 2)) - ((1647227/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log (190 : ℕ) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (190 : ℕ) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21286327/100000000) (δ := 317253/10000000000) 1269 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_191 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (191 : ℕ) / 2)) - ((-7885791/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log (191 : ℕ) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (191 : ℕ) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1549557/2500000) (δ := 6349/200000000) 1269 530
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_192 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (192 : ℕ) / 2)) - ((882051/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log (192 : ℕ) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (192 : ℕ) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12264963/100000000) (δ := 12697/400000000) 1269 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_193 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (193 : ℕ) / 2)) - ((-73754/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log (193 : ℕ) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (193 : ℕ) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4383597/6250000) (δ := 12697/400000000) 1269 531
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_194 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (194 : ℕ) / 2)) - ((9803463/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log (194 : ℕ) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (194 : ℕ) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4964681/100000000) (δ := 317297/10000000000) 1269 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_195 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (195 : ℕ) / 2)) - ((-79757/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log (195 : ℕ) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (195 : ℕ) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9573847/12500000) (δ := 158703/5000000000) 1269 532
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_196 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (196 : ℕ) / 2)) - ((4998313/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log (196 : ℕ) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (196 : ℕ) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 649417/100000000) (δ := 158717/5000000000) 1269 533
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_197 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (197 : ℕ) / 2)) - ((-9935751/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log (197 : ℕ) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (197 : ℕ) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37852183/50000000) (δ := 62/1953125) 1269 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_198 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (198 : ℕ) / 2)) - ((9830301/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log (198 : ℕ) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (198 : ℕ) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 461223/10000000) (δ := 15867/500000000) 1269 534
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_199 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (199 : ℕ) / 2)) - ((-194297/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log (199 : ℕ) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (199 : ℕ) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -725553/1000000) (δ := 79353/2500000000) 1269 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_200 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (200 : ℕ) / 2)) - ((480773/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log (200 : ℕ) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (200 : ℕ) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6955481/100000000) (δ := 2479/78125000) 1269 535
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_201 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (201 : ℕ) / 2)) - ((-9549637/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log (201 : ℕ) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (201 : ℕ) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -71008347/100000000) (δ := 317319/10000000000) 1269 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_202 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (202 : ℕ) / 2)) - ((9527903/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log (202 : ℕ) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (202 : ℕ) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3856241/50000000) (δ := 79321/2500000000) 1269 536
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_203 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (203 : ℕ) / 2)) - ((-4776301/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log (203 : ℕ) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (203 : ℕ) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -71033367/100000000) (δ := 39657/1250000000) 1269 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_204 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (204 : ℕ) / 2)) - ((9619899/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log (204 : ℕ) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (204 : ℕ) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3457479/50000000) (δ := 39657/1250000000) 1269 537
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_205 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (205 : ℕ) / 2)) - ((-2429699/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log (205 : ℕ) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (205 : ℕ) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1451941/2000000) (δ := 2539/80000000) 1269 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_206 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (206 : ℕ) / 2)) - ((1966341/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log (206 : ℕ) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (206 : ℕ) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 574131/12500000) (δ := 19833/625000000) 1269 538
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_207 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (207 : ℕ) / 2)) - ((-620889/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log (207 : ℕ) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (207 : ℕ) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37835421/50000000) (δ := 317399/10000000000) 1269 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_208 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (208 : ℕ) / 2)) - ((1249399/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log (208 : ℕ) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (208 : ℕ) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 96913/12500000) (δ := 317299/10000000000) 1269 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_209 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (209 : ℕ) / 2)) - ((-99773/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log (209 : ℕ) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (209 : ℕ) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38427513/50000000) (δ := 79351/2500000000) 1269 539
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_210 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (210 : ℕ) / 2)) - ((4918927/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log (210 : ℕ) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (210 : ℕ) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -901627/20000000) (δ := 317271/10000000000) 1269 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_211 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (211 : ℕ) / 2)) - ((-9530441/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log (211 : ℕ) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (211 : ℕ) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70848257/100000000) (δ := 39679/1250000000) 1269 540
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_212 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (212 : ℕ) / 2)) - ((450381/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log (212 : ℕ) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (212 : ℕ) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11231889/100000000) (δ := 15863/500000000) 1269 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_213 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (213 : ℕ) / 2)) - ((-1645033/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log (213 : ℕ) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (213 : ℕ) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1268309/2000000) (δ := 317343/10000000000) 1269 541
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_214 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (214 : ℕ) / 2)) - ((7146779/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log (214 : ℕ) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (214 : ℕ) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19365819/100000000) (δ := 63463/2000000000) 1269 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_215 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (215 : ℕ) / 2)) - ((-5750047/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log (215 : ℕ) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (215 : ℕ) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13646289/25000000) (δ := 63463/2000000000) 1269 542
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_216 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (216 : ℕ) / 2)) - ((504389/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log (216 : ℕ) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (216 : ℕ) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7221533/25000000) (δ := 79329/2500000000) 1269 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_217 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (217 : ℕ) / 2)) - ((-2030291/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log (217 : ℕ) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (217 : ℕ) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44381169/100000000) (δ := 39677/1250000000) 1269 543
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_218 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (218 : ℕ) / 2)) - ((-99501/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log (218 : ℕ) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (218 : ℕ) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39767447/100000000) (δ := 158629/5000000000) 1269 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_219 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (219 : ℕ) / 2)) - ((39803/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log (219 : ℕ) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (219 : ℕ) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32830457/100000000) (δ := 158679/5000000000) 1269 544
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_220 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (220 : ℕ) / 2)) - ((-1217203/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log (220 : ℕ) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (220 : ℕ) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25991399/50000000) (δ := 31743/1000000000) 1269 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_221 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (221 : ℕ) / 2)) - ((6979449/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log (221 : ℕ) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (221 : ℕ) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4989203/25000000) (δ := 31743/1000000000) 1269 545
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_222 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (222 : ℕ) / 2)) - ((-1734451/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log (222 : ℕ) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (222 : ℕ) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65509979/100000000) (δ := 317401/10000000000) 1269 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_223 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (223 : ℕ) / 2)) - ((9733697/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log (223 : ℕ) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (223 : ℕ) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5782441/100000000) (δ := 317401/10000000000) 1269 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_224 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (224 : ℕ) / 2)) - ((-2493639/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log (224 : ℕ) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (224 : ℕ) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3070241/4000000) (δ := 317301/10000000000) 1269 546
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_225 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (225 : ℕ) / 2)) - ((463093/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log (225 : ℕ) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (225 : ℕ) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1208211/12500000) (δ := 317429/10000000000) 1269 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_226 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (226 : ℕ) / 2)) - ((-3777111/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log (226 : ℕ) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (226 : ℕ) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30338681/50000000) (δ := 317287/5000000000) 1269 547
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_227 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (227 : ℕ) / 2)) - ((197381/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log (227 : ℕ) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (227 : ℕ) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1318427/5000000) (δ := 158673/5000000000) 1269 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_228 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (228 : ℕ) / 2)) - ((-203429/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log (228 : ℕ) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (228 : ℕ) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8671333/20000000) (δ := 158673/5000000000) 1269 548
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_229 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (229 : ℕ) / 2)) - ((-1999399/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log (229 : ℕ) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (229 : ℕ) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44302323/100000000) (δ := 158643/5000000000) 1269 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_230 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (230 : ℕ) / 2)) - ((5465027/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log (230 : ℕ) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (230 : ℕ) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6203837/25000000) (δ := 158693/5000000000) 1269 549
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_231 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (231 : ℕ) / 2)) - ((-8232203/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log (231 : ℕ) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (231 : ℕ) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31723207/50000000) (δ := 317389/10000000000) 1269 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_232 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (232 : ℕ) / 2)) - ((9794803/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log (232 : ℕ) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (232 : ℕ) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5073241/100000000) (δ := 317389/10000000000) 1269 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_233 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (233 : ℕ) / 2)) - ((-9781111/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log (233 : ℕ) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (233 : ℕ) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 73299439/100000000) (δ := 158707/5000000000) 1269 550
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_234 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (234 : ℕ) / 2)) - ((1007203/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log (234 : ℕ) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (234 : ℕ) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3169173/20000000) (δ := 158721/5000000000) 1269 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_235 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (235 : ℕ) / 2)) - ((-4804177/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log (235 : ℕ) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (235 : ℕ) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2589909/5000000) (δ := 158721/5000000000) 1269 551
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_236 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (236 : ℕ) / 2)) - ((67237/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log (236 : ℕ) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (236 : ℕ) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18962259/50000000) (δ := 317433/10000000000) 1269 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_237 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (237 : ℕ) / 2)) - ((3939459/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log (237 : ℕ) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (237 : ℕ) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2914689/10000000) (δ := 31737/1000000000) 1269 552
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_238 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (238 : ℕ) / 2)) - ((-3837561/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log (238 : ℕ) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (238 : ℕ) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30571843/50000000) (δ := 63461/2000000000) 1269 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_239 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (239 : ℕ) / 2)) - ((1954103/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log (239 : ℕ) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (239 : ℕ) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 536619/10000000) (δ := 158649/5000000000) 1269 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_240 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (240 : ℕ) / 2)) - ((-2404253/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log (240 : ℕ) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (240 : ℕ) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 71598473/100000000) (δ := 63481/2000000000) 1269 553
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_241 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (241 : ℕ) / 2)) - ((7102131/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log (241 : ℕ) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (241 : ℕ) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3904977/20000000) (δ := 79319/2500000000) 1269 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_242 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (242 : ℕ) / 2)) - ((-2720723/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log (242 : ℕ) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (242 : ℕ) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9231711/20000000) (δ := 79319/2500000000) 1269 554
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_243 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (243 : ℕ) / 2)) - ((-308721/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log (243 : ℕ) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (243 : ℕ) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22754443/50000000) (δ := 39681/1250000000) 1269 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_244 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (244 : ℕ) / 2)) - ((707099/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log (244 : ℕ) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (244 : ℕ) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19635229/100000000) (δ := 39681/1250000000) 1269 555
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_245 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (245 : ℕ) / 2)) - ((-9716013/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log (245 : ℕ) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (245 : ℕ) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18141893/25000000) (δ := 31731/500000000) 1269 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_246 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (246 : ℕ) / 2)) - ((9498119/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log (246 : ℕ) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (246 : ℕ) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3977029/50000000) (δ := 317283/10000000000) 1269 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_247 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (247 : ℕ) / 2)) - ((-6327357/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log (247 : ℕ) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (247 : ℕ) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14099233/25000000) (δ := 317283/10000000000) 1269 556
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_248 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (248 : ℕ) / 2)) - ((1069173/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log (248 : ℕ) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (248 : ℕ) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2286991/6250000) (δ := 317411/10000000000) 1269 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_249 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (249 : ℕ) / 2)) - ((4628247/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log (249 : ℕ) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (249 : ℕ) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27240431/100000000) (δ := 19837/625000000) 1269 557
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_250 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (250 : ℕ) / 2)) - ((-2204461/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log (250 : ℕ) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (250 : ℕ) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16565179/25000000) (δ := 317339/10000000000) 1269 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_251 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (251 : ℕ) / 2)) - ((9931043/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log (251 : ℕ) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (251 : ℕ) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -183601/6250000) (δ := 317339/10000000000) 1269 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_252 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (252 : ℕ) / 2)) - ((-92623/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log (252 : ℕ) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (252 : ℕ) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6013327/10000000) (δ := 317439/10000000000) 1269 558
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_253 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (253 : ℕ) / 2)) - ((2043657/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log (253 : ℕ) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (253 : ℕ) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34124517/100000000) (δ := 63467/2000000000) 1269 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_254 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (254 : ℕ) / 2)) - ((838831/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log (254 : ℕ) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (254 : ℕ) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28449873/100000000) (δ := 63467/2000000000) 1269 559
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_255 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (255 : ℕ) / 2)) - ((-4412739/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log (255 : ℕ) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (255 : ℕ) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66301239/100000000) (δ := 79349/2500000000) 1269 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_256 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (256 : ℕ) / 2)) - ((1232259/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log (256 : ℕ) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (256 : ℕ) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4217/100000) (δ := 19831/625000000) 1269 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_257 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (257 : ℕ) / 2)) - ((-3349913/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log (257 : ℕ) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (257 : ℕ) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 57624543/100000000) (δ := 317407/10000000000) 1269 560
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_258 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (258 : ℕ) / 2)) - ((17701/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log (258 : ℕ) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (258 : ℕ) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37853071/100000000) (δ := 317379/10000000000) 1269 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_259 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (259 : ℕ) / 2)) - ((5894323/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log (259 : ℕ) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (259 : ℕ) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2351101/10000000) (δ := 317279/10000000000) 1269 561
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_260 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (260 : ℕ) / 2)) - ((-4851949/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log (260 : ℕ) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (260 : ℕ) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -72440893/100000000) (δ := 39669/1250000000) 1269 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_261 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (261 : ℕ) / 2)) - ((8951997/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log (261 : ℕ) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (261 : ℕ) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1443491/12500000) (δ := 39669/1250000000) 1269 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_262 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (262 : ℕ) / 2)) - ((-3835877/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log (262 : ℕ) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (262 : ℕ) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 49111859/100000000) (δ := 951951/10000000000) 1269 562
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_263 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (263 : ℕ) / 2)) - ((-3247873/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log (263 : ℕ) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (263 : ℕ) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2376979/5000000) (δ := 317423/10000000000) 1269 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_264 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (264 : ℕ) / 2)) - ((349797/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log (264 : ℕ) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (264 : ℕ) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12660193/100000000) (δ := 23797/250000000) 1269 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_265 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (265 : ℕ) / 2)) - ((-2430509/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log (265 : ℕ) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (265 : ℕ) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 72631547/100000000) (δ := 1983/62500000) 1269 563
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_266 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (266 : ℕ) / 2)) - ((5502947/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log (266 : ℕ) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (266 : ℕ) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24701979/100000000) (δ := 158697/5000000000) 1269 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_267 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (267 : ℕ) / 2)) - ((88551/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log (267 : ℕ) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (267 : ℕ) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34818879/100000000) (δ := 317409/10000000000) 1269 564
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_268 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (268 : ℕ) / 2)) - ((-8120653/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log (268 : ℕ) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (268 : ℕ) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6296197/10000000) (δ := 317437/10000000000) 1269 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_269 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (269 : ℕ) / 2)) - ((9879579/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log (269 : ℕ) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (269 : ℕ) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -155347/4000000) (δ := 317437/10000000000) 1269 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_270 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (270 : ℕ) / 2)) - ((-1469289/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log (270 : ℕ) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (270 : ℕ) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27487859/50000000) (δ := 158633/5000000000) 1269 565
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_271 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (271 : ℕ) / 2)) - ((-834463/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log (271 : ℕ) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (271 : ℕ) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21730919/50000000) (δ := 158719/5000000000) 1269 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_272 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (272 : ℕ) / 2)) - ((8261721/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log (272 : ℕ) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (272 : ℕ) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7481461/50000000) (δ := 158719/5000000000) 1269 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_273 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (273 : ℕ) / 2)) - ((-2442627/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log (273 : ℕ) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (273 : ℕ) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36586769/50000000) (δ := 158669/5000000000) 1269 566
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_274 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (274 : ℕ) / 2)) - ((2547219/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log (274 : ℕ) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (274 : ℕ) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -518129/2000000) (δ := 317293/10000000000) 1269 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_275 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (275 : ℕ) / 2)) - ((2913467/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log (275 : ℕ) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (275 : ℕ) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31879051/100000000) (δ := 317393/10000000000) 1269 567
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_276 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (276 : ℕ) / 2)) - ((-9061619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log (276 : ℕ) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (276 : ℕ) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67622879/100000000) (δ := 317321/10000000000) 1269 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_277 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (277 : ℕ) / 2)) - ((4585367/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log (277 : ℕ) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (277 : ℕ) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -410119/4000000) (δ := 158641/5000000000) 1269 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_278 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (278 : ℕ) / 2)) - ((-3008357/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log (278 : ℕ) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (278 : ℕ) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4690913/10000000) (δ := 158641/5000000000) 1269 568
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_279 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (279 : ℕ) / 2)) - ((-1323277/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log (279 : ℕ) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (279 : ℕ) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5321461/10000000) (δ := 317353/10000000000) 1269 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_280 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (280 : ℕ) / 2)) - ((2474981/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log (280 : ℕ) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (280 : ℕ) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 884957/25000000) (δ := 6349/200000000) 1269 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_281 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (281 : ℕ) / 2)) - ((-7398109/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log (281 : ℕ) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (281 : ℕ) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60089641/100000000) (δ := 317253/10000000000) 1269 569
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_282 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (282 : ℕ) / 2)) - ((-547781/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log (282 : ℕ) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (282 : ℕ) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40640047/100000000) (δ := 158689/5000000000) 1269 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_283 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (283 : ℕ) / 2)) - ((8136453/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log (283 : ℕ) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (283 : ℕ) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15510031/100000000) (δ := 12693/400000000) 1269 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_284 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (284 : ℕ) / 2)) - ((-600129/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log (284 : ℕ) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (284 : ℕ) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 71463413/100000000) (δ := 158689/5000000000) 1269 570
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_285 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (285 : ℕ) / 2)) - ((3675299/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log (285 : ℕ) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (285 : ℕ) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14930559/50000000) (δ := 317297/10000000000) 1269 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_286 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (286 : ℕ) / 2)) - ((2582583/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log (286 : ℕ) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (286 : ℕ) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25700461/100000000) (δ := 317397/10000000000) 1269 571
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_287 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (287 : ℕ) / 2)) - ((-9948953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log (287 : ℕ) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (287 : ℕ) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38006351/50000000) (δ := 317269/10000000000) 1269 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_288 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (288 : ℕ) / 2)) - ((6722221/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log (288 : ℕ) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (288 : ℕ) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4167951/20000000) (δ := 158717/5000000000) 1269 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_289 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (289 : ℕ) / 2)) - ((3182/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log (289 : ℕ) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (289 : ℕ) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34142843/100000000) (δ := 317269/10000000000) 1269 572
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_290 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (290 : ℕ) / 2)) - ((-4573817/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log (290 : ℕ) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (290 : ℕ) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17035739/25000000) (δ := 158631/5000000000) 1269 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_291 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (291 : ℕ) / 2)) - ((8568959/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log (291 : ℕ) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (291 : ℕ) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -846217/6250000) (δ := 317341/10000000000) 1269 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_292 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (292 : ℕ) / 2)) - ((-642961/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log (292 : ℕ) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (292 : ℕ) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2043921/5000000) (δ := 158681/5000000000) 1269 573
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_293 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (293 : ℕ) / 2)) - ((-1970723/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log (293 : ℕ) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (293 : ℕ) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61970497/100000000) (δ := 79353/2500000000) 1269 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_294 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (294 : ℕ) / 2)) - ((4750851/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log (294 : ℕ) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (294 : ℕ) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3962687/50000000) (δ := 317391/10000000000) 1269 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_295 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (295 : ℕ) / 2)) - ((-1317733/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log (295 : ℕ) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (295 : ℕ) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45937331/100000000) (δ := 317391/10000000000) 1269 574
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_296 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (296 : ℕ) / 2)) - ((-3325711/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log (296 : ℕ) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (296 : ℕ) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11492403/20000000) (δ := 79321/2500000000) 1269 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_297 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (297 : ℕ) / 2)) - ((1234331/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log (297 : ℕ) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (297 : ℕ) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3962561/100000000) (δ := 39673/1250000000) 1269 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_298 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (298 : ℕ) / 2)) - ((-3925901/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log (298 : ℕ) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (298 : ℕ) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2467803/5000000) (δ := 79321/2500000000) 1269 575
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_299 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (299 : ℕ) / 2)) - ((-1149843/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log (299 : ℕ) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (299 : ℕ) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13645653/25000000) (δ := 317447/10000000000) 1269 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_300 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (300 : ℕ) / 2)) - ((997903/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log (300 : ℕ) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (300 : ℕ) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -161931/10000000) (δ := 79339/2500000000) 1269 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_301 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (301 : ℕ) / 2)) - ((-4581567/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log (301 : ℕ) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (301 : ℕ) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51167917/100000000) (δ := 317347/10000000000) 1269 576
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_302 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (302 : ℕ) / 2)) - ((-5321709/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log (302 : ℕ) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (302 : ℕ) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2131959/4000000) (δ := 79357/2500000000) 1269 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_303 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (303 : ℕ) / 2)) - ((4997037/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log (303 : ℕ) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (303 : ℕ) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -860723/100000000) (δ := 12691/400000000) 1269 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_304 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (304 : ℕ) / 2)) - ((-4665523/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log (304 : ℕ) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (304 : ℕ) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12851157/25000000) (δ := 2539/80000000) 1269 577
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_305 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (305 : ℕ) / 2)) - ((-27087/50000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log (305 : ℕ) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (305 : ℕ) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26791277/50000000) (δ := 1587/50000000) 1269 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_306 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (306 : ℕ) / 2)) - ((997801/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log (306 : ℕ) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (306 : ℕ) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1658247/100000000) (δ := 317303/10000000000) 1269 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_307 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (307 : ℕ) / 2)) - ((-4195899/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log (307 : ℕ) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (307 : ℕ) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25047373/50000000) (δ := 1587/50000000) 1269 578
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_308 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (308 : ℕ) / 2)) - ((-751703/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log (308 : ℕ) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (308 : ℕ) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55400037/100000000) (δ := 317271/10000000000) 1269 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_309 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (309 : ℕ) / 2)) - ((4936717/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log (309 : ℕ) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (309 : ℕ) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3981743/100000000) (δ := 317371/10000000000) 1269 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_310 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (310 : ℕ) / 2)) - ((-1572849/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log (310 : ℕ) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (310 : ℕ) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23634997/50000000) (δ := 79333/2500000000) 1269 579
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_311 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (311 : ℕ) / 2)) - ((-3509477/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log (311 : ℕ) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (311 : ℕ) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11744257/20000000) (δ := 3967/125000000) 1269 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_312 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (312 : ℕ) / 2)) - ((4758639/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log (312 : ℕ) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (312 : ℕ) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7799487/100000000) (δ := 317343/10000000000) 1269 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_313 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (313 : ℕ) / 2)) - ((-735443/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log (313 : ℕ) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (313 : ℕ) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42960513/100000000) (δ := 317343/10000000000) 1269 580
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_314 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (314 : ℕ) / 2)) - ((-1649817/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log (314 : ℕ) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (314 : ℕ) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -63520917/100000000) (δ := 63483/2000000000) 1269 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_315 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (315 : ℕ) / 2)) - ((4330831/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log (315 : ℕ) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (315 : ℕ) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6541463/50000000) (δ := 63463/2000000000) 1269 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_316 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (316 : ℕ) / 2)) - ((829069/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log (316 : ℕ) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (316 : ℕ) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18597427/50000000) (δ := 63463/2000000000) 1269 581
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_317 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (317 : ℕ) / 2)) - ((-9390623/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log (317 : ℕ) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (317 : ℕ) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6976721/10000000) (δ := 317287/10000000000) 1269 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_318 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (318 : ℕ) / 2)) - ((702233/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log (318 : ℕ) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (318 : ℕ) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -495167/2500000) (δ := 317287/10000000000) 1269 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_319 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (319 : ℕ) / 2)) - ((144967/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log (319 : ℕ) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (319 : ℕ) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29998397/100000000) (δ := 39677/1250000000) 1269 582
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_320 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (320 : ℕ) / 2)) - ((-9990233/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log (320 : ℕ) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (320 : ℕ) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -77434783/100000000) (δ := 63469/2000000000) 1269 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_321 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (321 : ℕ) / 2)) - ((875639/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log (321 : ℕ) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (321 : ℕ) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2794061/10000000) (δ := 158679/5000000000) 1269 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_322 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (322 : ℕ) / 2)) - ((6555207/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log (322 : ℕ) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (322 : ℕ) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2139811/10000000) (δ := 158679/5000000000) 1269 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_323 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (323 : ℕ) / 2)) - ((-593623/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log (323 : ℕ) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (323 : ℕ) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1411691/2000000) (δ := 158679/5000000000) 1269 583
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_324 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (324 : ℕ) / 2)) - ((722963/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log (324 : ℕ) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (324 : ℕ) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37460923/100000000) (δ := 317273/10000000000) 1269 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_325 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (325 : ℕ) / 2)) - ((8974517/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log (325 : ℕ) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (325 : ℕ) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11420957/100000000) (δ := 317273/10000000000) 1269 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_326 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (326 : ℕ) / 2)) - ((-7415333/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log (326 : ℕ) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (326 : ℕ) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6015373/10000000) (δ := 31743/1000000000) 1269 584
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_327 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (327 : ℕ) / 2)) - ((-709961/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log (327 : ℕ) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (327 : ℕ) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24171119/50000000) (δ := 158651/5000000000) 1269 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_328 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (328 : ℕ) / 2)) - ((9999929/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log (328 : ℕ) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (328 : ℕ) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46953/50000000) (δ := 158701/5000000000) 1269 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_329 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (329 : ℕ) / 2)) - ((-1782137/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log (329 : ℕ) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (329 : ℕ) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24190471/50000000) (δ := 158651/5000000000) 1269 585
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_330 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (330 : ℕ) / 2)) - ((-7522743/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log (330 : ℕ) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (330 : ℕ) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6055759/10000000) (δ := 317429/10000000000) 1269 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_331 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (331 : ℕ) / 2)) - ((8763827/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log (331 : ℕ) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (331 : ℕ) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12562423/100000000) (δ := 158687/5000000000) 1269 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_332 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (332 : ℕ) / 2)) - ((792941/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log (332 : ℕ) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (332 : ℕ) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17644197/50000000) (δ := 317329/10000000000) 1269 586
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_333 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (333 : ℕ) / 2)) - ((-246041/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log (333 : ℕ) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (333 : ℕ) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7408477/10000000) (δ := 317357/10000000000) 1269 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_334 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (334 : ℕ) / 2)) - ((4881369/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log (334 : ℕ) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (334 : ℕ) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26521063/100000000) (δ := 158723/5000000000) 1269 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_335 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (335 : ℕ) / 2)) - ((268157/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log (335 : ℕ) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (335 : ℕ) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20901467/100000000) (δ := 158723/5000000000) 1269 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_336 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (336 : ℕ) / 2)) - ((-9153809/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log (336 : ℕ) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (336 : ℕ) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34090617/50000000) (δ := 317257/10000000000) 1269 587
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_337 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (337 : ℕ) / 2)) - ((-993683/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log (337 : ℕ) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (337 : ℕ) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41758221/100000000) (δ := 317317/10000000000) 1269 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_338 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (338 : ℕ) / 2)) - ((9781077/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log (338 : ℕ) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (338 : ℕ) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 262039/5000000) (δ := 158643/5000000000) 1269 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_339 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (339 : ℕ) / 2)) - ((-4910879/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log (339 : ℕ) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (339 : ℕ) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13025841/25000000) (δ := 317317/10000000000) 1269 588
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_340 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (340 : ℕ) / 2)) - ((-688439/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log (340 : ℕ) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (340 : ℕ) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2330131/4000000) (δ := 317289/10000000000) 1269 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_341 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (341 : ℕ) / 2)) - ((4465219/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log (341 : ℕ) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (341 : ℕ) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2333657/20000000) (δ := 317289/10000000000) 1269 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_342 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (342 : ℕ) / 2)) - ((1785587/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log (342 : ℕ) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (342 : ℕ) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17390937/50000000) (δ := 317389/10000000000) 1269 589
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_343 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (343 : ℕ) / 2)) - ((-9947789/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log (343 : ℕ) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (343 : ℕ) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37992009/50000000) (δ := 158671/5000000000) 1269 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_344 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (344 : ℕ) / 2)) - ((29569/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log (344 : ℕ) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (344 : ℕ) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7451277/25000000) (δ := 158671/5000000000) 1269 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_345 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (345 : ℕ) / 2)) - ((7963123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log (345 : ℕ) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (345 : ℕ) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16240557/100000000) (δ := 158671/5000000000) 1269 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_346 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (346 : ℕ) / 2)) - ((-7927207/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log (346 : ℕ) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (346 : ℕ) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 62151391/100000000) (δ := 317261/10000000000) 1269 590
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_347 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (347 : ℕ) / 2)) - ((-3849617/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log (347 : ℕ) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (347 : ℕ) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -49149067/100000000) (δ := 31737/1000000000) 1269 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_348 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (348 : ℕ) / 2)) - ((9902073/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log (348 : ℕ) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (348 : ℕ) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -70031/2000000) (δ := 317433/10000000000) 1269 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_349 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (349 : ℕ) / 2)) - ((-1096187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log (349 : ℕ) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (349 : ℕ) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42015893/100000000) (δ := 31737/1000000000) 1269 591
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_350 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (350 : ℕ) / 2)) - ((-937829/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log (350 : ℕ) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (350 : ℕ) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34838977/50000000) (δ := 63481/2000000000) 1269 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_351 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (351 : ℕ) / 2)) - ((1119311/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log (351 : ℕ) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (351 : ℕ) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1526291/6250000) (δ := 158699/5000000000) 1269 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_352 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (352 : ℕ) / 2)) - ((3380783/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log (352 : ℕ) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (352 : ℕ) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20706571/100000000) (δ := 63481/2000000000) 1269 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_353 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (353 : ℕ) / 2)) - ((-1742241/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log (353 : ℕ) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (353 : ℕ) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 65706897/100000000) (δ := 63461/2000000000) 1269 592
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_354 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (354 : ℕ) / 2)) - ((-1425813/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log (354 : ℕ) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (354 : ℕ) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4649931/10000000) (δ := 317427/10000000000) 1269 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_355 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (355 : ℕ) / 2)) - ((2493847/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log (355 : ℕ) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (355 : ℕ) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -175437/10000000) (δ := 317427/10000000000) 1269 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_356 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (356 : ℕ) / 2)) - ((-286763/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log (356 : ℕ) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (356 : ℕ) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42866843/100000000) (δ := 79319/2500000000) 1269 593
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_357 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (357 : ℕ) / 2)) - ((-293247/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log (357 : ℕ) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (357 : ℕ) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69718477/100000000) (δ := 79337/2500000000) 1269 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_358 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (358 : ℕ) / 2)) - ((5285407/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log (358 : ℕ) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (358 : ℕ) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6336973/25000000) (δ := 79337/2500000000) 1269 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_359 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (359 : ℕ) / 2)) - ((7276143/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log (359 : ℕ) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (359 : ℕ) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3779793/20000000) (δ := 63471/2000000000) 1269 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_360 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (360 : ℕ) / 2)) - ((-8135033/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log (360 : ℕ) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (360 : ℕ) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31511841/50000000) (δ := 39681/1250000000) 1269 594
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_361 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (361 : ℕ) / 2)) - ((-4181449/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log (361 : ℕ) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (361 : ℕ) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25027481/50000000) (δ := 15871/500000000) 1269 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_362 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (362 : ℕ) / 2)) - ((9696549/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log (362 : ℕ) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (362 : ℕ) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6174529/100000000) (δ := 317383/10000000000) 1269 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_363 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (363 : ℕ) / 2)) - ((336973/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log (363 : ℕ) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (363 : ℕ) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9395941/25000000) (δ := 7933/250000000) 1269 595
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_364 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (364 : ℕ) / 2)) - ((-2485631/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log (364 : ℕ) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (364 : ℕ) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75858131/100000000) (δ := 19837/625000000) 1269 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_365 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (365 : ℕ) / 2)) - ((1368423/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log (365 : ℕ) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (365 : ℕ) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32339363/100000000) (δ := 317411/10000000000) 1269 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_366 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (366 : ℕ) / 2)) - ((9037193/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log (366 : ℕ) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (366 : ℕ) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11060437/100000000) (δ := 317411/10000000000) 1269 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_367 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (367 : ℕ) / 2)) - ((-141749/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log (367 : ℕ) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (367 : ℕ) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54341269/100000000) (δ := 19837/625000000) 1269 596
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_368 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (368 : ℕ) / 2)) - ((-290321/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log (368 : ℕ) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (368 : ℕ) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11914983/20000000) (δ := 79341/2500000000) 1269 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_369 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (369 : ℕ) / 2)) - ((3946421/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log (369 : ℕ) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (369 : ℕ) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -16528849/100000000) (δ := 19829/625000000) 1269 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_370 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (370 : ℕ) / 2)) - ((4923081/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log (370 : ℕ) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (370 : ℕ) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26401421/100000000) (δ := 19829/625000000) 1269 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_371 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (371 : ℕ) / 2)) - ((-9312309/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log (371 : ℕ) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (371 : ℕ) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17303577/25000000) (δ := 317439/10000000000) 1269 597
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_372 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (372 : ℕ) / 2)) - ((-1168443/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log (372 : ℕ) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (372 : ℕ) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -45166647/100000000) (δ := 39671/1250000000) 1269 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_373 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (373 : ℕ) / 2)) - ((4973353/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log (373 : ℕ) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (373 : ℕ) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2582179/100000000) (δ := 63467/2000000000) 1269 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_374 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (374 : ℕ) / 2)) - ((-246609/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log (374 : ℕ) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (374 : ℕ) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9971623/25000000) (δ := 79317/2500000000) 1269 598
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_375 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (375 : ℕ) / 2)) - ((-395617/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log (375 : ℕ) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (375 : ℕ) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74835507/100000000) (δ := 19831/625000000) 1269 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_376 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (376 : ℕ) / 2)) - ((2639479/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log (376 : ℕ) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (376 : ℕ) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32592083/100000000) (δ := 317307/10000000000) 1269 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_377 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (377 : ℕ) / 2)) - ((9280891/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log (377 : ℕ) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (377 : ℕ) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9538717/100000000) (δ := 317307/10000000000) 1269 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_378 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (378 : ℕ) / 2)) - ((-2359933/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log (378 : ℕ) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (378 : ℕ) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51558479/100000000) (δ := 79349/2500000000) 1269 599
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_379 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (379 : ℕ) / 2)) - ((-2067341/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log (379 : ℕ) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (379 : ℕ) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31805421/50000000) (δ := 317279/10000000000) 1269 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_380 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (380 : ℕ) / 2)) - ((803617/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log (380 : ℕ) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (380 : ℕ) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4362631/20000000) (δ := 19839/625000000) 1269 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_381 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (381 : ℕ) / 2)) - ((875353/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log (381 : ℕ) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (381 : ℕ) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9937541/50000000) (δ := 317379/10000000000) 1269 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_382 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (382 : ℕ) / 2)) - ((-242327/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log (382 : ℕ) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (382 : ℕ) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61455453/100000000) (δ := 317279/10000000000) 1269 600
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_383 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (383 : ℕ) / 2)) - ((-5608379/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log (383 : ℕ) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (383 : ℕ) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27077423/50000000) (δ := 79313/2500000000) 1269 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_384 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (384 : ℕ) / 2)) - ((1089909/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log (384 : ℕ) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (384 : ℕ) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12791791/100000000) (δ := 79313/2500000000) 1269 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_385 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (385 : ℕ) / 2)) - ((4189243/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log (385 : ℕ) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (385 : ℕ) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28463399/100000000) (δ := 79313/2500000000) 1269 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_386 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (386 : ℕ) / 2)) - ((-4684461/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log (386 : ℕ) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (386 : ℕ) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17402681/25000000) (δ := 79313/2500000000) 1269 601
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_387 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (387 : ℕ) / 2)) - ((-1412111/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log (387 : ℕ) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (387 : ℕ) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23213931/50000000) (δ := 317423/10000000000) 1269 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_388 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (388 : ℕ) / 2)) - ((1951943/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log (388 : ℕ) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (388 : ℕ) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5491509/100000000) (δ := 15869/500000000) 1269 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_389 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (389 : ℕ) / 2)) - ((97879/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log (389 : ℕ) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (389 : ℕ) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17669283/50000000) (δ := 15869/500000000) 1269 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_390 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (390 : ℕ) / 2)) - ((-9951001/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log (390 : ℕ) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (390 : ℕ) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76063949/100000000) (δ := 317323/10000000000) 1269 602
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_391 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (391 : ℕ) / 2)) - ((-224941/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log (391 : ℕ) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (391 : ℕ) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20197497/50000000) (δ := 317309/10000000000) 1269 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_392 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (392 : ℕ) / 2)) - ((249997/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log (392 : ℕ) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (392 : ℕ) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12259/10000000) (δ := 158647/5000000000) 1269 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_393 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (393 : ℕ) / 2)) - ((-506647/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log (393 : ℕ) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (393 : ℕ) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40537067/100000000) (δ := 317409/10000000000) 1269 603
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_394 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (394 : ℕ) / 2)) - ((-622337/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log (394 : ℕ) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (394 : ℕ) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38115597/50000000) (δ := 158633/5000000000) 1269 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_395 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (395 : ℕ) / 2)) - ((1295143/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log (395 : ℕ) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (395 : ℕ) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36022929/100000000) (δ := 158633/5000000000) 1269 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_396 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (396 : ℕ) / 2)) - ((9866773/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log (396 : ℕ) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (396 : ℕ) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2042701/50000000) (δ := 317337/10000000000) 1269 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_397 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (397 : ℕ) / 2)) - ((-47909/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log (397 : ℕ) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (397 : ℕ) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44090627/100000000) (δ := 317337/10000000000) 1269 604
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_398 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (398 : ℕ) / 2)) - ((-4881327/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log (398 : ℕ) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (398 : ℕ) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4567633/6250000) (δ := 63453/2000000000) 1269 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_399 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (399 : ℕ) / 2)) - ((59359/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log (399 : ℕ) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (399 : ℕ) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3327677/10000000) (δ := 158719/5000000000) 1269 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_400 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (400 : ℕ) / 2)) - ((9671197/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log (400 : ℕ) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (400 : ℕ) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6428653/100000000) (δ := 63473/2000000000) 1269 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_401 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (401 : ℕ) / 2)) - ((-2673413/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log (401 : ℕ) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (401 : ℕ) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4603573/10000000) (δ := 158719/5000000000) 1269 605
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_402 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (402 : ℕ) / 2)) - ((-9610217/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log (402 : ℕ) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (402 : ℕ) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -71536761/100000000) (δ := 317393/10000000000) 1269 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_403 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (403 : ℕ) / 2)) - ((1409343/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log (403 : ℕ) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (403 : ℕ) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32126379/100000000) (δ := 31741/1000000000) 1269 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_404 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (404 : ℕ) / 2)) - ((9589767/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log (404 : ℕ) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (404 : ℕ) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3592827/50000000) (δ := 317393/10000000000) 1269 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_405 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (405 : ℕ) / 2)) - ((-562777/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log (405 : ℕ) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (405 : ℕ) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46400927/100000000) (δ := 31731/1000000000) 1269 606
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_406 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (406 : ℕ) / 2)) - ((-2403201/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log (406 : ℕ) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (406 : ℕ) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14312039/20000000) (δ := 317421/10000000000) 1269 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_407 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (407 : ℕ) / 2)) - ((332521/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log (407 : ℕ) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (407 : ℕ) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6507689/20000000) (δ := 317421/10000000000) 1269 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_408 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (408 : ℕ) / 2)) - ((9675307/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log (408 : ℕ) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (408 : ℕ) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 638813/10000000) (δ := 317421/10000000000) 1269 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_409 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (409 : ℕ) / 2)) - ((-294681/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log (409 : ℕ) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (409 : ℕ) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4521953/10000000) (δ := 317421/10000000000) 1269 607
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_410 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (410 : ℕ) / 2)) - ((-9766257/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log (410 : ℕ) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (410 : ℕ) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73123877/100000000) (δ := 317353/10000000000) 1269 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_411 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (411 : ℕ) / 2)) - ((76151/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log (411 : ℕ) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (411 : ℕ) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34481241/100000000) (δ := 317253/10000000000) 1269 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_412 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (412 : ℕ) / 2)) - ((4934009/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log (412 : ℕ) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (412 : ℕ) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 203311/5000000) (δ := 6347/200000000) 1269 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_413 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (413 : ℕ) / 2)) - ((-259283/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log (413 : ℕ) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (413 : ℕ) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42520093/100000000) (δ := 317353/10000000000) 1269 608
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_414 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (414 : ℕ) / 2)) - ((-9956147/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log (414 : ℕ) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (414 : ℕ) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7619767/10000000) (δ := 158639/5000000000) 1269 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_415 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (415 : ℕ) / 2)) - ((107317/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log (415 : ℕ) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (415 : ℕ) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18963901/50000000) (δ := 12697/400000000) 1269 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_416 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (416 : ℕ) / 2)) - ((4999753/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log (416 : ℕ) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (416 : ℕ) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 62119/25000000) (δ := 158689/5000000000) 1269 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_417 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (417 : ℕ) / 2)) - ((18707/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log (417 : ℕ) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (417 : ℕ) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38334339/100000000) (δ := 12693/400000000) 1269 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_418 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (418 : ℕ) / 2)) - ((-155639/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log (418 : ℕ) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (418 : ℕ) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76328199/100000000) (δ := 12693/400000000) 1269 609
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_419 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (419 : ℕ) / 2)) - ((-1426351/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log (419 : ℕ) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (419 : ℕ) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4284799/10000000) (δ := 317297/10000000000) 1269 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_420 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (420 : ℕ) / 2)) - ((4898939/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log (420 : ℕ) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (420 : ℕ) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5034963/100000000) (δ := 158703/5000000000) 1269 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_421 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (421 : ℕ) / 2)) - ((2602589/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log (421 : ℕ) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (421 : ℕ) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32687649/100000000) (δ := 317397/10000000000) 1269 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_422 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (422 : ℕ) / 2)) - ((-4732257/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log (422 : ℕ) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (422 : ℕ) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7032143/10000000) (δ := 317297/10000000000) 1269 610
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_423 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (423 : ℕ) / 2)) - ((-774777/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log (423 : ℕ) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (423 : ℕ) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24607419/50000000) (δ := 158667/5000000000) 1269 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_424 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (424 : ℕ) / 2)) - ((8914103/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log (424 : ℕ) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (424 : ℕ) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11758717/100000000) (δ := 158717/5000000000) 1269 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_425 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (425 : ℕ) / 2)) - ((5196603/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log (425 : ℕ) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (425 : ℕ) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1024343/4000000) (δ := 317369/10000000000) 1269 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_426 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (426 : ℕ) / 2)) - ((-1012937/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log (426 : ℕ) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (426 : ℕ) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31444311/50000000) (δ := 158667/5000000000) 1269 611
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_427 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (427 : ℕ) / 2)) - ((-813969/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log (427 : ℕ) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (427 : ℕ) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56998207/100000000) (δ := 158681/5000000000) 1269 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_428 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (428 : ℕ) / 2)) - ((3498677/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log (428 : ℕ) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (428 : ℕ) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19894233/100000000) (δ := 158631/5000000000) 1269 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_429 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (429 : ℕ) / 2)) - ((7744021/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log (429 : ℕ) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (429 : ℕ) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1712567/10000000) (δ := 317441/10000000000) 1269 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_430 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (430 : ℕ) / 2)) - ((-5576373/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log (430 : ℕ) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (430 : ℕ) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6757291/12500000) (δ := 158681/5000000000) 1269 612
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_431 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (431 : ℕ) / 2)) - ((-880179/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log (431 : ℕ) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (431 : ℕ) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66175889/100000000) (δ := 79353/2500000000) 1269 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_432 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (432 : ℕ) / 2)) - ((384083/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log (432 : ℕ) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (432 : ℕ) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14707273/50000000) (δ := 317391/10000000000) 1269 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_433 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (433 : ℕ) / 2)) - ((4790491/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log (433 : ℕ) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (433 : ℕ) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7262727/100000000) (δ := 2479/78125000) 1269 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_434 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (434 : ℕ) / 2)) - ((-1823513/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log (434 : ℕ) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (434 : ℕ) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21927171/50000000) (δ := 2479/78125000) 1269 613
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_435 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (435 : ℕ) / 2)) - ((-2493363/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log (435 : ℕ) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (435 : ℕ) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -76717747/100000000) (δ := 79321/2500000000) 1269 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_436 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (436 : ℕ) / 2)) - ((-12801/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log (436 : ℕ) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (436 : ℕ) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1611771/4000000) (δ := 317419/10000000000) 1269 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_437 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (437 : ℕ) / 2)) - ((9875133/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log (437 : ℕ) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (437 : ℕ) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3954873/100000000) (δ := 39673/1250000000) 1269 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_438 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (438 : ℕ) / 2)) - ((2750591/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log (438 : ℕ) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (438 : ℕ) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32303629/100000000) (δ := 317319/10000000000) 1269 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_439 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (439 : ℕ) / 2)) - ((-4600481/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log (439 : ℕ) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (439 : ℕ) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3423903/5000000) (δ := 317419/10000000000) 1269 614
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_440 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (440 : ℕ) / 2)) - ((-631473/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log (440 : ℕ) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (440 : ℕ) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26254813/50000000) (δ := 39657/1250000000) 1269 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_441 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (441 : ℕ) / 2)) - ((3949941/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log (441 : ℕ) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (441 : ℕ) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3300033/20000000) (δ := 317347/10000000000) 1269 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_442 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (442 : ℕ) / 2)) - ((7129249/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log (442 : ℕ) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (442 : ℕ) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9714199/50000000) (δ := 79339/2500000000) 1269 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_443 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (443 : ℕ) / 2)) - ((-746741/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log (443 : ℕ) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (443 : ℕ) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 55276061/100000000) (δ := 317447/10000000000) 1269 615
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_444 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (444 : ℕ) / 2)) - ((-548453/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log (444 : ℕ) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (444 : ℕ) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33018403/50000000) (δ := 19833/625000000) 1269 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_445 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (445 : ℕ) / 2)) - ((3492389/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log (445 : ℕ) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (445 : ℕ) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1517547/5000000) (δ := 12691/400000000) 1269 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_446 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (446 : ℕ) / 2)) - ((9779841/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log (446 : ℕ) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (446 : ℕ) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2627807/50000000) (δ := 19833/625000000) 1269 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_447 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (447 : ℕ) / 2)) - ((-37761/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log (447 : ℕ) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (447 : ℕ) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40781269/100000000) (δ := 19833/625000000) 1269 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_448 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (448 : ℕ) / 2)) - ((-9957319/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log (448 : ℕ) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (448 : ℕ) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38114599/50000000) (δ := 79357/2500000000) 1269 616
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_449 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (449 : ℕ) / 2)) - ((-245989/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log (449 : ℕ) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (449 : ℕ) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9096681/20000000) (δ := 3173/100000000) 1269 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_450 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (450 : ℕ) / 2)) - ((4590049/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log (450 : ℕ) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (450 : ℕ) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10194101/100000000) (δ := 1587/50000000) 1269 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_451 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (451 : ℕ) / 2)) - ((269857/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log (451 : ℕ) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (451 : ℕ) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6254369/25000000) (δ := 317303/10000000000) 1269 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_452 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (452 : ℕ) / 2)) - ((-3707131/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log (452 : ℕ) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (452 : ℕ) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60149741/100000000) (δ := 317303/10000000000) 1269 617
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_453 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (453 : ℕ) / 2)) - ((-314361/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log (453 : ℕ) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (453 : ℕ) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61873767/100000000) (δ := 39679/1250000000) 1269 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_454 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (454 : ℕ) / 2)) - ((1187399/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log (454 : ℕ) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (454 : ℕ) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13448477/50000000) (δ := 317271/10000000000) 1269 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_455 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (455 : ℕ) / 2)) - ((4745843/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log (455 : ℕ) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (455 : ℕ) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1601061/20000000) (δ := 317371/10000000000) 1269 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_456 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (456 : ℕ) / 2)) - ((-354791/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log (456 : ℕ) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (456 : ℕ) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42829837/100000000) (δ := 79333/2500000000) 1269 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_457 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (457 : ℕ) / 2)) - ((-9992579/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log (457 : ℕ) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (457 : ℕ) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 77576643/100000000) (δ := 39679/1250000000) 1269 618
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_458 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (458 : ℕ) / 2)) - ((-441207/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log (458 : ℕ) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (458 : ℕ) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -44830737/100000000) (δ := 3967/125000000) 1269 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_459 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (459 : ℕ) / 2)) - ((9173911/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log (459 : ℕ) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (459 : ℕ) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5116519/50000000) (δ := 15863/500000000) 1269 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_460 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (460 : ℕ) / 2)) - ((2820401/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log (460 : ℕ) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (460 : ℕ) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4857387/20000000) (δ := 317443/10000000000) 1269 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_461 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (461 : ℕ) / 2)) - ((-7022559/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log (461 : ℕ) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (461 : ℕ) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2936697/5000000) (δ := 317443/10000000000) 1269 619
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_462 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (462 : ℕ) / 2)) - ((-521897/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log (462 : ℕ) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (462 : ℕ) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15993707/25000000) (δ := 63463/2000000000) 1269 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_463 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (463 : ℕ) / 2)) - ((3743717/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log (463 : ℕ) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (463 : ℕ) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29676931/100000000) (δ := 79347/2500000000) 1269 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_464 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (464 : ℕ) / 2)) - ((1229387/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log (464 : ℕ) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (464 : ℕ) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4546413/100000000) (δ := 39661/1250000000) 1269 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_465 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (465 : ℕ) / 2)) - ((57307/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log (465 : ℕ) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (465 : ℕ) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38696789/100000000) (δ := 79347/2500000000) 1269 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_466 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (466 : ℕ) / 2)) - ((-9735093/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log (466 : ℕ) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (466 : ℕ) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18193153/25000000) (δ := 63463/2000000000) 1269 620
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_467 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (467 : ℕ) / 2)) - ((-4271789/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log (467 : ℕ) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (467 : ℕ) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25152083/50000000) (δ := 79329/2500000000) 1269 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_468 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (468 : ℕ) / 2)) - ((1586131/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log (468 : ℕ) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (468 : ℕ) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8187139/50000000) (δ := 317387/10000000000) 1269 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_469 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (469 : ℕ) / 2)) - ((1530497/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log (469 : ℕ) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (469 : ℕ) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4371057/25000000) (δ := 317287/10000000000) 1269 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_470 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (470 : ℕ) / 2)) - ((-2308871/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log (470 : ℕ) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (470 : ℕ) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51269767/100000000) (δ := 317387/10000000000) 1269 621
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_471 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (471 : ℕ) / 2)) - ((-9669623/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log (471 : ℕ) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (471 : ℕ) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -72095709/100000000) (δ := 79361/2500000000) 1269 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_472 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (472 : ℕ) / 2)) - ((81683/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log (472 : ℕ) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (472 : ℕ) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9613233/25000000) (δ := 317359/10000000000) 1269 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_473 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (473 : ℕ) / 2)) - ((980997/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log (473 : ℕ) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (473 : ℕ) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4881537/100000000) (δ := 317359/10000000000) 1269 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_474 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (474 : ℕ) / 2)) - ((206613/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log (474 : ℕ) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (474 : ℕ) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 28620063/100000000) (δ := 317359/10000000000) 1269 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_475 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (475 : ℕ) / 2)) - ((-987811/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log (475 : ℕ) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (475 : ℕ) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 62050281/100000000) (δ := 79361/2500000000) 1269 622
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_476 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (476 : ℕ) / 2)) - ((-7808493/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log (476 : ℕ) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (476 : ℕ) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30835257/50000000) (δ := 317373/10000000000) 1269 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_477 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (477 : ℕ) / 2)) - ((2109489/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log (477 : ℕ) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (477 : ℕ) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28381471/100000000) (δ := 31733/1000000000) 1269 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_478 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (478 : ℕ) / 2)) - ((9813229/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log (478 : ℕ) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (478 : ℕ) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4839363/100000000) (δ := 31743/1000000000) 1269 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_479 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (479 : ℕ) / 2)) - ((512213/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log (479 : ℕ) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (479 : ℕ) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7597763/20000000) (δ := 317273/10000000000) 1269 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_480 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (480 : ℕ) / 2)) - ((-14933/15625 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log (480 : ℕ) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (480 : ℕ) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14214329/20000000) (δ := 317273/10000000000) 1269 623
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_481 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (481 : ℕ) / 2)) - ((-5218901/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log (481 : ℕ) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (481 : ℕ) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -52996539/100000000) (δ := 317301/10000000000) 1269 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_482 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (482 : ℕ) / 2)) - ((3476107/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log (482 : ℕ) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (482 : ℕ) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20051713/100000000) (δ := 317401/10000000000) 1269 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_483 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (483 : ℕ) / 2)) - ((871309/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log (483 : ℕ) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (483 : ℕ) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12823319/100000000) (δ := 158701/5000000000) 1269 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_484 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (484 : ℕ) / 2)) - ((-314669/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log (484 : ℕ) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (484 : ℕ) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45631727/100000000) (δ := 317401/10000000000) 1269 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_485 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (485 : ℕ) / 2)) - ((-999977/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log (485 : ℕ) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (485 : ℕ) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 78370341/100000000) (δ := 317301/10000000000) 1269 624
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_486 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (486 : ℕ) / 2)) - ((-2673407/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log (486 : ℕ) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (486 : ℕ) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23017857/50000000) (δ := 158637/5000000000) 1269 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_487 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (487 : ℕ) / 2)) - ((4295689/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log (487 : ℕ) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (487 : ℕ) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2686069/20000000) (δ := 158687/5000000000) 1269 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_488 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (488 : ℕ) / 2)) - ((360921/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log (488 : ℕ) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (488 : ℕ) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19108401/100000000) (δ := 158637/5000000000) 1269 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_489 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (489 : ℕ) / 2)) - ((-4727079/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log (489 : ℕ) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (489 : ℕ) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25789469/50000000) (δ := 317429/10000000000) 1269 625
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_490 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (490 : ℕ) / 2)) - ((-1220473/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log (490 : ℕ) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (490 : ℕ) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73095193/100000000) (δ := 317257/10000000000) 1269 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_491 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (491 : ℕ) / 2)) - ((-593579/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log (491 : ℕ) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (491 : ℕ) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5094341/12500000) (δ := 317257/10000000000) 1269 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_492 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (492 : ℕ) / 2)) - ((4715047/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log (492 : ℕ) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (492 : ℕ) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1696177/20000000) (δ := 158723/5000000000) 1269 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_493 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (493 : ℕ) / 2)) - ((364033/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log (493 : ℕ) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (493 : ℕ) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4745267/20000000) (δ := 158723/5000000000) 1269 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_494 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (494 : ℕ) / 2)) - ((-6162781/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log (494 : ℕ) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (494 : ℕ) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11174021/20000000) (δ := 158723/5000000000) 1269 626
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_495 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (495 : ℕ) / 2)) - ((-2325079/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log (495 : ℕ) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (495 : ℕ) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69132381/100000000) (δ := 63477/2000000000) 1269 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_496 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (496 : ℕ) / 2)) - ((859429/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log (496 : ℕ) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (496 : ℕ) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37118683/100000000) (δ := 158659/5000000000) 1269 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_497 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (497 : ℕ) / 2)) - ((611683/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log (497 : ℕ) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (497 : ℕ) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2585011/50000000) (δ := 63457/2000000000) 1269 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_498 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (498 : ℕ) / 2)) - ((601751/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log (498 : ℕ) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (498 : ℕ) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26713603/100000000) (δ := 63457/2000000000) 1269 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_499 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (499 : ℕ) / 2)) - ((-3482667/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log (499 : ℕ) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (499 : ℕ) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29266889/50000000) (δ := 63457/2000000000) 1269 627
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_500 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (500 : ℕ) / 2)) - ((-8915559/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log (500 : ℕ) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (500 : ℕ) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6678913/10000000) (δ := 158707/5000000000) 1269 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_501 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (501 : ℕ) / 2)) - ((1662501/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62166061/20000000 : ℚ) : ℝ) ≤ Real.log (501 : ℕ) / 2 := by
    have h := (log_br_501).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (501 : ℕ) / 2 ≤ ((31083031/10000000 : ℚ) : ℝ) := by
    have h := (log_br_501).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8773567/25000000) (δ := 317389/10000000000) 1269 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_502 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (502 : ℕ) / 2)) - ((1980827/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62186001/20000000 : ℚ) : ℝ) ≤ Real.log (502 : ℕ) / 2 := by
    have h := (log_br_502).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (502 : ℕ) / 2 ≤ ((31093001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_502).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3464443/100000000) (δ := 317389/10000000000) 1269 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_503 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (503 : ℕ) / 2)) - ((4320089/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62205901/20000000 : ℚ) : ℝ) ≤ Real.log (503 : ℕ) / 2 := by
    have h := (log_br_503).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (503 : ℕ) / 2 ≤ ((31102951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_503).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7025483/25000000) (δ := 317389/10000000000) 1269 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_504 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (504 : ℕ) / 2)) - ((-1453339/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31112881/10000000 : ℚ) : ℝ) ≤ Real.log (504 : ℕ) / 2 := by
    have h := (log_br_504).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (504 : ℕ) / 2 ≤ ((62225763/20000000 : ℚ) : ℝ) := by
    have h := (log_br_504).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 59606443/100000000) (δ := 317289/10000000000) 1269 628
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_505 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (505 : ℕ) / 2)) - ((-4387023/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3890349/1250000 : ℚ) : ℝ) ≤ Real.log (505 : ℕ) / 2 := by
    have h := (log_br_505).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (505 : ℕ) / 2 ≤ ((12449117/4000000 : ℚ) : ℝ) := by
    have h := (log_br_505).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33015271/50000000) (δ := 317361/10000000000) 1269 629
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_506 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (506 : ℕ) / 2)) - ((918467/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31132683/10000000 : ℚ) : ℝ) ≤ Real.log (506 : ℕ) / 2 := by
    have h := (log_br_506).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (506 : ℕ) / 2 ≤ ((62265367/20000000 : ℚ) : ℝ) := by
    have h := (log_br_506).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6930269/20000000) (δ := 158671/5000000000) 1269 629
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_507 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (507 : ℕ) / 2)) - ((9911291/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6228511/2000000 : ℚ) : ℝ) ≤ Real.log (507 : ℕ) / 2 := by
    have h := (log_br_507).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (507 : ℕ) / 2 ≤ ((62285111/20000000 : ℚ) : ℝ) := by
    have h := (log_br_507).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -133297/4000000) (δ := 158671/5000000000) 1269 629
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_508 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (508 : ℕ) / 2)) - ((4384511/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31152407/10000000 : ℚ) : ℝ) ≤ Real.log (508 : ℕ) / 2 := by
    have h := (log_br_508).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (508 : ℕ) / 2 ≤ ((12460963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_508).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5584609/20000000) (δ := 158671/5000000000) 1269 629
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_509 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (509 : ℕ) / 2)) - ((-7131161/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((48691/15625 : ℚ) : ℝ) ≤ Real.log (509 : ℕ) / 2 := by
    have h := (log_br_509).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (509 : ℕ) / 2 ≤ ((62324481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_509).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29559119/50000000) (δ := 317361/10000000000) 1269 629
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_510 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (510 : ℕ) / 2)) - ((-4461301/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62344107/20000000 : ℚ) : ℝ) ≤ Real.log (510 : ℕ) / 2 := by
    have h := (log_br_510).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (510 : ℕ) / 2 ≤ ((15586027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_510).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33414033/50000000) (δ := 317333/10000000000) 1269 630
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_511 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (511 : ℕ) / 2)) - ((700351/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12472739/4000000 : ℚ) : ℝ) ≤ Real.log (511 : ℕ) / 2 := by
    have h := (log_br_511).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (511 : ℕ) / 2 ≤ ((3897731/1250000 : ℚ) : ℝ) := by
    have h := (log_br_511).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35756601/100000000) (δ := 317333/10000000000) 1269 630
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_512 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (512 : ℕ) / 2)) - ((2455127/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31191623/10000000 : ℚ) : ℝ) ≤ Real.log (512 : ℕ) / 2 := by
    have h := (log_br_512).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (512 : ℕ) / 2 ≤ ((62383247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_512).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4743827/100000000) (δ := 317433/10000000000) 1269 630
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_513 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (513 : ℕ) / 2)) - ((2495297/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31201379/10000000 : ℚ) : ℝ) ≤ Real.log (513 : ℕ) / 2 := by
    have h := (log_br_513).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (513 : ℕ) / 2 ≤ ((62402759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_513).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26207083/100000000) (δ := 317433/10000000000) 1269 630
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_514 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (514 : ℕ) / 2)) - ((-1635477/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7802779/2500000 : ℚ) : ℝ) ≤ Real.log (514 : ℕ) / 2 := by
    have h := (log_br_514).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (514 : ℕ) / 2 ≤ ((62422233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_514).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11419543/20000000) (δ := 31727/1000000000) 1269 630
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_515 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (515 : ℕ) / 2)) - ((-93029/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62441669/20000000 : ℚ) : ℝ) ≤ Real.log (515 : ℕ) / 2 := by
    have h := (log_br_515).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (515 : ℕ) / 2 ≤ ((6244167/2000000 : ℚ) : ℝ) := by
    have h := (log_br_515).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8643747/12500000) (δ := 63481/2000000000) 1269 631
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_516 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (516 : ℕ) / 2)) - ((44491/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62461067/20000000 : ℚ) : ℝ) ≤ Real.log (516 : ℕ) / 2 := by
    have h := (log_br_516).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (516 : ℕ) / 2 ≤ ((15615267/5000000 : ℚ) : ℝ) := by
    have h := (log_br_516).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38379899/100000000) (δ := 158649/5000000000) 1269 631
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_517 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (517 : ℕ) / 2)) - ((2383307/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15620107/5000000 : ℚ) : ℝ) ≤ Real.log (517 : ℕ) / 2 := by
    have h := (log_br_517).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (517 : ℕ) / 2 ≤ ((62480429/20000000 : ℚ) : ℝ) := by
    have h := (log_br_517).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7668513/100000000) (δ := 158699/5000000000) 1269 631
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_518 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (518 : ℕ) / 2)) - ((3031617/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7812469/2500000 : ℚ) : ℝ) ≤ Real.log (518 : ℕ) / 2 := by
    have h := (log_br_518).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (518 : ℕ) / 2 ≤ ((62499753/20000000 : ℚ) : ℝ) := by
    have h := (log_br_518).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11492091/50000000) (δ := 158699/5000000000) 1269 631
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_519 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (519 : ℕ) / 2)) - ((-2707699/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31259519/10000000 : ℚ) : ℝ) ≤ Real.log (519 : ℕ) / 2 := by
    have h := (log_br_519).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (519 : ℕ) / 2 ≤ ((62519039/20000000 : ℚ) : ℝ) := by
    have h := (log_br_519).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 267883/500000) (δ := 63461/2000000000) 1269 631
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_520 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (520 : ℕ) / 2)) - ((-9752641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3908643/1250000 : ℚ) : ℝ) ≤ Real.log (520 : ℕ) / 2 := by
    have h := (log_br_520).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (520 : ℕ) / 2 ≤ ((62538289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_520).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1824193/2500000) (δ := 4959/156250000) 1269 632
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_521 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (521 : ℕ) / 2)) - ((-1285543/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((25023/8000 : ℚ) : ℝ) ≤ Real.log (521 : ℕ) / 2 := by
    have h := (log_br_521).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (521 : ℕ) / 2 ≤ ((62557501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_521).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8498537/20000000) (δ := 4959/156250000) 1269 632
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_522 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (522 : ℕ) / 2)) - ((8855807/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2503067/800000 : ℚ) : ℝ) ≤ Real.log (522 : ℕ) / 2 := by
    have h := (log_br_522).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (522 : ℕ) / 2 ≤ ((15644169/5000000 : ℚ) : ℝ) := by
    have h := (log_br_522).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6038171/50000000) (δ := 317427/10000000000) 1269 632
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_523 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (523 : ℕ) / 2)) - ((3721481/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31297907/10000000 : ℚ) : ℝ) ≤ Real.log (523 : ℕ) / 2 := by
    have h := (log_br_523).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (523 : ℕ) / 2 ≤ ((12519163/4000000 : ℚ) : ℝ) := by
    have h := (log_br_523).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18282897/100000000) (δ := 317327/10000000000) 1269 632
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_524 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (524 : ℕ) / 2)) - ((-3639837/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15653729/5000000 : ℚ) : ℝ) ≤ Real.log (524 : ℕ) / 2 := by
    have h := (log_br_524).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (524 : ℕ) / 2 ≤ ((62614917/20000000 : ℚ) : ℝ) := by
    have h := (log_br_524).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9716689/20000000) (δ := 4959/156250000) 1269 632
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_525 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (525 : ℕ) / 2)) - ((-9999341/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31316991/10000000 : ℚ) : ℝ) ≤ Real.log (525 : ℕ) / 2 := by
    have h := (log_br_525).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (525 : ℕ) / 2 ≤ ((62633983/20000000 : ℚ) : ℝ) := by
    have h := (log_br_525).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15650549/20000000) (δ := 39681/1250000000) 1269 633
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_526 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (526 : ℕ) / 2)) - ((-861611/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15663253/5000000 : ℚ) : ℝ) ≤ Real.log (526 : ℕ) / 2 := by
    have h := (log_br_526).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (526 : ℕ) / 2 ≤ ((62653013/20000000 : ℚ) : ℝ) := by
    have h := (log_br_526).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6008301/12500000) (δ := 63451/2000000000) 1269 633
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_527 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (527 : ℕ) / 2)) - ((3767093/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12534401/4000000 : ℚ) : ℝ) ≤ Real.log (527 : ℕ) / 2 := by
    have h := (log_br_527).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (527 : ℕ) / 2 ≤ ((31336003/10000000 : ℚ) : ℝ) := by
    have h := (log_br_527).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8969381/50000000) (δ := 63471/2000000000) 1269 633
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_528 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (528 : ℕ) / 2)) - ((1769097/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31345481/10000000 : ℚ) : ℝ) ≤ Real.log (528 : ℕ) / 2 := by
    have h := (log_br_528).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (528 : ℕ) / 2 ≤ ((62690963/20000000 : ℚ) : ℝ) := by
    have h := (log_br_528).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 606589/5000000) (δ := 39681/1250000000) 1269 633
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_529 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (529 : ℕ) / 2)) - ((-1148219/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15677471/5000000 : ℚ) : ℝ) ≤ Real.log (529 : ℕ) / 2 := by
    have h := (log_br_529).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (529 : ℕ) / 2 ≤ ((12541977/4000000 : ℚ) : ℝ) := by
    have h := (log_br_529).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21073401/50000000) (δ := 63451/2000000000) 1269 633
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_530 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (530 : ℕ) / 2)) - ((-9670541/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6272877/2000000 : ℚ) : ℝ) ≤ Real.log (530 : ℕ) / 2 := by
    have h := (log_br_530).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (530 : ℕ) / 2 ≤ ((62728771/20000000 : ℚ) : ℝ) := by
    have h := (log_br_530).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 901309/1250000) (δ := 39681/1250000000) 1269 633
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_531 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (531 : ℕ) / 2)) - ((-5908949/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3137381/1000000 : ℚ) : ℝ) ≤ Real.log (531 : ℕ) / 2 := by
    have h := (log_br_531).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (531 : ℕ) / 2 ≤ ((62747621/20000000 : ℚ) : ℝ) := by
    have h := (log_br_531).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55074101/100000000) (δ := 317383/10000000000) 1269 634
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_532 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (532 : ℕ) / 2)) - ((5325247/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31383217/10000000 : ℚ) : ℝ) ≤ Real.log (532 : ℕ) / 2 := by
    have h := (log_br_532).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (532 : ℕ) / 2 ≤ ((12553287/4000000 : ℚ) : ℝ) := by
    have h := (log_br_532).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25230393/100000000) (δ := 7933/250000000) 1269 634
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_533 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (533 : ℕ) / 2)) - ((9834157/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31392607/10000000 : ℚ) : ℝ) ≤ Real.log (533 : ℕ) / 2 := by
    have h := (log_br_533).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (533 : ℕ) / 2 ≤ ((12557043/4000000 : ℚ) : ℝ) := by
    have h := (log_br_533).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2279691/50000000) (δ := 7933/250000000) 1269 634
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_534 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (534 : ℕ) / 2)) - ((494503/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31401979/10000000 : ℚ) : ℝ) ≤ Real.log (534 : ℕ) / 2 := by
    have h := (log_br_534).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (534 : ℕ) / 2 ≤ ((62803959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_534).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8573013/25000000) (δ := 7933/250000000) 1269 634
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_535 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (535 : ℕ) / 2)) - ((-4174557/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62822667/20000000 : ℚ) : ℝ) ≤ Real.log (535 : ℕ) / 2 := by
    have h := (log_br_535).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (535 : ℕ) / 2 ≤ ((15705667/5000000 : ℚ) : ℝ) := by
    have h := (log_br_535).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 63969203/100000000) (δ := 317283/10000000000) 1269 634
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_536 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (536 : ℕ) / 2)) - ((-1030227/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62841341/20000000 : ℚ) : ℝ) ≤ Real.log (536 : ℕ) / 2 := by
    have h := (log_br_536).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (536 : ℕ) / 2 ≤ ((31420671/10000000 : ℚ) : ℝ) := by
    have h := (log_br_536).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -63488797/100000000) (δ := 79323/2500000000) 1269 635
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_537 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (537 : ℕ) / 2)) - ((2122619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3142999/1000000 : ℚ) : ℝ) ≤ Real.log (537 : ℕ) / 2 := by
    have h := (log_br_537).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (537 : ℕ) / 2 ≤ ((62859981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_537).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33922683/100000000) (δ := 19837/625000000) 1269 635
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_538 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (538 : ℕ) / 2)) - ((9844783/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12575717/4000000 : ℚ) : ℝ) ≤ Real.log (538 : ℕ) / 2 := by
    have h := (log_br_538).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (538 : ℕ) / 2 ≤ ((31439293/10000000 : ℚ) : ℝ) := by
    have h := (log_br_538).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2205251/50000000) (δ := 79323/2500000000) 1269 635
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_539 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (539 : ℕ) / 2)) - ((5387477/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12579431/4000000 : ℚ) : ℝ) ≤ Real.log (539 : ℕ) / 2 := by
    have h := (log_br_539).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (539 : ℕ) / 2 ≤ ((15724289/5000000 : ℚ) : ℝ) := by
    have h := (log_br_539).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 313077/1250000) (δ := 317411/10000000000) 1269 635
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_540 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (540 : ℕ) / 2)) - ((-713171/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62915691/20000000 : ℚ) : ℝ) ≤ Real.log (540 : ℕ) / 2 := by
    have h := (log_br_540).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (540 : ℕ) / 2 ≤ ((15728923/5000000 : ℚ) : ℝ) := by
    have h := (log_br_540).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5444889/10000000) (δ := 317411/10000000000) 1269 635
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_541 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (541 : ℕ) / 2)) - ((-1955957/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3933387/1250000 : ℚ) : ℝ) ≤ Real.log (541 : ℕ) / 2 := by
    have h := (log_br_541).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (541 : ℕ) / 2 ≤ ((62934193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_541).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73283531/100000000) (δ := 19829/625000000) 1269 636
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_542 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (542 : ℕ) / 2)) - ((-469079/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3147633/1000000 : ℚ) : ℝ) ≤ Real.log (542 : ℕ) / 2 := by
    have h := (log_br_542).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (542 : ℕ) / 2 ≤ ((62952661/20000000 : ℚ) : ℝ) := by
    have h := (log_br_542).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21994333/50000000) (δ := 19829/625000000) 1269 636
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_543 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (543 : ℕ) / 2)) - ((4154779/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((62971093/20000000 : ℚ) : ℝ) ≤ Real.log (543 : ℕ) / 2 := by
    have h := (log_br_543).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (543 : ℕ) / 2 ≤ ((31485547/10000000 : ℚ) : ℝ) := by
    have h := (log_br_543).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -368733/2500000) (δ := 317339/10000000000) 1269 636
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_544 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (544 : ℕ) / 2)) - ((523663/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15747373/5000000 : ℚ) : ℝ) ≤ Real.log (544 : ℕ) / 2 := by
    have h := (log_br_544).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (544 : ℕ) / 2 ≤ ((62989493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_544).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7218047/50000000) (δ := 19829/625000000) 1269 636
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_545 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (545 : ℕ) / 2)) - ((-427653/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63007857/20000000 : ℚ) : ℝ) ≤ Real.log (545 : ℕ) / 2 := by
    have h := (log_br_545).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (545 : ℕ) / 2 ≤ ((31503929/10000000 : ℚ) : ℝ) := by
    have h := (log_br_545).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1742703/4000000) (δ := 317339/10000000000) 1269 636
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_546 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (546 : ℕ) / 2)) - ((-4861727/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63026189/20000000 : ℚ) : ℝ) ≤ Real.log (546 : ℕ) / 2 := by
    have h := (log_br_546).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (546 : ℕ) / 2 ≤ ((6302619/2000000 : ℚ) : ℝ) := by
    have h := (log_br_546).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7264671/10000000) (δ := 317339/10000000000) 1269 636
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_547 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (547 : ℕ) / 2)) - ((-1503893/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7880561/2500000 : ℚ) : ℝ) ≤ Real.log (547 : ℕ) / 2 := by
    have h := (log_br_547).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (547 : ℕ) / 2 ≤ ((63044489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_547).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27703067/50000000) (δ := 39671/1250000000) 1269 637
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_548 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (548 : ℕ) / 2)) - ((4911433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1970711/625000 : ℚ) : ℝ) ≤ Real.log (548 : ℕ) / 2 := by
    have h := (log_br_548).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (548 : ℕ) / 2 ≤ ((63062753/20000000 : ℚ) : ℝ) := by
    have h := (log_br_548).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1652179/6250000) (δ := 39671/1250000000) 1269 637
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_549 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (549 : ℕ) / 2)) - ((9950613/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7885123/2500000 : ℚ) : ℝ) ≤ Real.log (549 : ℕ) / 2 := by
    have h := (log_br_549).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (549 : ℕ) / 2 ≤ ((12616197/4000000 : ℚ) : ℝ) := by
    have h := (log_br_549).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1242823/50000000) (δ := 39671/1250000000) 1269 637
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_550 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (550 : ℕ) / 2)) - ((1557197/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31549591/10000000 : ℚ) : ℝ) ≤ Real.log (550 : ℕ) / 2 := by
    have h := (log_br_550).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (550 : ℕ) / 2 ≤ ((63099183/20000000 : ℚ) : ℝ) := by
    have h := (log_br_550).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 979757/3125000) (δ := 63467/2000000000) 1269 637
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_551 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (551 : ℕ) / 2)) - ((-1854793/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15779337/5000000 : ℚ) : ℝ) ≤ Real.log (551 : ℕ) / 2 := by
    have h := (log_br_551).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (551 : ℕ) / 2 ≤ ((63117349/20000000 : ℚ) : ℝ) := by
    have h := (log_br_551).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60168041/100000000) (δ := 39671/1250000000) 1269 637
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_552 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (552 : ℕ) / 2)) - ((-365949/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1578387/500000 : ℚ) : ℝ) ≤ Real.log (552 : ℕ) / 2 := by
    have h := (log_br_552).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (552 : ℕ) / 2 ≤ ((63135481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_552).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -34074853/50000000) (δ := 317407/10000000000) 1269 638
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_553 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (553 : ℕ) / 2)) - ((-67469/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3157679/1000000 : ℚ) : ℝ) ≤ Real.log (553 : ℕ) / 2 := by
    have h := (log_br_553).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (553 : ℕ) / 2 ≤ ((63153581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_553).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -39438581/100000000) (δ := 317407/10000000000) 1269 638
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_554 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (554 : ℕ) / 2)) - ((70972/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31585823/10000000 : ℚ) : ℝ) ≤ Real.log (554 : ℕ) / 2 := by
    have h := (log_br_554).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (554 : ℕ) / 2 ≤ ((63171647/20000000 : ℚ) : ℝ) := by
    have h := (log_br_554).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10781389/100000000) (δ := 19831/625000000) 1269 638
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_555 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (555 : ℕ) / 2)) - ((7563603/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63189681/20000000 : ℚ) : ℝ) ≤ Real.log (555 : ℕ) / 2 := by
    have h := (log_br_555).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (555 : ℕ) / 2 ≤ ((31594841/10000000 : ℚ) : ℝ) := by
    have h := (log_br_555).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1782663/10000000) (δ := 317307/10000000000) 1269 638
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_556 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (556 : ℕ) / 2)) - ((-1403063/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31603841/10000000 : ℚ) : ℝ) ≤ Real.log (556 : ℕ) / 2 := by
    have h := (log_br_556).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (556 : ℕ) / 2 ≤ ((63207683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_556).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11595179/25000000) (δ := 19831/625000000) 1269 638
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_557 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (557 : ℕ) / 2)) - ((-1978673/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15806413/5000000 : ℚ) : ℝ) ≤ Real.log (557 : ℕ) / 2 := by
    have h := (log_br_557).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (557 : ℕ) / 2 ≤ ((63225653/20000000 : ℚ) : ℝ) := by
    have h := (log_br_557).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 74885629/100000000) (δ := 317407/10000000000) 1269 638
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_558 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (558 : ℕ) / 2)) - ((-547071/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63243589/20000000 : ℚ) : ℝ) ≤ Real.log (558 : ℕ) / 2 := by
    have h := (log_br_558).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (558 : ℕ) / 2 ≤ ((6324359/2000000 : ℚ) : ℝ) := by
    have h := (log_br_558).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26870719/50000000) (δ := 79331/2500000000) 1269 639
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_559 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (559 : ℕ) / 2)) - ((1322053/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31630747/10000000 : ℚ) : ℝ) ≤ Real.log (559 : ℕ) / 2 := by
    have h := (log_br_559).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (559 : ℕ) / 2 ≤ ((12652299/4000000 : ℚ) : ℝ) := by
    have h := (log_br_559).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1583727/6250000) (δ := 19839/625000000) 1269 639
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_560 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (560 : ℕ) / 2)) - ((9927539/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63279367/20000000 : ℚ) : ℝ) ≤ Real.log (560 : ℕ) / 2 := by
    have h := (log_br_560).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (560 : ℕ) / 2 ≤ ((7909921/2500000 : ℚ) : ℝ) := by
    have h := (log_br_560).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 602283/20000000) (δ := 317379/10000000000) 1269 639
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_561 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (561 : ℕ) / 2)) - ((312919/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63297209/20000000 : ℚ) : ℝ) ≤ Real.log (561 : ℕ) / 2 := by
    have h := (log_br_561).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (561 : ℕ) / 2 ≤ ((6329721/2000000 : ℚ) : ℝ) := by
    have h := (log_br_561).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31313287/100000000) (δ := 79331/2500000000) 1269 639
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_562 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (562 : ℕ) / 2)) - ((-3627347/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31657509/10000000 : ℚ) : ℝ) ≤ Real.log (562 : ℕ) / 2 := by
    have h := (log_br_562).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (562 : ℕ) / 2 ≤ ((63315019/20000000 : ℚ) : ℝ) := by
    have h := (log_br_562).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 59562813/100000000) (δ := 19839/625000000) 1269 639
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_563 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (563 : ℕ) / 2)) - ((-9327123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15833199/5000000 : ℚ) : ℝ) ≤ Real.log (563 : ℕ) / 2 := by
    have h := (log_br_563).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (563 : ℕ) / 2 ≤ ((63332797/20000000 : ℚ) : ℝ) := by
    have h := (log_br_563).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69316467/100000000) (δ := 39669/1250000000) 1269 640
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_564 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (564 : ℕ) / 2)) - ((-379029/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31675271/10000000 : ℚ) : ℝ) ≤ Real.log (564 : ℕ) / 2 := by
    have h := (log_br_564).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (564 : ℕ) / 2 ≤ ((63350543/20000000 : ℚ) : ℝ) := by
    have h := (log_br_564).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20583437/50000000) (δ := 317351/10000000000) 1269 640
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_565 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (565 : ℕ) / 2)) - ((8664953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63368257/20000000 : ℚ) : ℝ) ≤ Real.log (565 : ℕ) / 2 := by
    have h := (log_br_565).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (565 : ℕ) / 2 ≤ ((31684129/10000000 : ℚ) : ℝ) := by
    have h := (log_br_565).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2613291/20000000) (δ := 317451/10000000000) 1269 640
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_566 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (566 : ℕ) / 2)) - ((2064287/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3169297/1000000 : ℚ) : ℝ) ≤ Real.log (566 : ℕ) / 2 := by
    have h := (log_br_566).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (566 : ℕ) / 2 ≤ ((63385941/20000000 : ℚ) : ℝ) := by
    have h := (log_br_566).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14983203/100000000) (δ := 39669/1250000000) 1269 640
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_567 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (567 : ℕ) / 2)) - ((-740341/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63403593/20000000 : ℚ) : ℝ) ≤ Real.log (567 : ℕ) / 2 := by
    have h := (log_br_567).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (567 : ℕ) / 2 ≤ ((31701797/10000000 : ℚ) : ℝ) := by
    have h := (log_br_567).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1719411/4000000) (δ := 317451/10000000000) 1269 640
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_568 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (568 : ℕ) / 2)) - ((-9541081/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31710607/10000000 : ℚ) : ℝ) ≤ Real.log (568 : ℕ) / 2 := by
    have h := (log_br_568).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (568 : ℕ) / 2 ≤ ((12684243/4000000 : ℚ) : ℝ) := by
    have h := (log_br_568).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35468293/50000000) (δ := 317351/10000000000) 1269 640
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_569 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (569 : ℕ) / 2)) - ((-3440401/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15859701/5000000 : ℚ) : ℝ) ≤ Real.log (569 : ℕ) / 2 := by
    have h := (log_br_569).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (569 : ℕ) / 2 ≤ ((12687761/4000000 : ℚ) : ℝ) := by
    have h := (log_br_569).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -58240909/100000000) (δ := 317423/10000000000) 1269 641
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_570 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (570 : ℕ) / 2)) - ((695703/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63456363/20000000 : ℚ) : ℝ) ≤ Real.log (570 : ℕ) / 2 := by
    have h := (log_br_570).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (570 : ℕ) / 2 ≤ ((15864091/5000000 : ℚ) : ℝ) := by
    have h := (log_br_570).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15193973/50000000) (δ := 15869/500000000) 1269 641
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_571 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (571 : ℕ) / 2)) - ((994669/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15868473/5000000 : ℚ) : ℝ) ≤ Real.log (571 : ℕ) / 2 := by
    have h := (log_br_571).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (571 : ℕ) / 2 ≤ ((63473893/20000000 : ℚ) : ℝ) := by
    have h := (log_br_571).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2582569/100000000) (δ := 317423/10000000000) 1269 641
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_572 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (572 : ℕ) / 2)) - ((5344987/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63491389/20000000 : ℚ) : ℝ) ≤ Real.log (572 : ℕ) / 2 := by
    have h := (log_br_572).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (572 : ℕ) / 2 ≤ ((6349139/2000000 : ℚ) : ℝ) := by
    have h := (log_br_572).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25172047/100000000) (δ := 317323/10000000000) 1269 641
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_573 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (573 : ℕ) / 2)) - ((-5179307/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63508857/20000000 : ℚ) : ℝ) ≤ Real.log (573 : ℕ) / 2 := by
    have h := (log_br_573).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (573 : ℕ) / 2 ≤ ((31754429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_573).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26440331/50000000) (δ := 317323/10000000000) 1269 641
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_574 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (574 : ℕ) / 2)) - ((-9968059/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63526293/20000000 : ℚ) : ℝ) ≤ Real.log (574 : ℕ) / 2 := by
    have h := (log_br_574).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (574 : ℕ) / 2 ≤ ((31763147/10000000 : ℚ) : ℝ) := by
    have h := (log_br_574).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -19135279/25000000) (δ := 317309/10000000000) 1269 642
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_575 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (575 : ℕ) / 2)) - ((-3768323/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((635437/200000 : ℚ) : ℝ) ≤ Real.log (575 : ℕ) / 2 := by
    have h := (log_br_575).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (575 : ℕ) / 2 ≤ ((63543701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_575).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24464631/50000000) (δ := 158647/5000000000) 1269 642
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_576 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (576 : ℕ) / 2)) - ((3282363/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((15890269/5000000 : ℚ) : ℝ) ≤ Real.log (576 : ℕ) / 2 := by
    have h := (log_br_576).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (576 : ℕ) / 2 ≤ ((63561077/20000000 : ℚ) : ℝ) := by
    have h := (log_br_576).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10683291/50000000) (δ := 158647/5000000000) 1269 642
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_577 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (577 : ℕ) / 2)) - ((606193/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31789211/10000000 : ℚ) : ℝ) ≤ Real.log (577 : ℕ) / 2 := by
    have h := (log_br_577).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (577 : ℕ) / 2 ≤ ((63578423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_577).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 614851/10000000) (δ := 317409/10000000000) 1269 642
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_578 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (578 : ℕ) / 2)) - ((280291/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31797869/10000000 : ℚ) : ℝ) ≤ Real.log (578 : ℕ) / 2 := by
    have h := (log_br_578).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (578 : ℕ) / 2 ≤ ((63595739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_578).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6723203/20000000) (δ := 317409/10000000000) 1269 642
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_579 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (579 : ℕ) / 2)) - ((-7647421/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1987907/625000 : ℚ) : ℝ) ≤ Real.log (579 : ℕ) / 2 := by
    have h := (log_br_579).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (579 : ℕ) / 2 ≤ ((2544521/800000 : ℚ) : ℝ) := by
    have h := (log_br_579).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61035933/100000000) (δ := 158647/5000000000) 1269 642
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_580 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (580 : ℕ) / 2)) - ((-923073/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63630281/20000000 : ℚ) : ℝ) ≤ Real.log (580 : ℕ) / 2 := by
    have h := (log_br_580).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (580 : ℕ) / 2 ≤ ((31815141/10000000 : ℚ) : ℝ) := by
    have h := (log_br_580).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8583723/12500000) (δ := 317437/10000000000) 1269 643
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_581 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (581 : ℕ) / 2)) - ((-8291/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63647507/20000000 : ℚ) : ℝ) ≤ Real.log (581 : ℕ) / 2 := by
    have h := (log_br_581).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (581 : ℕ) / 2 ≤ ((15911877/5000000 : ℚ) : ℝ) := by
    have h := (log_br_581).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41345041/100000000) (δ := 158633/5000000000) 1269 643
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_582 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (582 : ℕ) / 2)) - ((4229217/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((994761/312500 : ℚ) : ℝ) ≤ Real.log (582 : ℕ) / 2 := by
    have h := (log_br_582).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (582 : ℕ) / 2 ≤ ((12732941/4000000 : ℚ) : ℝ) := by
    have h := (log_br_582).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -140663/1000000) (δ := 317337/10000000000) 1269 643
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_583 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (583 : ℕ) / 2)) - ((4322619/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63681871/20000000 : ℚ) : ℝ) ≤ Real.log (583 : ℕ) / 2 := by
    have h := (log_br_583).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (583 : ℕ) / 2 ≤ ((3980117/1250000 : ℚ) : ℝ) := by
    have h := (log_br_583).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6582427/50000000) (δ := 158633/5000000000) 1269 643
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_584 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (584 : ℕ) / 2)) - ((-86381/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63699009/20000000 : ℚ) : ℝ) ≤ Real.log (584 : ℕ) / 2 := by
    have h := (log_br_584).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (584 : ℕ) / 2 ≤ ((6369901/2000000 : ℚ) : ℝ) := by
    have h := (log_br_584).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20175003/50000000) (δ := 317437/10000000000) 1269 643
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_585 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (585 : ℕ) / 2)) - ((-9038867/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31858059/10000000 : ℚ) : ℝ) ≤ Real.log (585 : ℕ) / 2 := by
    have h := (log_br_585).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (585 : ℕ) / 2 ≤ ((63716119/20000000 : ℚ) : ℝ) := by
    have h := (log_br_585).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33744579/50000000) (δ := 158683/5000000000) 1269 643
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_586 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (586 : ℕ) / 2)) - ((-320447/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63733197/20000000 : ℚ) : ℝ) ≤ Real.log (586 : ℕ) / 2 := by
    have h := (log_br_586).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (586 : ℕ) / 2 ≤ ((31866599/10000000 : ℚ) : ℝ) := by
    have h := (log_br_586).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62498911/100000000) (δ := 158669/5000000000) 1269 644
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_587 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (587 : ℕ) / 2)) - ((95083/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((7968781/2500000 : ℚ) : ℝ) ≤ Real.log (587 : ℕ) / 2 := by
    have h := (log_br_587).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (587 : ℕ) / 2 ≤ ((63750249/20000000 : ℚ) : ℝ) := by
    have h := (log_br_587).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17725881/50000000) (δ := 158719/5000000000) 1269 644
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_588 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (588 : ℕ) / 2)) - ((4716953/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63767269/20000000 : ℚ) : ℝ) ≤ Real.log (588 : ℕ) / 2 := by
    have h := (log_br_588).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (588 : ℕ) / 2 ≤ ((6376727/2000000 : ℚ) : ℝ) := by
    have h := (log_br_588).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8452201/100000000) (δ := 158669/5000000000) 1269 644
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_589 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (589 : ℕ) / 2)) - ((7384319/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63784261/20000000 : ℚ) : ℝ) ≤ Real.log (589 : ℕ) / 2 := by
    have h := (log_br_589).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (589 : ℕ) / 2 ≤ ((31892131/10000000 : ℚ) : ℝ) := by
    have h := (log_br_589).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18501359/100000000) (δ := 158669/5000000000) 1269 644
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_590 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (590 : ℕ) / 2)) - ((-486323/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2552049/800000 : ℚ) : ℝ) ≤ Real.log (590 : ℕ) / 2 := by
    have h := (log_br_590).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (590 : ℕ) / 2 ≤ ((31900613/10000000 : ℚ) : ℝ) := by
    have h := (log_br_590).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5676313/12500000) (δ := 158669/5000000000) 1269 644
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_591 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (591 : ℕ) / 2)) - ((-4843761/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((797727/250000 : ℚ) : ℝ) ≤ Real.log (591 : ℕ) / 2 := by
    have h := (log_br_591).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (591 : ℕ) / 2 ≤ ((63818161/20000000 : ℚ) : ℝ) := by
    have h := (log_br_591).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4517103/6250000) (δ := 158719/5000000000) 1269 644
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_592 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (592 : ℕ) / 2)) - ((-680729/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31917533/10000000 : ℚ) : ℝ) ≤ Real.log (592 : ℕ) / 2 := by
    have h := (log_br_592).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (592 : ℕ) / 2 ≤ ((63835067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_592).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57988843/100000000) (δ := 317393/10000000000) 1269 645
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_593 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (593 : ℕ) / 2)) - ((3165481/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31925971/10000000 : ℚ) : ℝ) ≤ Real.log (593 : ℕ) / 2 := by
    have h := (log_br_593).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (593 : ℕ) / 2 ≤ ((12770389/4000000 : ℚ) : ℝ) := by
    have h := (log_br_593).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31217701/100000000) (δ := 95191/1000000000) 1269 645
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_594 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (594 : ℕ) / 2)) - ((2459799/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63868793/20000000 : ℚ) : ℝ) ≤ Real.log (594 : ℕ) / 2 := by
    have h := (log_br_594).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (594 : ℕ) / 2 ≤ ((31934397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_594).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4489389/100000000) (δ := 317293/10000000000) 1269 645
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_595 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (595 : ℕ) / 2)) - ((1262369/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31942807/10000000 : ℚ) : ℝ) ≤ Real.log (595 : ℕ) / 2 := by
    have h := (log_br_595).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (595 : ℕ) / 2 ≤ ((12777123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_595).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11096461/50000000) (δ := 317393/10000000000) 1269 645
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_596 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (596 : ℕ) / 2)) - ((-3731231/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((31951203/10000000 : ℚ) : ℝ) ≤ Real.log (596 : ℕ) / 2 := by
    have h := (log_br_596).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (596 : ℕ) / 2 ≤ ((63902407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_596).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3051827/6250000) (δ := 317393/10000000000) 1269 645
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_597 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (597 : ℕ) / 2)) - ((-992237/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63919171/20000000 : ℚ) : ℝ) ≤ Real.log (597 : ℕ) / 2 := by
    have h := (log_br_597).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (597 : ℕ) / 2 ≤ ((15979793/5000000 : ℚ) : ℝ) := by
    have h := (log_br_597).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37711357/50000000) (δ := 31741/1000000000) 1269 645
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_598 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (598 : ℕ) / 2)) - ((-5920347/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63935907/20000000 : ℚ) : ℝ) ≤ Real.log (598 : ℕ) / 2 := by
    have h := (log_br_598).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (598 : ℕ) / 2 ≤ ((15983977/5000000 : ℚ) : ℝ) := by
    have h := (log_br_598).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -55109439/100000000) (δ := 158641/5000000000) 1269 646
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_599 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (599 : ℕ) / 2)) - ((827449/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12790523/4000000 : ℚ) : ℝ) ≤ Real.log (599 : ℕ) / 2 := by
    have h := (log_br_599).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (599 : ℕ) / 2 ≤ ((7994077/2500000 : ℚ) : ℝ) := by
    have h := (log_br_599).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14303187/50000000) (δ := 158641/5000000000) 1269 646
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_600 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (600 : ℕ) / 2)) - ((398527/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3998081/1250000 : ℚ) : ℝ) ≤ Real.log (600 : ℕ) / 2 := by
    have h := (log_br_600).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (600 : ℕ) / 2 ≤ ((63969297/20000000 : ℚ) : ℝ) := by
    have h := (log_br_600).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1073069/50000000) (δ := 317321/10000000000) 1269 646
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_601 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (601 : ℕ) / 2)) - ((5646499/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((63985949/20000000 : ℚ) : ℝ) ≤ Real.log (601 : ℕ) / 2 := by
    have h := (log_br_601).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (601 : ℕ) / 2 ≤ ((1279719/400000 : ℚ) : ℝ) := by
    have h := (log_br_601).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24269683/100000000) (δ := 317421/10000000000) 1269 646
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_602 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (602 : ℕ) / 2)) - ((-4393251/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32001287/10000000 : ℚ) : ℝ) ≤ Real.log (602 : ℕ) / 2 := by
    have h := (log_br_602).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (602 : ℕ) / 2 ≤ ((2560103/800000 : ℚ) : ℝ) := by
    have h := (log_br_602).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5064109/10000000) (δ := 158691/5000000000) 1269 646
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_603 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (603 : ℕ) / 2)) - ((-2495061/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64019171/20000000 : ℚ) : ℝ) ≤ Real.log (603 : ℕ) / 2 := by
    have h := (log_br_603).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (603 : ℕ) / 2 ≤ ((16004793/5000000 : ℚ) : ℝ) := by
    have h := (log_br_603).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76968081/100000000) (δ := 158641/5000000000) 1269 646
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_604 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (604 : ℕ) / 2)) - ((-5499457/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64035741/20000000 : ℚ) : ℝ) ≤ Real.log (604 : ℕ) / 2 := by
    have h := (log_br_604).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (604 : ℕ) / 2 ≤ ((32017871/10000000 : ℚ) : ℝ) := by
    have h := (log_br_604).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53827389/100000000) (δ := 317353/10000000000) 1269 647
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_605 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (605 : ℕ) / 2)) - ((4505257/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16013071/5000000 : ℚ) : ℝ) ≤ Real.log (605 : ℕ) / 2 := by
    have h := (log_br_605).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (605 : ℕ) / 2 ≤ ((12810457/4000000 : ℚ) : ℝ) := by
    have h := (log_br_605).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3448257/12500000) (δ := 6349/200000000) 1269 647
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_606 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (606 : ℕ) / 2)) - ((4992283/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64068799/20000000 : ℚ) : ℝ) ≤ Real.log (606 : ℕ) / 2 := by
    have h := (log_br_606).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (606 : ℕ) / 2 ≤ ((40043/12500 : ℚ) : ℝ) := by
    have h := (log_br_606).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1389137/100000000) (δ := 6347/200000000) 1269 647
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_607 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (607 : ℕ) / 2)) - ((5481897/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64085287/20000000 : ℚ) : ℝ) ≤ Real.log (607 : ℕ) / 2 := by
    have h := (log_br_607).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (607 : ℕ) / 2 ≤ ((8010661/2500000 : ℚ) : ℝ) := by
    have h := (log_br_607).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24764953/100000000) (δ := 6347/200000000) 1269 647
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_608 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (608 : ℕ) / 2)) - ((-4477543/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16025437/5000000 : ℚ) : ℝ) ≤ Real.log (608 : ℕ) / 2 := by
    have h := (log_br_608).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (608 : ℕ) / 2 ≤ ((64101749/20000000 : ℚ) : ℝ) := by
    have h := (log_br_608).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25438107/50000000) (δ := 6349/200000000) 1269 647
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_609 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (609 : ℕ) / 2)) - ((-199593/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32059091/10000000 : ℚ) : ℝ) ≤ Real.log (609 : ℕ) / 2 := by
    have h := (log_br_609).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (609 : ℕ) / 2 ≤ ((64118183/20000000 : ℚ) : ℝ) := by
    have h := (log_br_609).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 76944647/100000000) (δ := 317253/10000000000) 1269 647
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_610 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (610 : ℕ) / 2)) - ((-2796657/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64134589/20000000 : ℚ) : ℝ) ≤ Real.log (610 : ℕ) / 2 := by
    have h := (log_br_610).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (610 : ℕ) / 2 ≤ ((6413459/2000000 : ℚ) : ℝ) := by
    have h := (log_br_610).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27054691/50000000) (δ := 158639/5000000000) 1269 648
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_611 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (611 : ℕ) / 2)) - ((862237/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64150969/20000000 : ℚ) : ℝ) ≤ Real.log (611 : ℕ) / 2 := by
    have h := (log_br_611).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (611 : ℕ) / 2 ≤ ((6415097/2000000 : ℚ) : ℝ) := by
    have h := (log_br_611).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28126607/100000000) (δ := 158639/5000000000) 1269 648
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_612 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (612 : ℕ) / 2)) - ((2490443/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32083661/10000000 : ℚ) : ℝ) ≤ Real.log (612 : ℕ) / 2 := by
    have h := (log_br_612).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (612 : ℕ) / 2 ≤ ((64167323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_612).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2186661/100000000) (δ := 158689/5000000000) 1269 648
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_613 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (613 : ℕ) / 2)) - ((2914587/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64183649/20000000 : ℚ) : ℝ) ≤ Real.log (613 : ℕ) / 2 := by
    have h := (log_br_613).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (613 : ℕ) / 2 ≤ ((1283673/400000 : ℚ) : ℝ) := by
    have h := (log_br_613).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23712043/100000000) (δ := 158639/5000000000) 1269 648
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_614 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (614 : ℕ) / 2)) - ((-2001849/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64199949/20000000 : ℚ) : ℝ) ≤ Real.log (614 : ℕ) / 2 := by
    have h := (log_br_614).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (614 : ℕ) / 2 ≤ ((1283999/400000 : ℚ) : ℝ) := by
    have h := (log_br_614).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24783959/50000000) (δ := 158639/5000000000) 1269 648
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_615 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (615 : ℕ) / 2)) - ((-9920279/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32108111/10000000 : ℚ) : ℝ) ≤ Real.log (615 : ℕ) / 2 := by
    have h := (log_br_615).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (615 : ℕ) / 2 ≤ ((64216223/20000000 : ℚ) : ℝ) := by
    have h := (log_br_615).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18845241/25000000) (δ := 158689/5000000000) 1269 648
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_616 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (616 : ℕ) / 2)) - ((-1236129/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64232469/20000000 : ℚ) : ℝ) ≤ Real.log (616 : ℕ) / 2 := by
    have h := (log_br_616).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (616 : ℕ) / 2 ≤ ((6423247/2000000 : ℚ) : ℝ) := by
    have h := (log_br_616).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11185373/20000000) (δ := 158703/5000000000) 1269 649
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_617 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (617 : ℕ) / 2)) - ((1775141/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6424869/2000000 : ℚ) : ℝ) ≤ Real.log (617 : ℕ) / 2 := by
    have h := (log_br_617).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (617 : ℕ) / 2 ≤ ((64248691/20000000 : ℚ) : ℝ) := by
    have h := (log_br_617).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30196303/100000000) (δ := 317397/10000000000) 1269 649
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_618 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (618 : ℕ) / 2)) - ((9837823/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16066221/5000000 : ℚ) : ℝ) ≤ Real.log (618 : ℕ) / 2 := by
    have h := (log_br_618).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (618 : ℕ) / 2 ≤ ((12852977/4000000 : ℚ) : ℝ) := by
    have h := (log_br_618).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4508571/100000000) (δ := 158653/5000000000) 1269 649
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_619 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (619 : ℕ) / 2)) - ((6633447/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16070263/5000000 : ℚ) : ℝ) ≤ Real.log (619 : ℕ) / 2 := by
    have h := (log_br_619).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (619 : ℕ) / 2 ≤ ((64281053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_619).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21137919/100000000) (δ := 158653/5000000000) 1269 649
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_620 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (620 : ℕ) / 2)) - ((-1472491/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32148597/10000000 : ℚ) : ℝ) ≤ Real.log (620 : ℕ) / 2 := by
    have h := (log_br_620).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (620 : ℕ) / 2 ≤ ((12859439/4000000 : ℚ) : ℝ) := by
    have h := (log_br_620).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 46743167/100000000) (δ := 317397/10000000000) 1269 649
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_621 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (621 : ℕ) / 2)) - ((-9690839/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6431331/2000000 : ℚ) : ℝ) ≤ Real.log (621 : ℕ) / 2 := by
    have h := (log_br_621).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (621 : ℕ) / 2 ≤ ((64313311/20000000 : ℚ) : ℝ) := by
    have h := (log_br_621).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18076793/25000000) (δ := 317397/10000000000) 1269 649
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_622 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (622 : ℕ) / 2)) - ((-7167927/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((321647/100000 : ℚ) : ℝ) ≤ Real.log (622 : ℕ) / 2 := by
    have h := (log_br_622).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (622 : ℕ) / 2 ≤ ((64329401/20000000 : ℚ) : ℝ) := by
    have h := (log_br_622).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59249699/100000000) (δ := 158717/5000000000) 1269 650
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_623 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (623 : ℕ) / 2)) - ((2183591/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12869093/4000000 : ℚ) : ℝ) ≤ Real.log (623 : ℕ) / 2 := by
    have h := (log_br_623).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (623 : ℕ) / 2 ≤ ((32172733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_623).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -527603/1562500) (δ := 317369/10000000000) 1269 650
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_624 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (624 : ℕ) / 2)) - ((1181311/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64361503/20000000 : ℚ) : ℝ) ≤ Real.log (624 : ℕ) / 2 := by
    have h := (log_br_624).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (624 : ℕ) / 2 ≤ ((2011297/625000 : ℚ) : ℝ) := by
    have h := (log_br_624).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1665263/20000000) (δ := 158667/5000000000) 1269 650
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_625 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (625 : ℕ) / 2)) - ((1939251/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16094379/5000000 : ℚ) : ℝ) ≤ Real.log (625 : ℕ) / 2 := by
    have h := (log_br_625).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (625 : ℕ) / 2 ≤ ((64377517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_625).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8537153/50000000) (δ := 158717/5000000000) 1269 650
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_626 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (626 : ℕ) / 2)) - ((-157767/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64393503/20000000 : ℚ) : ℝ) ≤ Real.log (626 : ℕ) / 2 := by
    have h := (log_br_626).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (626 : ℕ) / 2 ≤ ((2012297/625000 : ℚ) : ℝ) := by
    have h := (log_br_626).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8486737/20000000) (δ := 158667/5000000000) 1269 650
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_627 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (627 : ℕ) / 2)) - ((-9083577/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12881893/4000000 : ℚ) : ℝ) ≤ Real.log (627 : ℕ) / 2 := by
    have h := (log_br_627).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (627 : ℕ) / 2 ≤ ((32204733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_627).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1058647/1562500) (δ := 317369/10000000000) 1269 650
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_628 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (628 : ℕ) / 2)) - ((-2091591/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64425401/20000000 : ℚ) : ℝ) ≤ Real.log (628 : ℕ) / 2 := by
    have h := (log_br_628).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (628 : ℕ) / 2 ≤ ((32212701/10000000 : ℚ) : ℝ) := by
    have h := (log_br_628).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12809549/20000000) (δ := 158631/5000000000) 1269 651
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_629 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (629 : ℕ) / 2)) - ((2881/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2013791/625000 : ℚ) : ℝ) ≤ Real.log (629 : ℕ) / 2 := by
    have h := (log_br_629).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (629 : ℕ) / 2 ≤ ((64441313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_629).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38808921/100000000) (δ := 317341/10000000000) 1269 651
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_630 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (630 : ℕ) / 2)) - ((8554433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32228599/10000000 : ℚ) : ℝ) ≤ Real.log (630 : ℕ) / 2 := by
    have h := (log_br_630).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (630 : ℕ) / 2 ≤ ((64457199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_630).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6804877/50000000) (δ := 158681/5000000000) 1269 651
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_631 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (631 : ℕ) / 2)) - ((4475977/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32236529/10000000 : ℚ) : ℝ) ≤ Real.log (631 : ℕ) / 2 := by
    have h := (log_br_631).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (631 : ℕ) / 2 ≤ ((64473059/20000000 : ℚ) : ℝ) := by
    have h := (log_br_631).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11548171/100000000) (δ := 158681/5000000000) 1269 651
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_632 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (632 : ℕ) / 2)) - ((519753/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64488893/20000000 : ℚ) : ℝ) ≤ Real.log (632 : ℕ) / 2 := by
    have h := (log_br_632).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (632 : ℕ) / 2 ≤ ((32244447/10000000 : ℚ) : ℝ) := by
    have h := (log_br_632).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 916661/2500000) (δ := 158631/5000000000) 1269 651
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_633 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (633 : ℕ) / 2)) - ((-195687/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((503943/156250 : ℚ) : ℝ) ≤ Real.log (633 : ℕ) / 2 := by
    have h := (log_br_633).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (633 : ℕ) / 2 ≤ ((12900941/4000000 : ℚ) : ℝ) := by
    have h := (log_br_633).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61746639/100000000) (δ := 317341/10000000000) 1269 651
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_634 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (634 : ℕ) / 2)) - ((-9460971/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64520489/20000000 : ℚ) : ℝ) ≤ Real.log (634 : ℕ) / 2 := by
    have h := (log_br_634).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (634 : ℕ) / 2 ≤ ((6452049/2000000 : ℚ) : ℝ) := by
    have h := (log_br_634).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35147019/50000000) (δ := 317391/10000000000) 1269 652
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_635 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (635 : ℕ) / 2)) - ((-149167/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8067031/2500000 : ℚ) : ℝ) ≤ Real.log (635 : ℕ) / 2 := by
    have h := (log_br_635).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (635 : ℕ) / 2 ≤ ((64536251/20000000 : ℚ) : ℝ) := by
    have h := (log_br_635).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22647369/50000000) (δ := 951891/10000000000) 1269 652
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_636 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (636 : ℕ) / 2)) - ((214711/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12910397/4000000 : ℚ) : ℝ) ≤ Real.log (636 : ℕ) / 2 := by
    have h := (log_br_636).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (636 : ℕ) / 2 ≤ ((32275993/10000000 : ℚ) : ℝ) := by
    have h := (log_br_636).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5083377/25000000) (δ := 317391/10000000000) 1269 652
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_637 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (637 : ℕ) / 2)) - ((9832069/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4035481/1250000 : ℚ) : ℝ) ≤ Real.log (637 : ℕ) / 2 := by
    have h := (log_br_637).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (637 : ℕ) / 2 ≤ ((64567697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_637).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2294033/50000000) (δ := 317291/10000000000) 1269 652
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_638 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (638 : ℕ) / 2)) - ((3820347/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32291691/10000000 : ℚ) : ℝ) ≤ Real.log (638 : ℕ) / 2 := by
    have h := (log_br_638).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (638 : ℕ) / 2 ≤ ((64583383/20000000 : ℚ) : ℝ) := by
    have h := (log_br_638).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 920937/3125000) (δ := 79353/2500000000) 1269 652
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_639 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (639 : ℕ) / 2)) - ((-1415229/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16149761/5000000 : ℚ) : ℝ) ≤ Real.log (639 : ℕ) / 2 := by
    have h := (log_br_639).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (639 : ℕ) / 2 ≤ ((12919809/4000000 : ℚ) : ℝ) := by
    have h := (log_br_639).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 54313831/100000000) (δ := 317291/10000000000) 1269 652
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_640 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (640 : ℕ) / 2)) - ((-4998663/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64614681/20000000 : ℚ) : ℝ) ≤ Real.log (640 : ℕ) / 2 := by
    have h := (log_br_640).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (640 : ℕ) / 2 ≤ ((32307341/10000000 : ℚ) : ℝ) := by
    have h := (log_br_640).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7796161/10000000) (δ := 39673/1250000000) 1269 653
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_641 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (641 : ℕ) / 2)) - ((-2643309/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32315147/10000000 : ℚ) : ℝ) ≤ Real.log (641 : ℕ) / 2 := by
    have h := (log_br_641).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (641 : ℕ) / 2 ≤ ((12926059/4000000 : ℚ) : ℝ) := by
    have h := (log_br_641).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53195489/100000000) (δ := 79321/2500000000) 1269 653
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_642 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (642 : ℕ) / 2)) - ((32717/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64645883/20000000 : ℚ) : ℝ) ≤ Real.log (642 : ℕ) / 2 := by
    have h := (log_br_642).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (642 : ℕ) / 2 ≤ ((16161471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_642).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14233719/50000000) (δ := 317319/10000000000) 1269 653
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_643 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (643 : ℕ) / 2)) - ((617873/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64661447/20000000 : ℚ) : ℝ) ≤ Real.log (643 : ℕ) / 2 := by
    have h := (log_br_643).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (643 : ℕ) / 2 ≤ ((8082681/2500000 : ℚ) : ℝ) := by
    have h := (log_br_643).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3779043/100000000) (δ := 317319/10000000000) 1269 653
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_644 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (644 : ℕ) / 2)) - ((6712879/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64676987/20000000 : ℚ) : ℝ) ≤ Real.log (644 : ℕ) / 2 := by
    have h := (log_br_644).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (644 : ℕ) / 2 ≤ ((16169247/5000000 : ℚ) : ℝ) := by
    have h := (log_br_644).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10435641/50000000) (δ := 317319/10000000000) 1269 653
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_645 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (645 : ℕ) / 2)) - ((-2459941/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64692503/20000000 : ℚ) : ℝ) ≤ Real.log (645 : ℕ) / 2 := by
    have h := (log_br_645).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (645 : ℕ) / 2 ≤ ((8086563/2500000 : ℚ) : ℝ) := by
    have h := (log_br_645).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45483537/100000000) (δ := 317319/10000000000) 1269 653
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_646 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (646 : ℕ) / 2)) - ((-9429933/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12941599/4000000 : ℚ) : ℝ) ≤ Real.log (646 : ℕ) / 2 := by
    have h := (log_br_646).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (646 : ℕ) / 2 ≤ ((16176999/5000000 : ℚ) : ℝ) := by
    have h := (log_br_646).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35028861/50000000) (δ := 317319/10000000000) 1269 653
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_647 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (647 : ℕ) / 2)) - ((-1601683/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32361731/10000000 : ℚ) : ℝ) ≤ Real.log (647 : ℕ) / 2 := by
    have h := (log_br_647).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (647 : ℕ) / 2 ≤ ((64723463/20000000 : ℚ) : ℝ) := by
    have h := (log_br_647).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31243691/50000000) (δ := 317347/10000000000) 1269 654
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_648 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (648 : ℕ) / 2)) - ((102401/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12947781/4000000 : ℚ) : ℝ) ≤ Real.log (648 : ℕ) / 2 := by
    have h := (log_br_648).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (648 : ℕ) / 2 ≤ ((16184727/5000000 : ℚ) : ℝ) := by
    have h := (log_br_648).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37989337/100000000) (δ := 951847/10000000000) 1269 654
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_649 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (649 : ℕ) / 2)) - ((8571369/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64754327/20000000 : ℚ) : ℝ) ≤ Real.log (649 : ℕ) / 2 := by
    have h := (log_br_649).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (649 : ℕ) / 2 ≤ ((8094291/2500000 : ℚ) : ℝ) := by
    have h := (log_br_649).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -422743/3125000) (δ := 317447/10000000000) 1269 654
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_650 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (650 : ℕ) / 2)) - ((9065473/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64769723/20000000 : ℚ) : ℝ) ≤ Real.log (650 : ℕ) / 2 := by
    have h := (log_br_650).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (650 : ℕ) / 2 ≤ ((16192431/5000000 : ℚ) : ℝ) := by
    have h := (log_br_650).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10894129/100000000) (δ := 317447/10000000000) 1269 654
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_651 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (651 : ℕ) / 2)) - ((794687/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8098137/2500000 : ℚ) : ℝ) ≤ Real.log (651 : ℕ) / 2 := by
    have h := (log_br_651).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (651 : ℕ) / 2 ≤ ((64785097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_651).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35279551/100000000) (δ := 79339/2500000000) 1269 654
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_652 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (652 : ℕ) / 2)) - ((-3636157/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12960089/4000000 : ℚ) : ℝ) ≤ Real.log (652 : ℕ) / 2 := by
    have h := (log_br_652).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (652 : ℕ) / 2 ≤ ((32400223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_652).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29813451/50000000) (δ := 39657/1250000000) 1269 654
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_653 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (653 : ℕ) / 2)) - ((-9767801/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64815771/20000000 : ℚ) : ℝ) ≤ Real.log (653 : ℕ) / 2 := by
    have h := (log_br_653).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (653 : ℕ) / 2 ≤ ((16203943/5000000 : ℚ) : ℝ) := by
    have h := (log_br_653).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73141863/100000000) (δ := 19833/625000000) 1269 655
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_654 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (654 : ℕ) / 2)) - ((-3746009/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64831073/20000000 : ℚ) : ℝ) ≤ Real.log (654 : ℕ) / 2 := by
    have h := (log_br_654).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (654 : ℕ) / 2 ≤ ((32415537/10000000 : ℚ) : ℝ) := by
    have h := (log_br_654).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24434533/50000000) (δ := 2539/80000000) 1269 655
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_655 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (655 : ℕ) / 2)) - ((5526047/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4052897/1250000 : ℚ) : ℝ) ≤ Real.log (655 : ℕ) / 2 := by
    have h := (log_br_655).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (655 : ℕ) / 2 ≤ ((64846353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_655).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1539547/6250000) (δ := 12691/400000000) 1269 655
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_656 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (656 : ℕ) / 2)) - ((999849/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64861607/20000000 : ℚ) : ℝ) ≤ Real.log (656 : ℕ) / 2 := by
    have h := (log_br_656).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (656 : ℕ) / 2 ≤ ((8107701/2500000 : ℚ) : ℝ) := by
    have h := (log_br_656).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -108627/25000000) (δ := 19833/625000000) 1269 655
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_657 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (657 : ℕ) / 2)) - ((2911857/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1621921/500000 : ℚ) : ℝ) ≤ Real.log (657 : ℕ) / 2 := by
    have h := (log_br_657).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (657 : ℕ) / 2 ≤ ((64876841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_657).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11864419/50000000) (δ := 12691/400000000) 1269 655
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_658 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (658 : ℕ) / 2)) - ((-1683303/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64892049/20000000 : ℚ) : ℝ) ≤ Real.log (658 : ℕ) / 2 := by
    have h := (log_br_658).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (658 : ℕ) / 2 ≤ ((1297841/400000 : ℚ) : ℝ) := by
    have h := (log_br_658).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23927057/50000000) (δ := 2539/80000000) 1269 655
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_659 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (659 : ℕ) / 2)) - ((-4826931/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12981447/4000000 : ℚ) : ℝ) ≤ Real.log (659 : ℕ) / 2 := by
    have h := (log_br_659).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (659 : ℕ) / 2 ≤ ((16226809/5000000 : ℚ) : ℝ) := by
    have h := (log_br_659).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 71942907/100000000) (δ := 19833/625000000) 1269 655
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_660 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (660 : ℕ) / 2)) - ((-7659903/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32461199/10000000 : ℚ) : ℝ) ≤ Real.log (660 : ℕ) / 2 := by
    have h := (log_br_660).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (660 : ℕ) / 2 ≤ ((64922399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_660).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61084417/100000000) (δ := 3173/100000000) 1269 656
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_661 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (661 : ℕ) / 2)) - ((879389/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32468769/10000000 : ℚ) : ℝ) ≤ Real.log (661 : ℕ) / 2 := by
    have h := (log_br_661).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (661 : ℕ) / 2 ≤ ((64937539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_661).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2316787/6250000) (δ := 3173/100000000) 1269 656
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_662 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (662 : ℕ) / 2)) - ((4330199/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((12990531/4000000 : ℚ) : ℝ) ≤ Real.log (662 : ℕ) / 2 := by
    have h := (log_br_662).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (662 : ℕ) / 2 ≤ ((4059541/1250000 : ℚ) : ℝ) := by
    have h := (log_br_662).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13089251/100000000) (δ := 317303/10000000000) 1269 656
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_663 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (663 : ℕ) / 2)) - ((9072303/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64967749/20000000 : ℚ) : ℝ) ≤ Real.log (663 : ℕ) / 2 := by
    have h := (log_br_663).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (663 : ℕ) / 2 ≤ ((259871/80000 : ℚ) : ℝ) := by
    have h := (log_br_663).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10853607/100000000) (δ := 1587/50000000) 1269 656
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_664 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (664 : ℕ) / 2)) - ((896789/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((64982821/20000000 : ℚ) : ℝ) ≤ Real.log (664 : ℕ) / 2 := by
    have h := (log_br_664).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (664 : ℕ) / 2 ≤ ((32491411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_664).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34761567/100000000) (δ := 1587/50000000) 1269 656
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_665 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (665 : ℕ) / 2)) - ((-6993769/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6499787/2000000 : ℚ) : ℝ) ≤ Real.log (665 : ℕ) / 2 := by
    have h := (log_br_665).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (665 : ℕ) / 2 ≤ ((64997871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_665).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58633043/100000000) (δ := 3173/100000000) 1269 656
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_666 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (666 : ℕ) / 2)) - ((-9876807/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2031653/625000 : ℚ) : ℝ) ≤ Real.log (666 : ℕ) / 2 := by
    have h := (log_br_666).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (666 : ℕ) / 2 ≤ ((65012897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_666).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -74611597/100000000) (δ := 317371/10000000000) 1269 657
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_667 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (667 : ℕ) / 2)) - ((-4454383/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((650279/200000 : ℚ) : ℝ) ≤ Real.log (667 : ℕ) / 2 := by
    have h := (log_br_667).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (667 : ℕ) / 2 ≤ ((65027901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_667).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25405751/50000000) (δ := 317371/10000000000) 1269 657
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_668 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (668 : ℕ) / 2)) - ((234819/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65042881/20000000 : ℚ) : ℝ) ≤ Real.log (668 : ℕ) / 2 := by
    have h := (log_br_668).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (668 : ℕ) / 2 ≤ ((32521441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_668).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27047891/100000000) (δ := 317271/10000000000) 1269 657
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_669 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (669 : ℕ) / 2)) - ((4955997/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((813223/250000 : ℚ) : ℝ) ≤ Real.log (669 : ℕ) / 2 := by
    have h := (log_br_669).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (669 : ℕ) / 2 ≤ ((65057841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_669).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3319177/100000000) (δ := 317371/10000000000) 1269 657
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_670 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (670 : ℕ) / 2)) - ((6858789/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8134097/2500000 : ℚ) : ℝ) ≤ Real.log (670 : ℕ) / 2 := by
    have h := (log_br_670).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (670 : ℕ) / 2 ≤ ((65072779/20000000 : ℚ) : ℝ) := by
    have h := (log_br_670).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20374639/100000000) (δ := 951771/10000000000) 1269 657
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_671 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (671 : ℕ) / 2)) - ((-1893327/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65087691/20000000 : ℚ) : ℝ) ≤ Real.log (671 : ℕ) / 2 := by
    have h := (log_br_671).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (671 : ℕ) / 2 ≤ ((16271923/5000000 : ℚ) : ℝ) := by
    have h := (log_br_671).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44031971/100000000) (δ := 39679/1250000000) 1269 657
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_672 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (672 : ℕ) / 2)) - ((-1813389/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65102583/20000000 : ℚ) : ℝ) ≤ Real.log (672 : ℕ) / 2 := by
    have h := (log_br_672).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (672 : ℕ) / 2 ≤ ((8137823/2500000 : ℚ) : ℝ) := by
    have h := (log_br_672).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33827203/50000000) (δ := 39679/1250000000) 1269 657
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_673 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (673 : ℕ) / 2)) - ((-8736777/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65117453/20000000 : ℚ) : ℝ) ≤ Real.log (673 : ℕ) / 2 := by
    have h := (log_br_673).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (673 : ℕ) / 2 ≤ ((32558727/10000000 : ℚ) : ℝ) := by
    have h := (log_br_673).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -65837689/100000000) (δ := 3967/125000000) 1269 658
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_674 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (674 : ℕ) / 2)) - ((-240627/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((651323/200000 : ℚ) : ℝ) ≤ Real.log (674 : ℕ) / 2 := by
    have h := (log_br_674).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (674 : ℕ) / 2 ≤ ((65132303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_674).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -42285049/100000000) (δ := 47593/500000000) 1269 658
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_675 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (675 : ℕ) / 2)) - ((913967/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32573563/10000000 : ℚ) : ℝ) ≤ Real.log (675 : ℕ) / 2 := by
    have h := (log_br_675).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (675 : ℕ) / 2 ≤ ((65147127/20000000 : ℚ) : ℝ) := by
    have h := (log_br_675).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4692223/25000000) (δ := 317443/10000000000) 1269 658
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_676 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (676 : ℕ) / 2)) - ((1964551/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6516193/2000000 : ℚ) : ℝ) ≤ Real.log (676 : ℕ) / 2 := by
    have h := (log_br_676).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (676 : ℕ) / 2 ≤ ((65161931/20000000 : ℚ) : ℝ) := by
    have h := (log_br_676).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4713953/100000000) (δ := 317443/10000000000) 1269 658
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_677 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (677 : ℕ) / 2)) - ((4298443/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8147089/2500000 : ℚ) : ℝ) ≤ Real.log (677 : ℕ) / 2 := by
    have h := (log_br_677).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (677 : ℕ) / 2 ≤ ((65176713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_677).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 281619/1000000) (δ := 15863/500000000) 1269 658
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_678 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (678 : ℕ) / 2)) - ((-2362837/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4074467/1250000 : ℚ) : ℝ) ≤ Real.log (678 : ℕ) / 2 := by
    have h := (log_br_678).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (678 : ℕ) / 2 ≤ ((65191473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_678).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1031499/2000000) (δ := 15863/500000000) 1269 658
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_679 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (679 : ℕ) / 2)) - ((-9897351/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65206211/20000000 : ℚ) : ℝ) ≤ Real.log (679 : ℕ) / 2 := by
    have h := (log_br_679).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (679 : ℕ) / 2 ≤ ((16301553/5000000 : ℚ) : ℝ) := by
    have h := (log_br_679).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 74954689/100000000) (δ := 317343/10000000000) 1269 658
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_680 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (680 : ℕ) / 2)) - ((-7036143/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65220927/20000000 : ℚ) : ℝ) ≤ Real.log (680 : ℕ) / 2 := by
    have h := (log_br_680).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (680 : ℕ) / 2 ≤ ((1019077/312500 : ℚ) : ℝ) := by
    have h := (log_br_680).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -58781689/100000000) (δ := 39661/1250000000) 1269 659
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_681 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (681 : ℕ) / 2)) - ((302811/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32617811/10000000 : ℚ) : ℝ) ≤ Real.log (681 : ℕ) / 2 := by
    have h := (log_br_681).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (681 : ℕ) / 2 ≤ ((104377/32000 : ℚ) : ℝ) := by
    have h := (log_br_681).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35470159/100000000) (δ := 237947/2500000000) 1269 659
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_682 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (682 : ℕ) / 2)) - ((220841/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8156287/2500000 : ℚ) : ℝ) ≤ Real.log (682 : ℕ) / 2 := by
    have h := (log_br_682).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (682 : ℕ) / 2 ≤ ((65250297/20000000 : ℚ) : ℝ) := by
    have h := (log_br_682).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12195113/100000000) (δ := 79347/2500000000) 1269 659
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_683 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (683 : ℕ) / 2)) - ((4519779/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16316237/5000000 : ℚ) : ℝ) ≤ Real.log (683 : ℕ) / 2 := by
    have h := (log_br_683).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (683 : ℕ) / 2 ≤ ((65264949/20000000 : ℚ) : ℝ) := by
    have h := (log_br_683).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5523311/50000000) (δ := 79347/2500000000) 1269 659
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_684 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (684 : ℕ) / 2)) - ((1992519/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65279579/20000000 : ℚ) : ℝ) ≤ Real.log (684 : ℕ) / 2 := by
    have h := (log_br_684).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (684 : ℕ) / 2 ≤ ((3263979/1000000 : ℚ) : ℝ) := by
    have h := (log_br_684).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17127523/50000000) (δ := 39661/1250000000) 1269 659
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_685 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (685 : ℕ) / 2)) - ((-6641427/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16323547/5000000 : ℚ) : ℝ) ≤ Real.log (685 : ℕ) / 2 := by
    have h := (log_br_685).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (685 : ℕ) / 2 ≤ ((65294189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_685).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14357143/25000000) (δ := 79347/2500000000) 1269 659
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_686 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (686 : ℕ) / 2)) - ((-2491771/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8163597/2500000 : ℚ) : ℝ) ≤ Real.log (686 : ℕ) / 2 := by
    have h := (log_br_686).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (686 : ℕ) / 2 ≤ ((65308777/20000000 : ℚ) : ℝ) := by
    have h := (log_br_686).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15302169/20000000) (δ := 317387/10000000000) 1269 660
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_687 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (687 : ℕ) / 2)) - ((-1071549/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32661671/10000000 : ℚ) : ℝ) ≤ Real.log (687 : ℕ) / 2 := by
    have h := (log_br_687).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (687 : ℕ) / 2 ≤ ((65323343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_687).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6675691/12500000) (δ := 79329/2500000000) 1269 660
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_688 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (688 : ℕ) / 2)) - ((3499511/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2041809/625000 : ℚ) : ℝ) ≤ Real.log (688 : ℕ) / 2 := by
    have h := (log_br_688).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (688 : ℕ) / 2 ≤ ((65337889/20000000 : ℚ) : ℝ) := by
    have h := (log_br_688).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6066387/20000000) (δ := 317387/10000000000) 1269 660
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_689 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (689 : ℕ) / 2)) - ((9577479/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16338103/5000000 : ℚ) : ℝ) ≤ Real.log (689 : ℕ) / 2 := by
    have h := (log_br_689).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (689 : ℕ) / 2 ≤ ((65352413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_689).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -182331/2500000) (δ := 317387/10000000000) 1269 660
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_690 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (690 : ℕ) / 2)) - ((8089187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13073383/4000000 : ℚ) : ℝ) ≤ Real.log (690 : ℕ) / 2 := by
    have h := (log_br_690).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (690 : ℕ) / 2 ≤ ((16341729/5000000 : ℚ) : ℝ) := by
    have h := (log_br_690).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15712143/100000000) (δ := 39677/1250000000) 1269 660
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_691 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (691 : ℕ) / 2)) - ((233621/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32690699/10000000 : ℚ) : ℝ) ≤ Real.log (691 : ℕ) / 2 := by
    have h := (log_br_691).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (691 : ℕ) / 2 ≤ ((65381399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_691).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19342901/50000000) (δ := 79329/2500000000) 1269 660
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_692 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (692 : ℕ) / 2)) - ((-3898499/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65395859/20000000 : ℚ) : ℝ) ≤ Real.log (692 : ℕ) / 2 := by
    have h := (log_br_692).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (692 : ℕ) / 2 ≤ ((3269793/1000000 : ℚ) : ℝ) := by
    have h := (log_br_692).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61624563/100000000) (δ := 39677/1250000000) 1269 660
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_693 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (693 : ℕ) / 2)) - ((-9714311/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32705149/10000000 : ℚ) : ℝ) ≤ Real.log (693 : ℕ) / 2 := by
    have h := (log_br_693).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (693 : ℕ) / 2 ≤ ((65410301/20000000 : ℚ) : ℝ) := by
    have h := (log_br_693).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -72549619/100000000) (δ := 951859/10000000000) 1269 661
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_694 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (694 : ℕ) / 2)) - ((-2021619/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65424719/20000000 : ℚ) : ℝ) ≤ Real.log (694 : ℕ) / 2 := by
    have h := (log_br_694).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (694 : ℕ) / 2 ≤ ((817809/250000 : ℚ) : ℝ) := by
    have h := (log_br_694).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24837947/50000000) (δ := 317359/10000000000) 1269 661
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_695 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (695 : ℕ) / 2)) - ((4771221/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32719559/10000000 : ℚ) : ℝ) ≤ Real.log (695 : ℕ) / 2 := by
    have h := (log_br_695).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (695 : ℕ) / 2 ≤ ((65439119/20000000 : ℚ) : ℝ) := by
    have h := (log_br_695).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26835481/100000000) (δ := 79361/2500000000) 1269 661
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_696 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (696 : ℕ) / 2)) - ((4935229/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8181687/2500000 : ℚ) : ℝ) ≤ Real.log (696 : ℕ) / 2 := by
    have h := (log_br_696).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (696 : ℕ) / 2 ≤ ((65453497/20000000 : ℚ) : ℝ) := by
    have h := (log_br_696).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2014189/50000000) (δ := 317259/10000000000) 1269 661
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_697 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (697 : ℕ) / 2)) - ((7317707/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32733927/10000000 : ℚ) : ℝ) ≤ Real.log (697 : ℕ) / 2 := by
    have h := (log_br_697).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (697 : ℕ) / 2 ≤ ((13093571/4000000 : ℚ) : ℝ) := by
    have h := (log_br_697).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18746999/100000000) (δ := 79361/2500000000) 1269 661
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_698 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (698 : ℕ) / 2)) - ((-443249/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6548219/2000000 : ℚ) : ℝ) ≤ Real.log (698 : ℕ) / 2 := by
    have h := (log_br_698).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (698 : ℕ) / 2 ≤ ((65482193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_698).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20744533/50000000) (δ := 951859/10000000000) 1269 661
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_699 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (699 : ℕ) / 2)) - ((-1679819/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65496507/20000000 : ℚ) : ℝ) ≤ Real.log (699 : ℕ) / 2 := by
    have h := (log_br_699).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (699 : ℕ) / 2 ≤ ((16374127/5000000 : ℚ) : ℝ) := by
    have h := (log_br_699).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64197821/100000000) (δ := 317359/10000000000) 1269 661
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_700 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (700 : ℕ) / 2)) - ((-9449347/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65510803/20000000 : ℚ) : ℝ) ≤ Real.log (700 : ℕ) / 2 := by
    have h := (log_br_700).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (700 : ℕ) / 2 ≤ ((16377701/5000000 : ℚ) : ℝ) := by
    have h := (log_br_700).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35102391/50000000) (δ := 317273/10000000000) 1269 662
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_701 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (701 : ℕ) / 2)) - ((-407/1250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32762539/10000000 : ℚ) : ℝ) ≤ Real.log (701 : ℕ) / 2 := by
    have h := (log_br_701).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (701 : ℕ) / 2 ≤ ((65525079/20000000 : ℚ) : ℝ) := by
    have h := (log_br_701).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -47561063/100000000) (δ := 31733/1000000000) 1269 662
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_702 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (702 : ℕ) / 2)) - ((338793/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65539333/20000000 : ℚ) : ℝ) ≤ Real.log (702 : ℕ) / 2 := by
    have h := (log_br_702).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (702 : ℕ) / 2 ≤ ((8192417/2500000 : ℚ) : ℝ) := by
    have h := (log_br_702).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24947483/100000000) (δ := 95183/1000000000) 1269 662
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_703 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (703 : ℕ) / 2)) - ((1244393/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2048549/625000 : ℚ) : ℝ) ≤ Real.log (703 : ℕ) / 2 := by
    have h := (log_br_703).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (703 : ℕ) / 2 ≤ ((65553569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_703).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2368801/100000000) (δ := 317373/10000000000) 1269 662
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_704 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (704 : ℕ) / 2)) - ((432207/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65567783/20000000 : ℚ) : ℝ) ≤ Real.log (704 : ℕ) / 2 := by
    have h := (log_br_704).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (704 : ℕ) / 2 ≤ ((8195973/2500000 : ℚ) : ℝ) := by
    have h := (log_br_704).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20179743/100000000) (δ := 317273/10000000000) 1269 662
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_705 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (705 : ℕ) / 2)) - ((-683187/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65581977/20000000 : ℚ) : ℝ) ≤ Real.log (705 : ℕ) / 2 := by
    have h := (log_br_705).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (705 : ℕ) / 2 ≤ ((3279099/1000000 : ℚ) : ℝ) := by
    have h := (log_br_705).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21348281/50000000) (δ := 95183/1000000000) 1269 662
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_706 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (706 : ℕ) / 2)) - ((-1721159/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8199519/2500000 : ℚ) : ℝ) ≤ Real.log (706 : ℕ) / 2 := by
    have h := (log_br_706).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (706 : ℕ) / 2 ≤ ((65596153/20000000 : ℚ) : ℝ) := by
    have h := (log_br_706).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 65180069/100000000) (δ := 317373/10000000000) 1269 662
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_707 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (707 : ℕ) / 2)) - ((-584121/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32805153/10000000 : ℚ) : ℝ) ≤ Real.log (707 : ℕ) / 2 := by
    have h := (log_br_707).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (707 : ℕ) / 2 ≤ ((65610307/20000000 : ℚ) : ℝ) := by
    have h := (log_br_707).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -69447781/100000000) (δ := 317301/10000000000) 1269 663
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_708 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (708 : ℕ) / 2)) - ((-3053563/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1640611/500000 : ℚ) : ℝ) ≤ Real.log (708 : ℕ) / 2 := by
    have h := (log_br_708).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (708 : ℕ) / 2 ≤ ((65624441/20000000 : ℚ) : ℝ) := by
    have h := (log_br_708).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -47027723/100000000) (δ := 158701/5000000000) 1269 663
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_709 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (709 : ℕ) / 2)) - ((2762181/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13127711/4000000 : ℚ) : ℝ) ≤ Real.log (709 : ℕ) / 2 := by
    have h := (log_br_709).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (709 : ℕ) / 2 ≤ ((16409639/5000000 : ℚ) : ℝ) := by
    have h := (log_br_709).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4927561/20000000) (δ := 317401/10000000000) 1269 663
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_710 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (710 : ℕ) / 2)) - ((4979199/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65652649/20000000 : ℚ) : ℝ) ≤ Real.log (710 : ℕ) / 2 := by
    have h := (log_br_710).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (710 : ℕ) / 2 ≤ ((1313053/400000 : ℚ) : ℝ) := by
    have h := (log_br_710).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2281197/100000000) (δ := 158651/5000000000) 1269 663
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_711 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (711 : ℕ) / 2)) - ((1390813/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16416681/5000000 : ℚ) : ℝ) ≤ Real.log (711 : ℕ) / 2 := by
    have h := (log_br_711).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (711 : ℕ) / 2 ≤ ((2626669/800000 : ℚ) : ℝ) := by
    have h := (log_br_711).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2505659/12500000) (δ := 158701/5000000000) 1269 663
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_712 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (712 : ℕ) / 2)) - ((-612479/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65680779/20000000 : ℚ) : ℝ) ≤ Real.log (712 : ℕ) / 2 := by
    have h := (log_br_712).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (712 : ℕ) / 2 ≤ ((3284039/1000000 : ℚ) : ℝ) := by
    have h := (log_br_712).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8468003/20000000) (δ := 317401/10000000000) 1269 663
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_713 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (713 : ℕ) / 2)) - ((-2121489/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32847407/10000000 : ℚ) : ℝ) ≤ Real.log (713 : ℕ) / 2 := by
    have h := (log_br_713).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (713 : ℕ) / 2 ≤ ((13138963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_713).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32301517/50000000) (δ := 317301/10000000000) 1269 663
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_714 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (714 : ℕ) / 2)) - ((-9454639/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65708829/20000000 : ℚ) : ℝ) ≤ Real.log (714 : ℕ) / 2 := by
    have h := (log_br_714).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (714 : ℕ) / 2 ≤ ((6570883/2000000 : ℚ) : ℝ) := by
    have h := (log_br_714).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14049061/20000000) (δ := 317329/10000000000) 1269 664
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_715 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (715 : ℕ) / 2)) - ((-687617/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2628913/800000 : ℚ) : ℝ) ≤ Real.log (715 : ℕ) / 2 := by
    have h := (log_br_715).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (715 : ℕ) / 2 ≤ ((32861413/10000000 : ℚ) : ℝ) := by
    have h := (log_br_715).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -960883/2000000) (δ := 317329/10000000000) 1269 664
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_716 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (716 : ℕ) / 2)) - ((1276339/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65736801/20000000 : ℚ) : ℝ) ≤ Real.log (716 : ℕ) / 2 := by
    have h := (log_br_716).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (716 : ℕ) / 2 ≤ ((32868401/10000000 : ℚ) : ℝ) := by
    have h := (log_br_716).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -161717/625000) (δ := 317329/10000000000) 1269 664
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_717 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (717 : ℕ) / 2)) - ((494429/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32875379/10000000 : ℚ) : ℝ) ≤ Real.log (717 : ℕ) / 2 := by
    have h := (log_br_717).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (717 : ℕ) / 2 ≤ ((65750759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_717).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3735429/100000000) (δ := 317429/10000000000) 1269 664
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_718 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (718 : ℕ) / 2)) - ((296763/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13152939/4000000 : ℚ) : ℝ) ≤ Real.log (718 : ℕ) / 2 := by
    have h := (log_br_718).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (718 : ℕ) / 2 ≤ ((8220587/2500000 : ℚ) : ℝ) := by
    have h := (log_br_718).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9186069/50000000) (δ := 158687/5000000000) 1269 664
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_719 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (719 : ℕ) / 2)) - ((-58961/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65778613/20000000 : ℚ) : ℝ) ≤ Real.log (719 : ℕ) / 2 := by
    have h := (log_br_719).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (719 : ℕ) / 2 ≤ ((32889307/10000000 : ℚ) : ℝ) := by
    have h := (log_br_719).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8089913/20000000) (δ := 317329/10000000000) 1269 664
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_720 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (720 : ℕ) / 2)) - ((-8010683/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((257002/78125 : ℚ) : ℝ) ≤ Real.log (720 : ℕ) / 2 := by
    have h := (log_br_720).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (720 : ℕ) / 2 ≤ ((65792513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_720).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 31248427/50000000) (δ := 158637/5000000000) 1269 664
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_721 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (721 : ℕ) / 2)) - ((-9715979/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65806391/20000000 : ℚ) : ℝ) ≤ Real.log (721 : ℕ) / 2 := by
    have h := (log_br_721).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (721 : ℕ) / 2 ≤ ((8225799/2500000 : ℚ) : ℝ) := by
    have h := (log_br_721).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14513443/20000000) (δ := 317257/10000000000) 1269 665
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_722 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (722 : ℕ) / 2)) - ((-4371931/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65820251/20000000 : ℚ) : ℝ) ≤ Real.log (722 : ℕ) / 2 := by
    have h := (log_br_722).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (722 : ℕ) / 2 ≤ ((16455063/5000000 : ℚ) : ℝ) := by
    have h := (log_br_722).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5058179/10000000) (δ := 317257/10000000000) 1269 665
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_723 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (723 : ℕ) / 2)) - ((4129913/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16458523/5000000 : ℚ) : ℝ) ≤ Real.log (723 : ℕ) / 2 := by
    have h := (log_br_723).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (723 : ℕ) / 2 ≤ ((65834093/20000000 : ℚ) : ℝ) := by
    have h := (log_br_723).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3578313/12500000) (δ := 317357/10000000000) 1269 665
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_724 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (724 : ℕ) / 2)) - ((9642713/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65847913/20000000 : ℚ) : ℝ) ≤ Real.log (724 : ℕ) / 2 := by
    have h := (log_br_724).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (724 : ℕ) / 2 ≤ ((32923957/10000000 : ℚ) : ℝ) := by
    have h := (log_br_724).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3351471/50000000) (δ := 158723/5000000000) 1269 665
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_725 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (725 : ℕ) / 2)) - ((4104867/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16465429/5000000 : ℚ) : ℝ) ≤ Real.log (725 : ℕ) / 2 := by
    have h := (log_br_725).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (725 : ℕ) / 2 ≤ ((65861717/20000000 : ℚ) : ℝ) := by
    have h := (log_br_725).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7596033/50000000) (δ := 317357/10000000000) 1269 665
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_726 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (726 : ℕ) / 2)) - ((884033/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((131751/40000 : ℚ) : ℝ) ≤ Real.log (726 : ℕ) / 2 := by
    have h := (log_br_726).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (726 : ℕ) / 2 ≤ ((65875501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_726).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4632117/12500000) (δ := 317357/10000000000) 1269 665
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_727 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (727 : ℕ) / 2)) - ((-3533443/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4118079/1250000 : ℚ) : ℝ) ≤ Real.log (727 : ℕ) / 2 := by
    have h := (log_br_727).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (727 : ℕ) / 2 ≤ ((13177853/4000000 : ℚ) : ℝ) := by
    have h := (log_br_727).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58890081/100000000) (δ := 317357/10000000000) 1269 665
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_728 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (728 : ℕ) / 2)) - ((-2490719/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6590301/2000000 : ℚ) : ℝ) ≤ Real.log (728 : ℕ) / 2 := by
    have h := (log_br_728).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (728 : ℕ) / 2 ≤ ((65903011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_728).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -76384959/100000000) (δ := 63457/2000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_729 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (729 : ℕ) / 2)) - ((-287917/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((65916737/20000000 : ℚ) : ℝ) ≤ Real.log (729 : ℕ) / 2 := by
    have h := (log_br_729).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (729 : ℕ) / 2 ≤ ((32958369/10000000 : ℚ) : ℝ) := by
    have h := (log_br_729).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10922101/20000000) (δ := 158659/5000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_730 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (730 : ℕ) / 2)) - ((39587/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13186089/4000000 : ℚ) : ℝ) ≤ Real.log (730 : ℕ) / 2 := by
    have h := (log_br_730).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (730 : ℕ) / 2 ≤ ((32965223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_730).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3286619/10000000) (δ := 158659/5000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_731 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (731 : ℕ) / 2)) - ((180429/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((32972067/10000000 : ℚ) : ℝ) ≤ Real.log (731 : ℕ) / 2 := by
    have h := (log_br_731).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (731 : ℕ) / 2 ≤ ((13188827/4000000 : ℚ) : ℝ) := by
    have h := (log_br_731).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5576007/50000000) (δ := 63457/2000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_732 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (732 : ℕ) / 2)) - ((9125399/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13191561/4000000 : ℚ) : ℝ) ≤ Real.log (732 : ℕ) / 2 := by
    have h := (log_br_732).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (732 : ℕ) / 2 ≤ ((32978903/10000000 : ℚ) : ℝ) := by
    have h := (log_br_732).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1053361/10000000) (δ := 158659/5000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_733 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (733 : ℕ) / 2)) - ((174663/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((257701/78125 : ℚ) : ℝ) ≤ Real.log (733 : ℕ) / 2 := by
    have h := (log_br_733).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (733 : ℕ) / 2 ≤ ((65971459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_733).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6437819/20000000) (δ := 475909/5000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_734 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (734 : ℕ) / 2)) - ((-5495131/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6598509/2000000 : ℚ) : ℝ) ≤ Real.log (734 : ℕ) / 2 := by
    have h := (log_br_734).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (734 : ℕ) / 2 ≤ ((65985091/20000000 : ℚ) : ℝ) := by
    have h := (log_br_734).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 53814441/100000000) (δ := 63457/2000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_735 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (735 : ℕ) / 2)) - ((-9921719/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4124919/1250000 : ℚ) : ℝ) ≤ Real.log (735 : ℕ) / 2 := by
    have h := (log_br_735).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (735 : ℕ) / 2 ≤ ((13199741/4000000 : ℚ) : ℝ) := by
    have h := (log_br_735).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75409649/100000000) (δ := 158709/5000000000) 1269 666
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_736 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (736 : ℕ) / 2)) - ((-1480273/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66012301/20000000 : ℚ) : ℝ) ≤ Real.log (736 : ℕ) / 2 := by
    have h := (log_br_736).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (736 : ℕ) / 2 ≤ ((33006151/10000000 : ℚ) : ℝ) := by
    have h := (log_br_736).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -60101743/100000000) (δ := 158657/5000000000) 1269 667
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_737 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (737 : ℕ) / 2)) - ((56367/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33012939/10000000 : ℚ) : ℝ) ≤ Real.log (737 : ℕ) / 2 := by
    have h := (log_br_737).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (737 : ℕ) / 2 ≤ ((66025879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_737).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38565227/100000000) (δ := 158707/5000000000) 1269 667
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_738 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (738 : ℕ) / 2)) - ((970213/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33019719/10000000 : ℚ) : ℝ) ≤ Real.log (738 : ℕ) / 2 := by
    have h := (log_br_738).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (738 : ℕ) / 2 ≤ ((66039439/20000000 : ℚ) : ℝ) := by
    have h := (log_br_738).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17055677/100000000) (δ := 158707/5000000000) 1269 667
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_739 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (739 : ℕ) / 2)) - ((9843853/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66052979/20000000 : ℚ) : ℝ) ≤ Real.log (739 : ℕ) / 2 := by
    have h := (log_br_739).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (739 : ℕ) / 2 ≤ ((3302649/1000000 : ℚ) : ℝ) := by
    have h := (log_br_739).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 884747/20000000) (δ := 317389/10000000000) 1269 667
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_740 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (740 : ℕ) / 2)) - ((1021189/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66066501/20000000 : ℚ) : ℝ) ≤ Real.log (740 : ℕ) / 2 := by
    have h := (log_br_740).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (740 : ℕ) / 2 ≤ ((33033251/10000000 : ℚ) : ℝ) := by
    have h := (log_br_740).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25873007/100000000) (δ := 158657/5000000000) 1269 667
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_741 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (741 : ℕ) / 2)) - ((-315531/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33040003/10000000 : ℚ) : ℝ) ≤ Real.log (741 : ℕ) / 2 := by
    have h := (log_br_741).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (741 : ℕ) / 2 ≤ ((66080007/20000000 : ℚ) : ℝ) := by
    have h := (log_br_741).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 47295313/100000000) (δ := 158707/5000000000) 1269 667
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_742 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (742 : ℕ) / 2)) - ((-184669/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16523373/5000000 : ℚ) : ℝ) ≤ Real.log (742 : ℕ) / 2 := by
    have h := (log_br_742).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (742 : ℕ) / 2 ≤ ((66093493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_742).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 68687481/100000000) (δ := 317289/10000000000) 1269 667
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_743 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (743 : ℕ) / 2)) - ((-8958521/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((826337/250000 : ℚ) : ℝ) ≤ Real.log (743 : ℕ) / 2 := by
    have h := (log_br_743).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (743 : ℕ) / 2 ≤ ((66106961/20000000 : ℚ) : ℝ) := by
    have h := (log_br_743).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67028537/100000000) (δ := 158671/5000000000) 1269 668
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_744 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (744 : ℕ) / 2)) - ((-2541247/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6612041/2000000 : ℚ) : ℝ) ≤ Real.log (744 : ℕ) / 2 := by
    have h := (log_br_744).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (744 : ℕ) / 2 ≤ ((66120411/20000000 : ℚ) : ℝ) := by
    have h := (log_br_744).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22846737/50000000) (δ := 317361/10000000000) 1269 668
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_745 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (745 : ℕ) / 2)) - ((5607719/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33066921/10000000 : ℚ) : ℝ) ≤ Real.log (745 : ℕ) / 2 := by
    have h := (log_br_745).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (745 : ℕ) / 2 ≤ ((66133843/20000000 : ℚ) : ℝ) := by
    have h := (log_br_745).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6096741/25000000) (δ := 317361/10000000000) 1269 668
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_746 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (746 : ℕ) / 2)) - ((2480693/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13229451/4000000 : ℚ) : ℝ) ≤ Real.log (746 : ℕ) / 2 := by
    have h := (log_br_746).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (746 : ℕ) / 2 ≤ ((33073629/10000000 : ℚ) : ℝ) := by
    have h := (log_br_746).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3109007/100000000) (δ := 475921/5000000000) 1269 668
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_747 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (747 : ℕ) / 2)) - ((7481329/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66160651/20000000 : ℚ) : ℝ) ≤ Real.log (747 : ℕ) / 2 := by
    have h := (log_br_747).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (747 : ℕ) / 2 ≤ ((16540163/5000000 : ℚ) : ℝ) := by
    have h := (log_br_747).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4534703/25000000) (δ := 317261/10000000000) 1269 668
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_748 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (748 : ℕ) / 2)) - ((-17951/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66174029/20000000 : ℚ) : ℝ) ≤ Real.log (748 : ℕ) / 2 := by
    have h := (log_br_748).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (748 : ℕ) / 2 ≤ ((6617403/2000000 : ℚ) : ℝ) := by
    have h := (log_br_748).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2459979/6250000) (δ := 158721/5000000000) 1269 668
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_749 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (749 : ℕ) / 2)) - ((-376063/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66187389/20000000 : ℚ) : ℝ) ≤ Real.log (749 : ℕ) / 2 := by
    have h := (log_br_749).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (749 : ℕ) / 2 ≤ ((6618739/2000000 : ℚ) : ℝ) := by
    have h := (log_br_749).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15137991/25000000) (δ := 158721/5000000000) 1269 668
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_750 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (750 : ℕ) / 2)) - ((-4959669/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16550183/5000000 : ℚ) : ℝ) ≤ Real.log (750 : ℕ) / 2 := by
    have h := (log_br_750).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (750 : ℕ) / 2 ≤ ((66200733/20000000 : ℚ) : ℝ) := by
    have h := (log_br_750).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37681167/50000000) (δ := 317433/10000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_751 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (751 : ℕ) / 2)) - ((-5632297/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8276757/2500000 : ℚ) : ℝ) ≤ Real.log (751 : ℕ) / 2 := by
    have h := (log_br_751).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (751 : ℕ) / 2 ≤ ((66214057/20000000 : ℚ) : ℝ) := by
    have h := (log_br_751).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -54227139/100000000) (δ := 317433/10000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_752 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (752 : ℕ) / 2)) - ((48713/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66227363/20000000 : ℚ) : ℝ) ≤ Real.log (752 : ℕ) / 2 := by
    have h := (log_br_752).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (752 : ℕ) / 2 ≤ ((16556841/5000000 : ℚ) : ℝ) := by
    have h := (log_br_752).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33118911/100000000) (δ := 31737/1000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_753 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (753 : ℕ) / 2)) - ((8862691/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16560163/5000000 : ℚ) : ℝ) ≤ Real.log (753 : ℕ) / 2 := by
    have h := (log_br_753).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (753 : ℕ) / 2 ≤ ((66240653/20000000 : ℚ) : ℝ) := by
    have h := (log_br_753).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6019617/50000000) (δ := 317433/10000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_754 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (754 : ℕ) / 2)) - ((2339323/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66253923/20000000 : ℚ) : ℝ) ≤ Real.log (754 : ℕ) / 2 := by
    have h := (log_br_754).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (754 : ℕ) / 2 ≤ ((16563481/5000000 : ℚ) : ℝ) := by
    have h := (log_br_754).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9011889/100000000) (δ := 31737/1000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_755 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (755 : ℕ) / 2)) - ((722027/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66267177/20000000 : ℚ) : ℝ) ≤ Real.log (755 : ℕ) / 2 := by
    have h := (log_br_755).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (755 : ℕ) / 2 ≤ ((33133589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_755).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30036047/100000000) (δ := 317333/10000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_756 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (756 : ℕ) / 2)) - ((-4533051/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66280413/20000000 : ℚ) : ℝ) ≤ Real.log (756 : ℕ) / 2 := by
    have h := (log_br_756).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (756 : ℕ) / 2 ≤ ((33140207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_756).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12757913/25000000) (δ := 317333/10000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_757 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (757 : ℕ) / 2)) - ((-9659823/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((517919/156250 : ℚ) : ℝ) ≤ Real.log (757 : ℕ) / 2 := by
    have h := (log_br_757).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (757 : ℕ) / 2 ≤ ((66293633/20000000 : ℚ) : ℝ) := by
    have h := (log_br_757).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 72000291/100000000) (δ := 317433/10000000000) 1269 669
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_758 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (758 : ℕ) / 2)) - ((-4193179/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66306833/20000000 : ℚ) : ℝ) ≤ Real.log (758 : ℕ) / 2 := by
    have h := (log_br_758).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (758 : ℕ) / 2 ≤ ((33153417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_758).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8017407/12500000) (δ := 158649/5000000000) 1269 670
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_759 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (759 : ℕ) / 2)) - ((-787947/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66320017/20000000 : ℚ) : ℝ) ≤ Real.log (759 : ℕ) / 2 := by
    have h := (log_br_759).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (759 : ℕ) / 2 ≤ ((33160009/10000000 : ℚ) : ℝ) := by
    have h := (log_br_759).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5403267/12500000) (δ := 158649/5000000000) 1269 670
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_760 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (760 : ℕ) / 2)) - ((6266111/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((259114/78125 : ℚ) : ℝ) ≤ Real.log (760 : ℕ) / 2 := by
    have h := (log_br_760).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (760 : ℕ) / 2 ≤ ((13266637/4000000 : ℚ) : ℝ) := by
    have h := (log_br_760).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11169991/50000000) (δ := 63461/2000000000) 1269 670
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_761 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (761 : ℕ) / 2)) - ((4991213/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66346333/20000000 : ℚ) : ℝ) ≤ Real.log (761 : ℕ) / 2 := by
    have h := (log_br_761).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (761 : ℕ) / 2 ≤ ((33173167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_761).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1482381/100000000) (δ := 158649/5000000000) 1269 670
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_762 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (762 : ℕ) / 2)) - ((1787923/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13271893/4000000 : ℚ) : ℝ) ≤ Real.log (762 : ℕ) / 2 := by
    have h := (log_br_762).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (762 : ℕ) / 2 ≤ ((33179733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_762).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9674127/50000000) (δ := 158649/5000000000) 1269 670
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_763 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (763 : ℕ) / 2)) - ((-352733/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3318629/1000000 : ℚ) : ℝ) ≤ Real.log (763 : ℕ) / 2 := by
    have h := (log_br_763).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (763 : ℕ) / 2 ≤ ((66372581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_763).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40151923/100000000) (δ := 63461/2000000000) 1269 670
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_764 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (764 : ℕ) / 2)) - ((-7619283/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66385677/20000000 : ℚ) : ℝ) ≤ Real.log (764 : ℕ) / 2 := by
    have h := (log_br_764).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (764 : ℕ) / 2 ≤ ((33192839/10000000 : ℚ) : ℝ) := by
    have h := (log_br_764).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 60927039/100000000) (δ := 158649/5000000000) 1269 670
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_765 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (765 : ℕ) / 2)) - ((-9921379/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33199379/10000000 : ℚ) : ℝ) ≤ Real.log (765 : ℕ) / 2 := by
    have h := (log_br_765).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (765 : ℕ) / 2 ≤ ((66398759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_765).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -75402857/100000000) (δ := 317377/10000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_766 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (766 : ℕ) / 2)) - ((-5781591/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66411821/20000000 : ℚ) : ℝ) ≤ Real.log (766 : ℕ) / 2 := by
    have h := (log_br_766).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (766 : ℕ) / 2 ≤ ((33205911/10000000 : ℚ) : ℝ) := by
    have h := (log_br_766).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -27340837/50000000) (δ := 158713/5000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_767 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (767 : ℕ) / 2)) - ((2097913/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16606217/5000000 : ℚ) : ℝ) ≤ Real.log (767 : ℕ) / 2 := by
    have h := (log_br_767).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (767 : ℕ) / 2 ≤ ((66424869/20000000 : ℚ) : ℝ) := by
    have h := (log_br_767).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3398587/10000000) (δ := 158663/5000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_768 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (768 : ℕ) / 2)) - ((8614163/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66437897/20000000 : ℚ) : ℝ) ≤ Real.log (768 : ℕ) / 2 := by
    have h := (log_br_768).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (768 : ℕ) / 2 ≤ ((33218949/10000000 : ℚ) : ℝ) := by
    have h := (log_br_768).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13318619/100000000) (δ := 158713/5000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_769 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (769 : ℕ) / 2)) - ((4787101/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66450909/20000000 : ℚ) : ℝ) ≤ Real.log (769 : ℕ) / 2 := by
    have h := (log_br_769).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (769 : ℕ) / 2 ≤ ((6645091/2000000 : ℚ) : ℝ) := by
    have h := (log_br_769).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3660833/50000000) (δ := 158713/5000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_770 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (770 : ℕ) / 2)) - ((4379647/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13292781/4000000 : ℚ) : ℝ) ≤ Real.log (770 : ℕ) / 2 := by
    have h := (log_br_770).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (770 : ℕ) / 2 ≤ ((33231953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_770).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27936571/100000000) (δ := 158713/5000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_771 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (771 : ℕ) / 2)) - ((-3617279/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66476883/20000000 : ℚ) : ℝ) ≤ Real.log (771 : ℕ) / 2 := by
    have h := (log_br_771).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (771 : ℕ) / 2 ≤ ((16619221/5000000 : ℚ) : ℝ) := by
    have h := (log_br_771).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12130731/25000000) (δ := 317277/10000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_772 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (772 : ℕ) / 2)) - ((-2323293/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13297969/4000000 : ℚ) : ℝ) ≤ Real.log (772 : ℕ) / 2 := by
    have h := (log_br_772).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (772 : ℕ) / 2 ≤ ((33244923/10000000 : ℚ) : ℝ) := by
    have h := (log_br_772).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8635487/12500000) (δ := 158713/5000000000) 1269 671
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_773 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (773 : ℕ) / 2)) - ((-9034169/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6650279/2000000 : ℚ) : ℝ) ≤ Real.log (773 : ℕ) / 2 := by
    have h := (log_br_773).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (773 : ℕ) / 2 ≤ ((66502791/20000000 : ℚ) : ℝ) := by
    have h := (log_br_773).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6746173/10000000) (δ := 63451/2000000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_774 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (774 : ℕ) / 2)) - ((-756433/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33257859/10000000 : ℚ) : ℝ) ≤ Real.log (774 : ℕ) / 2 := by
    have h := (log_br_774).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (774 : ℕ) / 2 ≤ ((66515719/20000000 : ℚ) : ℝ) := by
    have h := (log_br_774).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4695469/10000000) (δ := 63451/2000000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_775 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (775 : ℕ) / 2)) - ((4898129/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6652863/2000000 : ℚ) : ℝ) ≤ Real.log (775 : ℕ) / 2 := by
    have h := (log_br_775).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (775 : ℕ) / 2 ≤ ((66528631/20000000 : ℚ) : ℝ) := by
    have h := (log_br_775).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2647303/10000000) (δ := 63451/2000000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_776 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (776 : ℕ) / 2)) - ((4855817/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2661661/800000 : ℚ) : ℝ) ≤ Real.log (776 : ℕ) / 2 := by
    have h := (log_br_776).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (776 : ℕ) / 2 ≤ ((33270763/10000000 : ℚ) : ℝ) := by
    have h := (log_br_776).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -188073/3125000) (δ := 79337/2500000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_777 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (777 : ℕ) / 2)) - ((4192217/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66554403/20000000 : ℚ) : ℝ) ≤ Real.log (777 : ℕ) / 2 := by
    have h := (log_br_777).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (777 : ℕ) / 2 ≤ ((16638601/5000000 : ℚ) : ℝ) := by
    have h := (log_br_777).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14409391/100000000) (δ := 63471/2000000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_778 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (778 : ℕ) / 2)) - ((1773831/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13313453/4000000 : ℚ) : ℝ) ≤ Real.log (778 : ℕ) / 2 := by
    have h := (log_br_778).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (778 : ℕ) / 2 ≤ ((33283633/10000000 : ℚ) : ℝ) := by
    have h := (log_br_778).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34811739/100000000) (δ := 79337/2500000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_779 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (779 : ℕ) / 2)) - ((-74317/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6658011/2000000 : ℚ) : ℝ) ≤ Real.log (779 : ℕ) / 2 := by
    have h := (log_br_779).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (779 : ℕ) / 2 ≤ ((66580111/20000000 : ℚ) : ℝ) := by
    have h := (log_br_779).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 689839/1250000) (δ := 63451/2000000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_780 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (780 : ℕ) / 2)) - ((-9927957/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66592939/20000000 : ℚ) : ℝ) ≤ Real.log (780 : ℕ) / 2 := by
    have h := (log_br_780).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (780 : ℕ) / 2 ≤ ((3329647/1000000 : ℚ) : ℝ) := by
    have h := (log_br_780).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75537121/100000000) (δ := 63471/2000000000) 1269 672
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_781 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (781 : ℕ) / 2)) - ((-192363/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66605751/20000000 : ℚ) : ℝ) ≤ Real.log (781 : ℕ) / 2 := by
    have h := (log_br_781).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (781 : ℕ) / 2 ≤ ((8325719/2500000 : ℚ) : ℝ) := by
    have h := (log_br_781).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15304869/25000000) (δ := 15871/500000000) 1269 673
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_782 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (782 : ℕ) / 2)) - ((-165071/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66618547/20000000 : ℚ) : ℝ) ≤ Real.log (782 : ℕ) / 2 := by
    have h := (log_br_782).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (782 : ℕ) / 2 ≤ ((16654637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_782).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -40921821/100000000) (δ := 15871/500000000) 1269 673
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_783 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (783 : ℕ) / 2)) - ((211809/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33315663/10000000 : ℚ) : ℝ) ≤ Real.log (783 : ℕ) / 2 := by
    have h := (log_br_783).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (783 : ℕ) / 2 ≤ ((66631327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_783).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20651133/100000000) (δ := 317383/10000000000) 1269 673
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_784 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (784 : ℕ) / 2)) - ((9998693/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6664409/2000000 : ℚ) : ℝ) ≤ Real.log (784 : ℕ) / 2 := by
    have h := (log_br_784).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (784 : ℕ) / 2 ≤ ((66644091/20000000 : ℚ) : ℝ) := by
    have h := (log_br_784).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -202119/50000000) (δ := 317383/10000000000) 1269 673
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_785 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (785 : ℕ) / 2)) - ((7019763/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66656837/20000000 : ℚ) : ℝ) ≤ Real.log (785 : ℕ) / 2 := by
    have h := (log_br_785).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (785 : ℕ) / 2 ≤ ((33328419/10000000 : ℚ) : ℝ) := by
    have h := (log_br_785).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19815691/100000000) (δ := 317283/10000000000) 1269 673
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_786 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (786 : ℕ) / 2)) - ((-59091/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66669567/20000000 : ℚ) : ℝ) ≤ Real.log (786 : ℕ) / 2 := by
    have h := (log_br_786).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (786 : ℕ) / 2 ≤ ((260428/78125 : ℚ) : ℝ) := by
    have h := (log_br_786).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 20004327/50000000) (δ := 15871/500000000) 1269 673
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_787 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (787 : ℕ) / 2)) - ((-1484359/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33341141/10000000 : ℚ) : ℝ) ≤ Real.log (787 : ℕ) / 2 := by
    have h := (log_br_787).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (787 : ℕ) / 2 ≤ ((66682283/20000000 : ℚ) : ℝ) := by
    have h := (log_br_787).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 30088911/50000000) (δ := 317383/10000000000) 1269 673
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_788 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (788 : ℕ) / 2)) - ((-4987329/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3334749/1000000 : ℚ) : ℝ) ≤ Real.log (788 : ℕ) / 2 := by
    have h := (log_br_788).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (788 : ℕ) / 2 ≤ ((66694981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_788).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9594951/12500000) (δ := 317311/10000000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_789 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (789 : ℕ) / 2)) - ((-1280543/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66707663/20000000 : ℚ) : ℝ) ≤ Real.log (789 : ℕ) / 2 := by
    have h := (log_br_789).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (789 : ℕ) / 2 ≤ ((4169229/1250000 : ℚ) : ℝ) := by
    have h := (log_br_789).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -56641199/100000000) (δ := 79323/2500000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_790 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (790 : ℕ) / 2)) - ((217183/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66720329/20000000 : ℚ) : ℝ) ≤ Real.log (790 : ℕ) / 2 := by
    have h := (log_br_790).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (790 : ℕ) / 2 ≤ ((6672033/2000000 : ℚ) : ℝ) := by
    have h := (log_br_790).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36549757/100000000) (δ := 317411/10000000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_791 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (791 : ℕ) / 2)) - ((98799/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66732979/20000000 : ℚ) : ℝ) ≤ Real.log (791 : ℕ) / 2 := by
    have h := (log_br_791).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (791 : ℕ) / 2 ≤ ((3336649/1000000 : ℚ) : ℝ) := by
    have h := (log_br_791).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8241847/50000000) (δ := 79323/2500000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_792 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (792 : ℕ) / 2)) - ((9898953/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66745613/20000000 : ℚ) : ℝ) ≤ Real.log (792 : ℕ) / 2 := by
    have h := (log_br_792).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (792 : ℕ) / 2 ≤ ((33372807/10000000 : ℚ) : ℝ) := by
    have h := (log_br_792).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 889247/25000000) (δ := 317411/10000000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_793 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (793 : ℕ) / 2)) - ((5873991/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8344779/2500000 : ℚ) : ℝ) ≤ Real.log (793 : ℕ) / 2 := by
    have h := (log_br_793).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (793 : ℕ) / 2 ≤ ((66758233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_793).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23573877/100000000) (δ := 317311/10000000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_794 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (794 : ℕ) / 2)) - ((-13673/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33385417/10000000 : ℚ) : ℝ) ≤ Real.log (794 : ℕ) / 2 := by
    have h := (log_br_794).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (794 : ℕ) / 2 ≤ ((13354167/4000000 : ℚ) : ℝ) := by
    have h := (log_br_794).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 217819/500000) (δ := 19837/625000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_795 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (795 : ℕ) / 2)) - ((-4125561/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66783421/20000000 : ℚ) : ℝ) ≤ Real.log (795 : ℕ) / 2 := by
    have h := (log_br_795).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (795 : ℕ) / 2 ≤ ((33391711/10000000 : ℚ) : ℝ) := by
    have h := (log_br_795).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7941241/12500000) (δ := 317411/10000000000) 1269 674
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_796 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (796 : ℕ) / 2)) - ((-9806247/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66795991/20000000 : ℚ) : ℝ) ≤ Real.log (796 : ℕ) / 2 := by
    have h := (log_br_796).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (796 : ℕ) / 2 ≤ ((8349499/2500000 : ℚ) : ℝ) := by
    have h := (log_br_796).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36805271/50000000) (δ := 317339/10000000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_797 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (797 : ℕ) / 2)) - ((-545521/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33404273/10000000 : ℚ) : ℝ) ≤ Real.log (797 : ℕ) / 2 := by
    have h := (log_br_797).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (797 : ℕ) / 2 ≤ ((66808547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_797).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -53695173/100000000) (δ := 19829/625000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_798 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (798 : ℕ) / 2)) - ((542131/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13364217/4000000 : ℚ) : ℝ) ≤ Real.log (798 : ℕ) / 2 := by
    have h := (log_br_798).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (798 : ℕ) / 2 ≤ ((33410543/10000000 : ℚ) : ℝ) := by
    have h := (log_br_798).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -264103/781250) (δ := 79341/2500000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_799 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (799 : ℕ) / 2)) - ((8485489/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66833609/20000000 : ℚ) : ℝ) ≤ Real.log (799 : ℕ) / 2 := by
    have h := (log_br_799).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (799 : ℕ) / 2 ≤ ((6683361/2000000 : ℚ) : ℝ) := by
    have h := (log_br_799).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13938989/100000000) (δ := 79341/2500000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_800 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (800 : ℕ) / 2)) - ((9722639/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66846117/20000000 : ℚ) : ℝ) ≤ Real.log (800 : ℕ) / 2 := by
    have h := (log_br_800).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (800 : ℕ) / 2 ≤ ((33423059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_800).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2950913/50000000) (δ := 79341/2500000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_801 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (801 : ℕ) / 2)) - ((5159411/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66858609/20000000 : ℚ) : ℝ) ≤ Real.log (801 : ℕ) / 2 := by
    have h := (log_br_801).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (801 : ℕ) / 2 ≤ ((6685861/2000000 : ℚ) : ℝ) := by
    have h := (log_br_801).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25717261/100000000) (δ := 79341/2500000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_802 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (802 : ℕ) / 2)) - ((-1234887/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33435543/10000000 : ℚ) : ℝ) ≤ Real.log (802 : ℕ) / 2 := by
    have h := (log_br_802).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (802 : ℕ) / 2 ≤ ((66871087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_802).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22754451/50000000) (δ := 19829/625000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_803 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (803 : ℕ) / 2)) - ((-4312553/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66883547/20000000 : ℚ) : ℝ) ≤ Real.log (803 : ℕ) / 2 := by
    have h := (log_br_803).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (803 : ℕ) / 2 ≤ ((16720887/5000000 : ℚ) : ℝ) := by
    have h := (log_br_803).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 65275163/100000000) (δ := 317339/10000000000) 1269 675
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_804 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (804 : ℕ) / 2)) - ((-483317/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8361999/2500000 : ℚ) : ℝ) ≤ Real.log (804 : ℕ) / 2 := by
    have h := (log_br_804).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (804 : ℕ) / 2 ≤ ((66895993/20000000 : ℚ) : ℝ) := by
    have h := (log_br_804).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -18015897/25000000) (δ := 39667/1250000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_805 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (805 : ℕ) / 2)) - ((-2497683/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33454211/10000000 : ℚ) : ℝ) ≤ Real.log (805 : ℕ) / 2 := by
    have h := (log_br_805).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (805 : ℕ) / 2 ≤ ((66908423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_805).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -52346501/100000000) (δ := 317367/10000000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_806 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (806 : ℕ) / 2)) - ((2615889/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66920837/20000000 : ℚ) : ℝ) ≤ Real.log (806 : ℕ) / 2 := by
    have h := (log_br_806).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (806 : ℕ) / 2 ≤ ((33460419/10000000 : ℚ) : ℝ) := by
    have h := (log_br_806).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -32653207/100000000) (δ := 317267/10000000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_807 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (807 : ℕ) / 2)) - ((8681113/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16733309/5000000 : ℚ) : ℝ) ≤ Real.log (807 : ℕ) / 2 := by
    have h := (log_br_807).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (807 : ℕ) / 2 ≤ ((66933237/20000000 : ℚ) : ℝ) := by
    have h := (log_br_807).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -12985293/100000000) (δ := 39667/1250000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_808 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (808 : ℕ) / 2)) - ((2411843/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3347281/1000000 : ℚ) : ℝ) ≤ Real.log (808 : ℕ) / 2 := by
    have h := (log_br_808).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (808 : ℕ) / 2 ≤ ((66945621/20000000 : ℚ) : ℝ) := by
    have h := (log_br_808).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6658827/100000000) (δ := 39667/1250000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_809 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (809 : ℕ) / 2)) - ((620699/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66957989/20000000 : ℚ) : ℝ) ≤ Real.log (809 : ℕ) / 2 := by
    have h := (log_br_809).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (809 : ℕ) / 2 ≤ ((6695799/2000000 : ℚ) : ℝ) := by
    have h := (log_br_809).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26279153/100000000) (δ := 317267/10000000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_810 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (810 : ℕ) / 2)) - ((-2611059/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33485171/10000000 : ℚ) : ℝ) ≤ Real.log (810 : ℕ) / 2 := by
    have h := (log_br_810).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (810 : ℕ) / 2 ≤ ((66970343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_810).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 45874099/100000000) (δ := 317367/10000000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_811 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (811 : ℕ) / 2)) - ((-1731867/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1674567/500000 : ℚ) : ℝ) ≤ Real.log (811 : ℕ) / 2 := by
    have h := (log_br_811).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (811 : ℕ) / 2 ≤ ((66982681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_811).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16361313/25000000) (δ := 39667/1250000000) 1269 676
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_812 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (812 : ℕ) / 2)) - ((-9668737/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((66995003/20000000 : ℚ) : ℝ) ≤ Real.log (812 : ℕ) / 2 := by
    have h := (log_br_812).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (812 : ℕ) / 2 ≤ ((16748751/5000000 : ℚ) : ℝ) := by
    have h := (log_br_812).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -36043511/50000000) (δ := 317307/10000000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_813 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (813 : ℕ) / 2)) - ((-1014071/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67007311/20000000 : ℚ) : ℝ) ≤ Real.log (813 : ℕ) / 2 := by
    have h := (log_br_813).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (813 : ℕ) / 2 ≤ ((4187957/1250000 : ℚ) : ℝ) := by
    have h := (log_br_813).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -52563457/100000000) (δ := 317307/10000000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_814 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (814 : ℕ) / 2)) - ((1228227/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67019603/20000000 : ℚ) : ℝ) ≤ Real.log (814 : ℕ) / 2 := by
    have h := (log_br_814).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (814 : ℕ) / 2 ≤ ((16754901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_814).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4133159/12500000) (δ := 317307/10000000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_815 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (815 : ℕ) / 2)) - ((2139667/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67031881/20000000 : ℚ) : ℝ) ≤ Real.log (815 : ℕ) / 2 := by
    have h := (log_br_815).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (815 : ℕ) / 2 ≤ ((33515941/10000000 : ℚ) : ℝ) := by
    have h := (log_br_815).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2717859/20000000) (δ := 79349/2500000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_816 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (816 : ℕ) / 2)) - ((4863209/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67044143/20000000 : ℚ) : ℝ) ≤ Real.log (816 : ℕ) / 2 := by
    have h := (log_br_816).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (816 : ℕ) / 2 ≤ ((4190259/1250000 : ℚ) : ℝ) := by
    have h := (log_br_816).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5861303/100000000) (δ := 317307/10000000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_817 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (817 : ℕ) / 2)) - ((5305693/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6705639/2000000 : ℚ) : ℝ) ≤ Real.log (817 : ℕ) / 2 := by
    have h := (log_br_817).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (817 : ℕ) / 2 ≤ ((67056391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_817).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25288107/100000000) (δ := 317407/10000000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_818 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (818 : ℕ) / 2)) - ((-538037/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67068623/20000000 : ℚ) : ℝ) ≤ Real.log (818 : ℕ) / 2 := by
    have h := (log_br_818).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (818 : ℕ) / 2 ≤ ((4191789/1250000 : ℚ) : ℝ) := by
    have h := (log_br_818).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44692703/100000000) (δ := 317307/10000000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_819 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (819 : ℕ) / 2)) - ((-8371657/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1677021/500000 : ℚ) : ℝ) ≤ Real.log (819 : ℕ) / 2 := by
    have h := (log_br_819).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (819 : ℕ) / 2 ≤ ((67080841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_819).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 64071919/100000000) (δ := 19831/625000000) 1269 677
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_820 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (820 : ℕ) / 2)) - ((-9809381/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67093043/20000000 : ℚ) : ℝ) ≤ Real.log (820 : ℕ) / 2 := by
    have h := (log_br_820).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (820 : ℕ) / 2 ≤ ((16773261/5000000 : ℚ) : ℝ) := by
    have h := (log_br_820).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -14730141/20000000) (δ := 79331/2500000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_821 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (821 : ℕ) / 2)) - ((-5662123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67105231/20000000 : ℚ) : ℝ) ≤ Real.log (821 : ℕ) / 2 := by
    have h := (log_br_821).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (821 : ℕ) / 2 ≤ ((4194077/1250000 : ℚ) : ℝ) := by
    have h := (log_br_821).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5431749/10000000) (δ := 79331/2500000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_822 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (822 : ℕ) / 2)) - ((339173/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67117403/20000000 : ℚ) : ℝ) ≤ Real.log (822 : ℕ) / 2 := by
    have h := (log_br_822).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (822 : ℕ) / 2 ≤ ((16779351/5000000 : ℚ) : ℝ) := by
    have h := (log_br_822).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -7001931/20000000) (δ := 79331/2500000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_823 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (823 : ℕ) / 2)) - ((1617353/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33564781/10000000 : ℚ) : ℝ) ≤ Real.log (823 : ℕ) / 2 := by
    have h := (log_br_823).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (823 : ℕ) / 2 ≤ ((67129563/20000000 : ℚ) : ℝ) := by
    have h := (log_br_823).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15722441/100000000) (δ := 317279/10000000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_824 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (824 : ℕ) / 2)) - ((9899949/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13428341/4000000 : ℚ) : ℝ) ≤ Real.log (824 : ℕ) / 2 := by
    have h := (log_br_824).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (824 : ℕ) / 2 ≤ ((33570853/10000000 : ℚ) : ℝ) := by
    have h := (log_br_824).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3539393/100000000) (δ := 317379/10000000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_825 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (825 : ℕ) / 2)) - ((612879/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67153833/20000000 : ℚ) : ℝ) ≤ Real.log (825 : ℕ) / 2 := by
    have h := (log_br_825).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (825 : ℕ) / 2 ≤ ((33576917/10000000 : ℚ) : ℝ) := by
    have h := (log_br_825).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22777433/100000000) (δ := 317379/10000000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_826 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (826 : ℕ) / 2)) - ((-108719/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67165947/20000000 : ℚ) : ℝ) ≤ Real.log (826 : ℕ) / 2 := by
    have h := (log_br_826).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (826 : ℕ) / 2 ≤ ((16791487/5000000 : ℚ) : ℝ) := by
    have h := (log_br_826).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8398653/20000000) (δ := 79331/2500000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_827 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (827 : ℕ) / 2)) - ((-3842891/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33589023/10000000 : ℚ) : ℝ) ≤ Real.log (827 : ℕ) / 2 := by
    have h := (log_br_827).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (827 : ℕ) / 2 ≤ ((67178047/20000000 : ℚ) : ℝ) := by
    have h := (log_br_827).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7648163/12500000) (δ := 317279/10000000000) 1269 678
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_828 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (828 : ℕ) / 2)) - ((-9973649/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67190131/20000000 : ℚ) : ℝ) ≤ Real.log (828 : ℕ) / 2 := by
    have h := (log_br_828).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (828 : ℕ) / 2 ≤ ((16797533/5000000 : ℚ) : ℝ) := by
    have h := (log_br_828).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -76724497/100000000) (δ := 317451/10000000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_829 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (829 : ℕ) / 2)) - ((-6686131/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67202201/20000000 : ℚ) : ℝ) ≤ Real.log (829 : ℕ) / 2 := by
    have h := (log_br_829).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (829 : ℕ) / 2 ≤ ((33601101/10000000 : ℚ) : ℝ) := by
    have h := (log_br_829).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2878923/5000000) (δ := 79313/2500000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_830 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (830 : ℕ) / 2)) - ((326053/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67214257/20000000 : ℚ) : ℝ) ≤ Real.log (830 : ℕ) / 2 := by
    have h := (log_br_830).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (830 : ℕ) / 2 ≤ ((33607129/10000000 : ℚ) : ℝ) := by
    have h := (log_br_830).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3845463/10000000) (δ := 79313/2500000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_831 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (831 : ℕ) / 2)) - ((1787369/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67226297/20000000 : ℚ) : ℝ) ≤ Real.log (831 : ℕ) / 2 := by
    have h := (log_br_831).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (831 : ℕ) / 2 ≤ ((33613149/10000000 : ℚ) : ℝ) := by
    have h := (log_br_831).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -967809/5000000) (δ := 79313/2500000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_832 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (832 : ℕ) / 2)) - ((499969/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16809581/5000000 : ℚ) : ℝ) ≤ Real.log (832 : ℕ) / 2 := by
    have h := (log_br_832).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (832 : ℕ) / 2 ≤ ((2689533/800000 : ℚ) : ℝ) := by
    have h := (log_br_832).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -278351/100000000) (δ := 317351/10000000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_833 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (833 : ℕ) / 2)) - ((3654941/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2101573/625000 : ℚ) : ℝ) ≤ Real.log (833 : ℕ) / 2 := by
    have h := (log_br_833).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (833 : ℕ) / 2 ≤ ((67250337/20000000 : ℚ) : ℝ) := by
    have h := (log_br_833).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4693921/25000000) (δ := 317351/10000000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_834 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (834 : ℕ) / 2)) - ((4677/80000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33631167/10000000 : ℚ) : ℝ) ≤ Real.log (834 : ℕ) / 2 := by
    have h := (log_br_834).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (834 : ℕ) / 2 ≤ ((13452467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_834).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37807511/100000000) (δ := 39669/1250000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_835 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (835 : ℕ) / 2)) - ((-100877/156250 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67274317/20000000 : ℚ) : ℝ) ≤ Real.log (835 : ℕ) / 2 := by
    have h := (log_br_835).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (835 : ℕ) / 2 ≤ ((33637159/10000000 : ℚ) : ℝ) := by
    have h := (log_br_835).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 11363109/20000000) (δ := 79313/2500000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_836 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (836 : ℕ) / 2)) - ((-9940067/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33643143/10000000 : ℚ) : ℝ) ≤ Real.log (836 : ℕ) / 2 := by
    have h := (log_br_836).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (836 : ℕ) / 2 ≤ ((67286287/20000000 : ℚ) : ℝ) := by
    have h := (log_br_836).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 75801371/100000000) (δ := 39669/1250000000) 1269 679
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_837 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (837 : ℕ) / 2)) - ((-7967227/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((210307/62500 : ℚ) : ℝ) ≤ Real.log (837 : ℕ) / 2 := by
    have h := (log_br_837).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (837 : ℕ) / 2 ≤ ((67298241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_837).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62316229/100000000) (δ := 1983/62500000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_838 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (838 : ℕ) / 2)) - ((-408649/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67310181/20000000 : ℚ) : ℝ) ≤ Real.log (838 : ℕ) / 2 := by
    have h := (log_br_838).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (838 : ℕ) / 2 ≤ ((33655091/10000000 : ℚ) : ℝ) := by
    have h := (log_br_838).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -21687409/50000000) (δ := 15869/500000000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_839 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (839 : ℕ) / 2)) - ((1116887/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67322107/20000000 : ℚ) : ℝ) ≤ Real.log (839 : ℕ) / 2 := by
    have h := (log_br_839).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (839 : ℕ) / 2 ≤ ((16830527/5000000 : ℚ) : ℝ) := by
    have h := (log_br_839).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -61143/250000) (δ := 317323/10000000000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_840 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (840 : ℕ) / 2)) - ((9753411/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33667009/10000000 : ℚ) : ℝ) ≤ Real.log (840 : ℕ) / 2 := by
    have h := (log_br_840).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (840 : ℕ) / 2 ≤ ((67334019/20000000 : ℚ) : ℝ) := by
    have h := (log_br_840).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -347711/6250000) (δ := 317423/10000000000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_841 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (841 : ℕ) / 2)) - ((2153987/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16836479/5000000 : ℚ) : ℝ) ≤ Real.log (841 : ℕ) / 2 := by
    have h := (log_br_841).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (841 : ℕ) / 2 ≤ ((67345917/20000000 : ℚ) : ℝ) := by
    have h := (log_br_841).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6654913/50000000) (δ := 1983/62500000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_842 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (842 : ℕ) / 2)) - ((1402733/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((336789/100000 : ℚ) : ℝ) ≤ Real.log (842 : ℕ) / 2 := by
    have h := (log_br_842).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (842 : ℕ) / 2 ≤ ((67357801/20000000 : ℚ) : ℝ) := by
    have h := (log_br_842).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 32160821/100000000) (δ := 1983/62500000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_843 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (843 : ℕ) / 2)) - ((-282343/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67369669/20000000 : ℚ) : ℝ) ≤ Real.log (843 : ℕ) / 2 := by
    have h := (log_br_843).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (843 : ℕ) / 2 ≤ ((6736967/2000000 : ℚ) : ℝ) := by
    have h := (log_br_843).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25494011/50000000) (δ := 15869/500000000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_844 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (844 : ℕ) / 2)) - ((-4697083/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16845381/5000000 : ℚ) : ℝ) ≤ Real.log (844 : ℕ) / 2 := by
    have h := (log_br_844).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (844 : ℕ) / 2 ≤ ((2695261/800000 : ℚ) : ℝ) := by
    have h := (log_br_844).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 8724127/12500000) (δ := 1983/62500000) 1269 680
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_845 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (845 : ℕ) / 2)) - ((-9204747/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33696683/10000000 : ℚ) : ℝ) ≤ Real.log (845 : ℕ) / 2 := by
    have h := (log_br_845).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (845 : ℕ) / 2 ≤ ((67393367/20000000 : ℚ) : ℝ) := by
    have h := (log_br_845).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -17125561/25000000) (δ := 158647/5000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_846 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (846 : ℕ) / 2)) - ((-4067287/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67405193/20000000 : ℚ) : ℝ) ≤ Real.log (846 : ℕ) / 2 := by
    have h := (log_br_846).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (846 : ℕ) / 2 ≤ ((33702597/10000000 : ℚ) : ℝ) := by
    have h := (log_br_846).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9948333/20000000) (δ := 158697/5000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_847 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (847 : ℕ) / 2)) - ((3246717/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33708503/10000000 : ℚ) : ℝ) ≤ Real.log (847 : ℕ) / 2 := by
    have h := (log_br_847).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (847 : ℕ) / 2 ≤ ((67417007/20000000 : ℚ) : ℝ) := by
    have h := (log_br_847).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15501647/50000000) (δ := 158647/5000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_848 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (848 : ℕ) / 2)) - ((2204157/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33714403/10000000 : ℚ) : ℝ) ≤ Real.log (848 : ℕ) / 2 := by
    have h := (log_br_848).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (848 : ℕ) / 2 ≤ ((67428807/20000000 : ℚ) : ℝ) := by
    have h := (log_br_848).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1535693/12500000) (δ := 158647/5000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_849 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (849 : ℕ) / 2)) - ((9673253/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67440591/20000000 : ℚ) : ℝ) ≤ Real.log (849 : ℕ) / 2 := by
    have h := (log_br_849).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (849 : ℕ) / 2 ≤ ((4215037/1250000 : ℚ) : ℝ) := by
    have h := (log_br_849).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1602103/25000000) (δ := 317309/10000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_850 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (850 : ℕ) / 2)) - ((5375479/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67452363/20000000 : ℚ) : ℝ) ≤ Real.log (850 : ℕ) / 2 := by
    have h := (log_br_850).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (850 : ℕ) / 2 ≤ ((16863091/5000000 : ℚ) : ℝ) := by
    have h := (log_br_850).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 25081747/100000000) (δ := 317309/10000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_851 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (851 : ℕ) / 2)) - ((-44393/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67464121/20000000 : ℚ) : ℝ) ≤ Real.log (851 : ℕ) / 2 := by
    have h := (log_br_851).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (851 : ℕ) / 2 ≤ ((33732061/10000000 : ℚ) : ℝ) := by
    have h := (log_br_851).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 349863/800000) (δ := 158697/5000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_852 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (852 : ℕ) / 2)) - ((-7978229/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13495173/4000000 : ℚ) : ℝ) ≤ Real.log (852 : ℕ) / 2 := by
    have h := (log_br_852).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (852 : ℕ) / 2 ≤ ((33737933/10000000 : ℚ) : ℝ) := by
    have h := (log_br_852).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12472359/20000000) (δ := 158697/5000000000) 1269 681
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_853 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (853 : ℕ) / 2)) - ((-9952849/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13497519/4000000 : ℚ) : ℝ) ≤ Real.log (853 : ℕ) / 2 := by
    have h := (log_br_853).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (853 : ℕ) / 2 ≤ ((16871899/5000000 : ℚ) : ℝ) := by
    have h := (log_br_853).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38055563/50000000) (δ := 317437/10000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_854 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (854 : ℕ) / 2)) - ((-6670697/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67499311/20000000 : ℚ) : ℝ) ≤ Real.log (854 : ℕ) / 2 := by
    have h := (log_br_854).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (854 : ℕ) / 2 ≤ ((4218707/1250000 : ℚ) : ℝ) := by
    have h := (log_br_854).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57526621/100000000) (δ := 317437/10000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_855 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (855 : ℕ) / 2)) - ((24573/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33755507/10000000 : ℚ) : ℝ) ≤ Real.log (855 : ℕ) / 2 := by
    have h := (log_br_855).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (855 : ℕ) / 2 ≤ ((13502203/4000000 : ℚ) : ℝ) := by
    have h := (log_br_855).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -38962737/100000000) (δ := 317337/10000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_856 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (856 : ℕ) / 2)) - ((427829/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67522703/20000000 : ℚ) : ℝ) ≤ Real.log (856 : ℕ) / 2 := by
    have h := (log_br_856).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (856 : ℕ) / 2 ≤ ((4220169/1250000 : ℚ) : ℝ) := by
    have h := (log_br_856).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20421061/100000000) (δ := 317437/10000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_857 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (857 : ℕ) / 2)) - ((4985567/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67534379/20000000 : ℚ) : ℝ) ≤ Real.log (857 : ℕ) / 2 := by
    have h := (log_br_857).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (857 : ℕ) / 2 ≤ ((3376719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_857).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -950003/50000000) (δ := 317437/10000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_858 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (858 : ℕ) / 2)) - ((7876011/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1688651/500000 : ℚ) : ℝ) ≤ Real.log (858 : ℕ) / 2 := by
    have h := (log_br_858).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (858 : ℕ) / 2 ≤ ((67546041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_858).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2074657/12500000) (δ := 158683/5000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_859 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (859 : ℕ) / 2)) - ((166991/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67557689/20000000 : ℚ) : ℝ) ≤ Real.log (859 : ℕ) / 2 := by
    have h := (log_br_859).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (859 : ℕ) / 2 ≤ ((6755769/2000000 : ℚ) : ℝ) := by
    have h := (log_br_859).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 17537741/50000000) (δ := 158633/5000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_860 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (860 : ℕ) / 2)) - ((-539969/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67569323/20000000 : ℚ) : ℝ) ≤ Real.log (860 : ℕ) / 2 := by
    have h := (log_br_860).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (860 : ℕ) / 2 ≤ ((16892331/5000000 : ℚ) : ℝ) := by
    have h := (log_br_860).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 26764957/50000000) (δ := 317437/10000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_861 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (861 : ℕ) / 2)) - ((-1931239/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13516189/4000000 : ℚ) : ℝ) ≤ Real.log (861 : ℕ) / 2 := by
    have h := (log_br_861).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (861 : ℕ) / 2 ≤ ((33790473/10000000 : ℚ) : ℝ) := by
    have h := (log_br_861).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 562229/781250) (δ := 158633/5000000000) 1269 682
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_862 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (862 : ℕ) / 2)) - ((-177997/200000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8449069/2500000 : ℚ) : ℝ) ≤ Real.log (862 : ℕ) / 2 := by
    have h := (log_br_862).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (862 : ℕ) / 2 ≤ ((67592553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_862).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -66702717/100000000) (δ := 63453/2000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_863 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (863 : ℕ) / 2)) - ((-707679/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33802073/10000000 : ℚ) : ℝ) ≤ Real.log (863 : ℕ) / 2 := by
    have h := (log_br_863).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (863 : ℕ) / 2 ≤ ((67604147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_863).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -24155867/50000000) (δ := 158719/5000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_864 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (864 : ℕ) / 2)) - ((145817/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67615727/20000000 : ℚ) : ℝ) ≤ Real.log (864 : ℕ) / 2 := by
    have h := (log_br_864).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (864 : ℕ) / 2 ≤ ((4225983/1250000 : ℚ) : ℝ) := by
    have h := (log_br_864).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -29941373/100000000) (δ := 158669/5000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_865 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (865 : ℕ) / 2)) - ((8944193/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13525459/4000000 : ℚ) : ℝ) ≤ Real.log (865 : ℕ) / 2 := by
    have h := (log_br_865).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (865 : ℕ) / 2 ≤ ((2113353/625000 : ℚ) : ℝ) := by
    have h := (log_br_865).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11591633/100000000) (δ := 158669/5000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_866 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (866 : ℕ) / 2)) - ((2409803/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67638849/20000000 : ℚ) : ℝ) ≤ Real.log (866 : ℕ) / 2 := by
    have h := (log_br_866).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (866 : ℕ) / 2 ≤ ((1352777/400000 : ℚ) : ℝ) := by
    have h := (log_br_866).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6735899/100000000) (δ := 63473/2000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_867 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (867 : ℕ) / 2)) - ((269457/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67650389/20000000 : ℚ) : ℝ) ≤ Real.log (867 : ℕ) / 2 := by
    have h := (log_br_867).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (867 : ℕ) / 2 ≤ ((6765039/2000000 : ℚ) : ℝ) := by
    have h := (log_br_867).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3130153/12500000) (δ := 63473/2000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_868 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (868 : ℕ) / 2)) - ((-807963/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67661917/20000000 : ℚ) : ℝ) ≤ Real.log (868 : ℕ) / 2 := by
    have h := (log_br_868).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (868 : ℕ) / 2 ≤ ((33830959/10000000 : ℚ) : ℝ) := by
    have h := (log_br_868).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21663757/50000000) (δ := 63473/2000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_869 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (869 : ℕ) / 2)) - ((-3894367/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67673431/20000000 : ℚ) : ℝ) ≤ Real.log (869 : ℕ) / 2 := by
    have h := (log_br_869).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (869 : ℕ) / 2 ≤ ((8459179/2500000 : ℚ) : ℝ) := by
    have h := (log_br_869).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61591597/100000000) (δ := 158669/5000000000) 1269 683
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_870 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (870 : ℕ) / 2)) - ((-4993291/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16921233/5000000 : ℚ) : ℝ) ≤ Real.log (870 : ℕ) / 2 := by
    have h := (log_br_870).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (870 : ℕ) / 2 ≤ ((67684933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_870).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3089783/4000000) (δ := 317393/10000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_871 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (871 : ℕ) / 2)) - ((-3552247/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67696419/20000000 : ℚ) : ℝ) ≤ Real.log (871 : ℕ) / 2 := by
    have h := (log_br_871).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (871 : ℕ) / 2 ≤ ((3384821/1000000 : ℚ) : ℝ) := by
    have h := (log_br_871).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -59023321/100000000) (δ := 317293/10000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_872 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (872 : ℕ) / 2)) - ((-620079/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33853947/10000000 : ℚ) : ℝ) ≤ Real.log (872 : ℕ) / 2 := by
    have h := (log_br_872).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (872 : ℕ) / 2 ≤ ((13541579/4000000 : ℚ) : ℝ) := by
    have h := (log_br_872).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -20410551/50000000) (δ := 31731/1000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_873 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (873 : ℕ) / 2)) - ((6171793/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13543871/4000000 : ℚ) : ℝ) ≤ Real.log (873 : ℕ) / 2 := by
    have h := (log_br_873).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (873 : ℕ) / 2 ≤ ((16929839/5000000 : ℚ) : ℝ) := by
    have h := (log_br_873).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -22641091/100000000) (δ := 317293/10000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_874 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (874 : ℕ) / 2)) - ((1967949/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67730803/20000000 : ℚ) : ℝ) ≤ Real.log (874 : ℕ) / 2 := by
    have h := (log_br_874).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (874 : ℕ) / 2 ≤ ((16932701/5000000 : ℚ) : ℝ) := by
    have h := (log_br_874).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4481701/100000000) (δ := 317293/10000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_875 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (875 : ℕ) / 2)) - ((1068077/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33871119/10000000 : ℚ) : ℝ) ≤ Real.log (875 : ℕ) / 2 := by
    have h := (log_br_875).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (875 : ℕ) / 2 ≤ ((67742239/20000000 : ℚ) : ℝ) := by
    have h := (log_br_875).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3414267/25000000) (δ := 31731/1000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_876 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (876 : ℕ) / 2)) - ((1476587/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3387683/1000000 : ℚ) : ℝ) ≤ Real.log (876 : ℕ) / 2 := by
    have h := (log_br_876).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (876 : ℕ) / 2 ≤ ((67753661/20000000 : ℚ) : ℝ) := by
    have h := (log_br_876).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6355043/20000000) (δ := 317393/10000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_877 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (877 : ℕ) / 2)) - ((-4115129/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67765069/20000000 : ℚ) : ℝ) ≤ Real.log (877 : ℕ) / 2 := by
    have h := (log_br_877).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (877 : ℕ) / 2 ≤ ((6776507/2000000 : ℚ) : ℝ) := by
    have h := (log_br_877).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24936371/50000000) (δ := 31741/1000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_878 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (878 : ℕ) / 2)) - ((-9116123/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13555293/4000000 : ℚ) : ℝ) ≤ Real.log (878 : ℕ) / 2 := by
    have h := (log_br_878).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (878 : ℕ) / 2 ≤ ((33888233/10000000 : ℚ) : ℝ) := by
    have h := (log_br_878).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 67949647/100000000) (δ := 31741/1000000000) 1269 684
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_879 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (879 : ℕ) / 2)) - ((-4778681/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8473481/2500000 : ℚ) : ℝ) ≤ Real.log (879 : ℕ) / 2 := by
    have h := (log_br_879).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (879 : ℕ) / 2 ≤ ((67787849/20000000 : ℚ) : ℝ) := by
    have h := (log_br_879).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35536851/50000000) (δ := 158691/5000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_880 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (880 : ℕ) / 2)) - ((-5232513/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67799219/20000000 : ℚ) : ℝ) ≤ Real.log (880 : ℕ) / 2 := by
    have h := (log_br_880).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (880 : ℕ) / 2 ≤ ((3389961/1000000 : ℚ) : ℝ) := by
    have h := (log_br_880).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26518227/50000000) (δ := 317421/10000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_881 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (881 : ℕ) / 2)) - ((1691231/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4238161/1250000 : ℚ) : ℝ) ≤ Real.log (881 : ℕ) / 2 := by
    have h := (log_br_881).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (881 : ℕ) / 2 ≤ ((67810577/20000000 : ℚ) : ℝ) := by
    have h := (log_br_881).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8755353/25000000) (δ := 158691/5000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_882 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (882 : ℕ) / 2)) - ((3884467/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((423887/125000 : ℚ) : ℝ) ≤ Real.log (882 : ℕ) / 2 := by
    have h := (log_br_882).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (882 : ℕ) / 2 ≤ ((67821921/20000000 : ℚ) : ℝ) := by
    have h := (log_br_882).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1064187/6250000) (δ := 158691/5000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_883 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (883 : ℕ) / 2)) - ((1998561/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16958313/5000000 : ℚ) : ℝ) ≤ Real.log (883 : ℕ) / 2 := by
    have h := (log_br_883).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (883 : ℕ) / 2 ≤ ((67833253/20000000 : ℚ) : ℝ) := by
    have h := (log_br_883).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 948393/100000000) (δ := 158691/5000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_884 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (884 : ℕ) / 2)) - ((1818857/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6784457/2000000 : ℚ) : ℝ) ≤ Real.log (884 : ℕ) / 2 := by
    have h := (log_br_884).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (884 : ℕ) / 2 ≤ ((67844571/20000000 : ℚ) : ℝ) := by
    have h := (log_br_884).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1890157/10000000) (δ := 317321/10000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_885 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (885 : ℕ) / 2)) - ((48607/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16963969/5000000 : ℚ) : ℝ) ≤ Real.log (885 : ℕ) / 2 := by
    have h := (log_br_885).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (885 : ℕ) / 2 ≤ ((67855877/20000000 : ℚ) : ℝ) := by
    have h := (log_br_885).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36835713/100000000) (δ := 158691/5000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_886 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (886 : ℕ) / 2)) - ((-5803619/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67867169/20000000 : ℚ) : ℝ) ≤ Real.log (886 : ℕ) / 2 := by
    have h := (log_br_886).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (886 : ℕ) / 2 ≤ ((6786717/2000000 : ℚ) : ℝ) := by
    have h := (log_br_886).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27374617/50000000) (δ := 158641/5000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_887 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (887 : ℕ) / 2)) - ((-9723027/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67878449/20000000 : ℚ) : ℝ) ≤ Real.log (887 : ℕ) / 2 := by
    have h := (log_br_887).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (887 : ℕ) / 2 ≤ ((1357569/400000 : ℚ) : ℝ) := by
    have h := (log_br_887).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 36321067/50000000) (δ := 158641/5000000000) 1269 685
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_888 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (888 : ℕ) / 2)) - ((-1774869/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67889717/20000000 : ℚ) : ℝ) ≤ Real.log (888 : ℕ) / 2 := by
    have h := (log_br_888).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (888 : ℕ) / 2 ≤ ((33944859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_888).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -33281817/50000000) (δ := 6347/200000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_889 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (889 : ℕ) / 2)) - ((-737417/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16975243/5000000 : ℚ) : ℝ) ≤ Real.log (889 : ℕ) / 2 := by
    have h := (log_br_889).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (889 : ℕ) / 2 ≤ ((67900973/20000000 : ℚ) : ℝ) := by
    have h := (log_br_889).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4871039/10000000) (δ := 317253/10000000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_890 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (890 : ℕ) / 2)) - ((1647083/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33956107/10000000 : ℚ) : ℝ) ≤ Real.log (890 : ℕ) / 2 := by
    have h := (log_br_890).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (890 : ℕ) / 2 ≤ ((13582443/4000000 : ℚ) : ℝ) := by
    have h := (log_br_890).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -3859721/12500000) (δ := 6349/200000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_891 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (891 : ℕ) / 2)) - ((8665407/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16980861/5000000 : ℚ) : ℝ) ≤ Real.log (891 : ℕ) / 2 := by
    have h := (log_br_891).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (891 : ℕ) / 2 ≤ ((13584689/4000000 : ℚ) : ℝ) := by
    have h := (log_br_891).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -653209/5000000) (δ := 317253/10000000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_892 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (892 : ℕ) / 2)) - ((9821641/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67934661/20000000 : ℚ) : ℝ) ≤ Real.log (892 : ℕ) / 2 := by
    have h := (log_br_892).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (892 : ℕ) / 2 ≤ ((33967331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_892).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2364393/50000000) (δ := 6347/200000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_893 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (893 : ℕ) / 2)) - ((1243149/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13589173/4000000 : ℚ) : ℝ) ≤ Real.log (893 : ℕ) / 2 := by
    have h := (log_br_893).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (893 : ℕ) / 2 ≤ ((33972933/10000000 : ℚ) : ℝ) := by
    have h := (log_br_893).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22501131/100000000) (δ := 6347/200000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_894 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (894 : ℕ) / 2)) - ((-393711/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67957057/20000000 : ℚ) : ℝ) ≤ Real.log (894 : ℕ) / 2 := by
    have h := (log_br_894).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (894 : ℕ) / 2 ≤ ((33978529/10000000 : ℚ) : ℝ) := by
    have h := (log_br_894).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40254441/100000000) (δ := 6347/200000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_895 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (895 : ℕ) / 2)) - ((-6807253/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((67968237/20000000 : ℚ) : ℝ) ≤ Real.log (895 : ℕ) / 2 := by
    have h := (log_br_895).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (895 : ℕ) / 2 ≤ ((33984119/10000000 : ℚ) : ℝ) := by
    have h := (log_br_895).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14497179/25000000) (δ := 6347/200000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_896 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (896 : ℕ) / 2)) - ((-496783/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((16994851/5000000 : ℚ) : ℝ) ≤ Real.log (896 : ℕ) / 2 := by
    have h := (log_br_896).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (896 : ℕ) / 2 ≤ ((13595881/4000000 : ℚ) : ℝ) := by
    have h := (log_br_896).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7570237/10000000) (δ := 317253/10000000000) 1269 686
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_897 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (897 : ℕ) / 2)) - ((-1657167/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((33995279/10000000 : ℚ) : ℝ) ≤ Real.log (897 : ℕ) / 2 := by
    have h := (log_br_897).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (897 : ℕ) / 2 ≤ ((67990559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_897).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6368423/10000000) (δ := 12693/400000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_898 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (898 : ℕ) / 2)) - ((-83237/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((680017/200000 : ℚ) : ℝ) ≤ Real.log (898 : ℕ) / 2 := by
    have h := (log_br_898).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (898 : ℕ) / 2 ≤ ((68001701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_898).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -46010233/100000000) (δ := 158689/5000000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_899 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (899 : ℕ) / 2)) - ((4228477/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6801283/2000000 : ℚ) : ℝ) ≤ Real.log (899 : ℕ) / 2 := by
    have h := (log_br_899).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (899 : ℕ) / 2 ≤ ((68012831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_899).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2835527/10000000) (δ := 12693/400000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_900 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (900 : ℕ) / 2)) - ((9094499/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68023947/20000000 : ℚ) : ℝ) ≤ Real.log (900 : ℕ) / 2 := by
    have h := (log_br_900).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (900 : ℕ) / 2 ≤ ((17005987/5000000 : ℚ) : ℝ) := by
    have h := (log_br_900).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10720929/100000000) (δ := 158639/5000000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_901 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (901 : ℕ) / 2)) - ((75173/78125 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17008763/5000000 : ℚ) : ℝ) ≤ Real.log (901 : ℕ) / 2 := by
    have h := (log_br_901).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (901 : ℕ) / 2 ≤ ((68035053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_901).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 6894377/100000000) (δ := 158689/5000000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_902 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (902 : ℕ) / 2)) - ((5573331/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13609229/4000000 : ℚ) : ℝ) ≤ Real.log (902 : ℕ) / 2 := by
    have h := (log_br_902).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (902 : ℕ) / 2 ≤ ((34023073/10000000 : ℚ) : ℝ) := by
    have h := (log_br_902).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 24490649/100000000) (δ := 12697/400000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_903 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (903 : ℕ) / 2)) - ((-44649/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2722289/800000 : ℚ) : ℝ) ≤ Real.log (903 : ℕ) / 2 := by
    have h := (log_br_903).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (903 : ℕ) / 2 ≤ ((34028613/10000000 : ℚ) : ℝ) := by
    have h := (log_br_903).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42066299/100000000) (δ := 12697/400000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_904 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (904 : ℕ) / 2)) - ((-7271219/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68068293/20000000 : ℚ) : ℝ) ≤ Real.log (904 : ℕ) / 2 := by
    have h := (log_br_904).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (904 : ℕ) / 2 ≤ ((34034147/10000000 : ℚ) : ℝ) := by
    have h := (log_br_904).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 29811457/50000000) (δ := 12697/400000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_905 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (905 : ℕ) / 2)) - ((-624049/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68079349/20000000 : ℚ) : ℝ) ≤ Real.log (905 : ℕ) / 2 := by
    have h := (log_br_905).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (905 : ℕ) / 2 ≤ ((1361587/400000 : ℚ) : ℝ) := by
    have h := (log_br_905).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38580247/50000000) (δ := 12697/400000000) 1269 687
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_906 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (906 : ℕ) / 2)) - ((-998447/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68090393/20000000 : ℚ) : ℝ) ≤ Real.log (906 : ℕ) / 2 := by
    have h := (log_br_906).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (906 : ℕ) / 2 ≤ ((34045197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_906).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -31200297/50000000) (δ := 317297/10000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_907 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (907 : ℕ) / 2)) - ((-223409/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4256339/1250000 : ℚ) : ℝ) ≤ Real.log (907 : ℕ) / 2 := by
    have h := (log_br_907).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (907 : ℕ) / 2 ≤ ((2724057/800000 : ℚ) : ℝ) := by
    have h := (log_br_907).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4490267/10000000) (δ := 317397/10000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_908 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (908 : ℕ) / 2)) - ((4563111/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68112443/20000000 : ℚ) : ℝ) ≤ Real.log (908 : ℕ) / 2 := by
    have h := (log_br_908).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (908 : ℕ) / 2 ≤ ((17028111/5000000 : ℚ) : ℝ) := by
    have h := (log_br_908).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13711891/50000000) (δ := 158703/5000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_909 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (909 : ℕ) / 2)) - ((9216219/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1362469/400000 : ℚ) : ℝ) ≤ Real.log (909 : ℕ) / 2 := by
    have h := (log_br_909).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (909 : ℕ) / 2 ≤ ((68123451/20000000 : ℚ) : ℝ) := by
    have h := (log_br_909).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1245491/12500000) (δ := 158653/5000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_910 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (910 : ℕ) / 2)) - ((2389023/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13626889/4000000 : ℚ) : ℝ) ≤ Real.log (910 : ℕ) / 2 := by
    have h := (log_br_910).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (910 : ℕ) / 2 ≤ ((34067223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_910).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7476891/100000000) (δ := 317297/10000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_911 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (911 : ℕ) / 2)) - ((5437083/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17036357/5000000 : ℚ) : ℝ) ≤ Real.log (911 : ℕ) / 2 := by
    have h := (log_br_911).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (911 : ℕ) / 2 ≤ ((68145429/20000000 : ℚ) : ℝ) := by
    have h := (log_br_911).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 995947/4000000) (δ := 317397/10000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_912 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (912 : ℕ) / 2)) - ((-302409/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68156399/20000000 : ℚ) : ℝ) ≤ Real.log (912 : ℕ) / 2 := by
    have h := (log_br_912).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (912 : ℕ) / 2 ≤ ((170391/50000 : ℚ) : ℝ) := by
    have h := (log_br_912).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 42301423/100000000) (δ := 158703/5000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_913 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (913 : ℕ) / 2)) - ((-7288283/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34083679/10000000 : ℚ) : ℝ) ≤ Real.log (913 : ℕ) / 2 := by
    have h := (log_br_913).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (913 : ℕ) / 2 ≤ ((68167359/20000000 : ℚ) : ℝ) := by
    have h := (log_br_913).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 59685137/100000000) (δ := 158653/5000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_914 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (914 : ℕ) / 2)) - ((-2495561/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13635661/4000000 : ℚ) : ℝ) ≤ Real.log (914 : ℕ) / 2 := by
    have h := (log_br_914).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (914 : ℕ) / 2 ≤ ((34089153/10000000 : ℚ) : ℝ) := by
    have h := (log_br_914).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9631227/12500000) (δ := 317297/10000000000) 1269 688
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_915 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (915 : ℕ) / 2)) - ((-8055307/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1704731/500000 : ℚ) : ℝ) ≤ Real.log (915 : ℕ) / 2 := by
    have h := (log_br_915).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (915 : ℕ) / 2 ≤ ((68189241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_915).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62684173/100000000) (δ := 317269/10000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_916 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (916 : ℕ) / 2)) - ((-2411069/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68200163/20000000 : ℚ) : ℝ) ≤ Real.log (916 : ℕ) / 2 := by
    have h := (log_br_916).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (916 : ℕ) / 2 ≤ ((17050041/5000000 : ℚ) : ℝ) := by
    have h := (log_br_916).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -11339391/25000000) (δ := 317369/10000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_917 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (917 : ℕ) / 2)) - ((4338817/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34105537/10000000 : ℚ) : ℝ) ≤ Real.log (917 : ℕ) / 2 := by
    have h := (log_br_917).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (917 : ℕ) / 2 ≤ ((2728443/800000 : ℚ) : ℝ) := by
    have h := (log_br_917).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28049991/100000000) (δ := 158717/5000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_918 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (918 : ℕ) / 2)) - ((9087747/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68221973/20000000 : ℚ) : ℝ) ≤ Real.log (918 : ℕ) / 2 := by
    have h := (log_br_918).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (918 : ℕ) / 2 ≤ ((34110987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_918).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -2690363/25000000) (δ := 158667/5000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_919 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (919 : ℕ) / 2)) - ((2415727/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68232861/20000000 : ℚ) : ℝ) ≤ Real.log (919 : ℕ) / 2 := by
    have h := (log_br_919).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (919 : ℕ) / 2 ≤ ((34116431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_919).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3254819/50000000) (δ := 158667/5000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_920 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (920 : ℕ) / 2)) - ((2906771/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8530467/2500000 : ℚ) : ℝ) ≤ Real.log (920 : ℕ) / 2 := by
    have h := (log_br_920).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (920 : ℕ) / 2 ≤ ((68243737/20000000 : ℚ) : ℝ) := by
    have h := (log_br_920).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23760107/100000000) (δ := 317269/10000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_921 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (921 : ℕ) / 2)) - ((-344371/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((341273/100000 : ℚ) : ℝ) ≤ Real.log (921 : ℕ) / 2 := by
    have h := (log_br_921).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (921 : ℕ) / 2 ≤ ((68254601/20000000 : ℚ) : ℝ) := by
    have h := (log_br_921).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 40993127/100000000) (δ := 317269/10000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_922 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (922 : ℕ) / 2)) - ((-3435493/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17066363/5000000 : ℚ) : ℝ) ≤ Real.log (922 : ℕ) / 2 := by
    have h := (log_br_922).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (922 : ℕ) / 2 ≤ ((68265453/20000000 : ℚ) : ℝ) := by
    have h := (log_br_922).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 7275889/12500000) (δ := 317269/10000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_923 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (923 : ℕ) / 2)) - ((-9921339/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17069073/5000000 : ℚ) : ℝ) ≤ Real.log (923 : ℕ) / 2 := by
    have h := (log_br_923).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (923 : ℕ) / 2 ≤ ((68276293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_923).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37701031/50000000) (δ := 317269/10000000000) 1269 689
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_924 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (924 : ℕ) / 2)) - ((-8464433/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((853589/250000 : ℚ) : ℝ) ≤ Real.log (924 : ℕ) / 2 := by
    have h := (log_br_924).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (924 : ℕ) / 2 ≤ ((68287121/20000000 : ℚ) : ℝ) := by
    have h := (log_br_924).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8062707/12500000) (δ := 158681/5000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_925 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (925 : ℕ) / 2)) - ((-793369/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68297937/20000000 : ℚ) : ℝ) ≤ Real.log (925 : ℕ) / 2 := by
    have h := (log_br_925).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (925 : ℕ) / 2 ≤ ((34148969/10000000 : ℚ) : ℝ) := by
    have h := (log_br_925).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -47343189/100000000) (δ := 317441/10000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_926 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (926 : ℕ) / 2)) - ((1773747/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34154371/10000000 : ℚ) : ℝ) ≤ Real.log (926 : ℕ) / 2 := by
    have h := (log_br_926).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (926 : ℕ) / 2 ≤ ((68308743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_926).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -15101879/50000000) (δ := 317341/10000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_927 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (927 : ℕ) / 2)) - ((346463/400000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13663907/4000000 : ℚ) : ℝ) ≤ Real.log (927 : ℕ) / 2 := by
    have h := (log_br_927).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (927 : ℕ) / 2 ≤ ((4269971/1250000 : ℚ) : ℝ) := by
    have h := (log_br_927).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6541681/50000000) (δ := 158631/5000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_928 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (928 : ℕ) / 2)) - ((4935511/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68330317/20000000 : ℚ) : ℝ) ≤ Real.log (928 : ℕ) / 2 := by
    have h := (log_br_928).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (928 : ℕ) / 2 ≤ ((34165159/10000000 : ℚ) : ℝ) := by
    have h := (log_br_928).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2009793/50000000) (δ := 317441/10000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_929 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (929 : ℕ) / 2)) - ((207617/312500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68341087/20000000 : ℚ) : ℝ) ≤ Real.log (929 : ℕ) / 2 := by
    have h := (log_br_929).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (929 : ℕ) / 2 ≤ ((2135659/625000 : ℚ) : ℝ) := by
    have h := (log_br_929).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 10551749/50000000) (δ := 158631/5000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_930 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (930 : ℕ) / 2)) - ((44047/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13670369/4000000 : ℚ) : ℝ) ≤ Real.log (930 : ℕ) / 2 := by
    have h := (log_br_930).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (930 : ℕ) / 2 ≤ ((34175923/10000000 : ℚ) : ℝ) := by
    have h := (log_br_930).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4771047/12500000) (δ := 317441/10000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_931 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (931 : ℕ) / 2)) - ((-2977291/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2136331/625000 : ℚ) : ℝ) ≤ Real.log (931 : ℕ) / 2 := by
    have h := (log_br_931).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (931 : ℕ) / 2 ≤ ((68362593/20000000 : ℚ) : ℝ) := by
    have h := (log_br_931).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13803951/25000000) (δ := 158681/5000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_932 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (932 : ℕ) / 2)) - ((-605297/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4273333/1250000 : ℚ) : ℝ) ≤ Real.log (932 : ℕ) / 2 := by
    have h := (log_br_932).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (932 : ℕ) / 2 ≤ ((68373329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_932).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 9030723/12500000) (δ := 158681/5000000000) 1269 690
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_933 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (933 : ℕ) / 2)) - ((-9095167/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17096013/5000000 : ℚ) : ℝ) ≤ Real.log (933 : ℕ) / 2 := by
    have h := (log_br_933).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (933 : ℕ) / 2 ≤ ((68384053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_933).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67822903/100000000) (δ := 79353/2500000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_934 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (934 : ℕ) / 2)) - ((-2230681/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17098691/5000000 : ℚ) : ℝ) ≤ Real.log (934 : ℕ) / 2 := by
    have h := (log_br_934).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (934 : ℕ) / 2 ≤ ((13678953/4000000 : ℚ) : ℝ) := by
    have h := (log_br_934).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -50830993/100000000) (δ := 79353/2500000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_935 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (935 : ℕ) / 2)) - ((2148469/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13681093/4000000 : ℚ) : ℝ) ≤ Real.log (935 : ℕ) / 2 := by
    have h := (log_br_935).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (935 : ℕ) / 2 ≤ ((34202733/10000000 : ℚ) : ℝ) := by
    have h := (log_br_935).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8464133/25000000) (δ := 2479/78125000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_936 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (936 : ℕ) / 2)) - ((390027/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34208077/10000000 : ℚ) : ℝ) ≤ Real.log (936 : ℕ) / 2 := by
    have h := (log_br_936).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (936 : ℕ) / 2 ≤ ((13683231/4000000 : ℚ) : ℝ) := by
    have h := (log_br_936).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8450553/50000000) (δ := 317291/10000000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_937 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (937 : ℕ) / 2)) - ((9999989/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4276677/1250000 : ℚ) : ℝ) ≤ Real.log (937 : ℕ) / 2 := by
    have h := (log_br_937).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (937 : ℕ) / 2 ≤ ((68426833/20000000 : ℚ) : ℝ) := by
    have h := (log_br_937).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 4609/12500000) (δ := 79353/2500000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_938 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (938 : ℕ) / 2)) - ((7786431/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68437499/20000000 : ℚ) : ℝ) ≤ Real.log (938 : ℕ) / 2 := by
    have h := (log_br_938).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (938 : ℕ) / 2 ≤ ((219/64 : ℚ) : ℝ) := by
    have h := (log_br_938).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 84787/500000) (δ := 317391/10000000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_939 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (939 : ℕ) / 2)) - ((1073773/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34224077/10000000 : ℚ) : ℝ) ≤ Real.log (939 : ℕ) / 2 := by
    have h := (log_br_939).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (939 : ℕ) / 2 ≤ ((13689631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_939).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 16929447/50000000) (δ := 317291/10000000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_940 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (940 : ℕ) / 2)) - ((-1107453/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34229399/10000000 : ℚ) : ℝ) ≤ Real.log (940 : ℕ) / 2 := by
    have h := (log_br_940).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (940 : ℕ) / 2 ≤ ((68458799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_940).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 50742939/100000000) (δ := 317291/10000000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_941 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (941 : ℕ) / 2)) - ((-56621/62500 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68469431/20000000 : ℚ) : ℝ) ≤ Real.log (941 : ℕ) / 2 := by
    have h := (log_br_941).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (941 : ℕ) / 2 ≤ ((8558679/2500000 : ℚ) : ℝ) := by
    have h := (log_br_941).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 13521907/20000000) (δ := 317391/10000000000) 1269 691
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_942 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (942 : ℕ) / 2)) - ((-1215149/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17120013/5000000 : ℚ) : ℝ) ≤ Real.log (942 : ℕ) / 2 := by
    have h := (log_br_942).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (942 : ℕ) / 2 ≤ ((68480053/20000000 : ℚ) : ℝ) := by
    have h := (log_br_942).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9077817/12500000) (δ := 79321/2500000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_943 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (943 : ℕ) / 2)) - ((-6138281/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34245331/10000000 : ℚ) : ℝ) ≤ Real.log (943 : ℕ) / 2 := by
    have h := (log_br_943).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (943 : ℕ) / 2 ≤ ((68490663/20000000 : ℚ) : ℝ) := by
    have h := (log_br_943).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6974053/12500000) (δ := 317419/10000000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_944 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (944 : ℕ) / 2)) - ((116057/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68501261/20000000 : ℚ) : ℝ) ≤ Real.log (944 : ℕ) / 2 := by
    have h := (log_br_944).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (944 : ℕ) / 2 ≤ ((34250631/10000000 : ℚ) : ℝ) := by
    have h := (log_br_944).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -487247/1250000) (δ := 317319/10000000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_945 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (945 : ℕ) / 2)) - ((1578611/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68511849/20000000 : ℚ) : ℝ) ≤ Real.log (945 : ℕ) / 2 := by
    have h := (log_br_945).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (945 : ℕ) / 2 ≤ ((1370237/400000 : ℚ) : ℝ) := by
    have h := (log_br_945).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -4436909/20000000) (δ := 317319/10000000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_946 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (946 : ℕ) / 2)) - ((2441727/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2740897/800000 : ℚ) : ℝ) ≤ Real.log (946 : ℕ) / 2 := by
    have h := (log_br_946).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (946 : ℕ) / 2 ≤ ((34261213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_946).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -1081673/20000000) (δ := 317319/10000000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_947 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (947 : ℕ) / 2)) - ((1123367/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6853299/2000000 : ℚ) : ℝ) ≤ Real.log (947 : ℕ) / 2 := by
    have h := (log_br_947).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (947 : ℕ) / 2 ≤ ((68532991/20000000 : ℚ) : ℝ) := by
    have h := (log_br_947).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5675183/50000000) (δ := 317419/10000000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_948 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (948 : ℕ) / 2)) - ((2161613/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13708709/4000000 : ℚ) : ℝ) ≤ Real.log (948 : ℕ) / 2 := by
    have h := (log_br_948).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (948 : ℕ) / 2 ≤ ((34271773/10000000 : ℚ) : ℝ) := by
    have h := (log_br_948).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5618647/20000000) (δ := 317319/10000000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_949 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (949 : ℕ) / 2)) - ((-2200083/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68554087/20000000 : ℚ) : ℝ) ≤ Real.log (949 : ℕ) / 2 := by
    have h := (log_br_949).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (949 : ℕ) / 2 ≤ ((8569261/2500000 : ℚ) : ℝ) := by
    have h := (log_br_949).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 44815483/100000000) (δ := 39673/1250000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_950 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (950 : ℕ) / 2)) - ((-7771211/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68564619/20000000 : ℚ) : ℝ) ≤ Real.log (950 : ℕ) / 2 := by
    have h := (log_br_950).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (950 : ℕ) / 2 ≤ ((3428231/1000000 : ℚ) : ℝ) := by
    have h := (log_br_950).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 15380467/25000000) (δ := 39673/1250000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_951 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (951 : ℕ) / 2)) - ((-4999567/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((3428757/1000000 : ℚ) : ℝ) ≤ Real.log (951 : ℕ) / 2 := by
    have h := (log_br_951).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (951 : ℕ) / 2 ≤ ((68575141/20000000 : ℚ) : ℝ) := by
    have h := (log_br_951).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 19552701/25000000) (δ := 79321/2500000000) 1269 692
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_952 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (952 : ℕ) / 2)) - ((-3969199/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1371713/400000 : ℚ) : ℝ) ≤ Real.log (952 : ℕ) / 2 := by
    have h := (log_br_952).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (952 : ℕ) / 2 ≤ ((68585651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_952).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62197341/100000000) (δ := 79339/2500000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_953 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (953 : ℕ) / 2)) - ((-1241553/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68596149/20000000 : ℚ) : ℝ) ≤ Real.log (953 : ℕ) / 2 := by
    have h := (log_br_953).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (953 : ℕ) / 2 ≤ ((1371923/400000 : ℚ) : ℝ) := by
    have h := (log_br_953).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -45543303/100000000) (δ := 317447/10000000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_954 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (954 : ℕ) / 2)) - ((4026997/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17151659/5000000 : ℚ) : ℝ) ≤ Real.log (954 : ℕ) / 2 := by
    have h := (log_br_954).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (954 : ℕ) / 2 ≤ ((68606637/20000000 : ℚ) : ℝ) := by
    have h := (log_br_954).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -28908299/100000000) (δ := 317347/10000000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_955 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (955 : ℕ) / 2)) - ((4407973/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68617113/20000000 : ℚ) : ℝ) ≤ Real.log (955 : ℕ) / 2 := by
    have h := (log_br_955).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (955 : ℕ) / 2 ≤ ((34308557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_955).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -6144579/50000000) (δ := 317447/10000000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_956 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (956 : ℕ) / 2)) - ((1970317/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68627579/20000000 : ℚ) : ℝ) ≤ Real.log (956 : ℕ) / 2 := by
    have h := (log_br_956).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (956 : ℕ) / 2 ≤ ((3431379/1000000 : ℚ) : ℝ) := by
    have h := (log_br_956).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 862507/20000000) (δ := 39657/1250000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_957 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (957 : ℕ) / 2)) - ((6705787/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68638033/20000000 : ℚ) : ℝ) ≤ Real.log (957 : ℕ) / 2 := by
    have h := (log_br_957).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (957 : ℕ) / 2 ≤ ((34319017/10000000 : ℚ) : ℝ) := by
    have h := (log_br_957).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 2611899/12500000) (δ := 317447/10000000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_958 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (958 : ℕ) / 2)) - ((361269/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68648477/20000000 : ℚ) : ℝ) ≤ Real.log (958 : ℕ) / 2 := by
    have h := (log_br_958).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (958 : ℕ) / 2 ≤ ((34324239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_958).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 37461987/100000000) (δ := 317447/10000000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_959 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (959 : ℕ) / 2)) - ((-139019/250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((6865891/2000000 : ℚ) : ℝ) ≤ Real.log (959 : ℕ) / 2 := by
    have h := (log_br_959).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (959 : ℕ) / 2 ≤ ((68658911/20000000 : ℚ) : ℝ) := by
    have h := (log_br_959).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 27005667/50000000) (δ := 79339/2500000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_960 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (960 : ℕ) / 2)) - ((-593299/625000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17167333/5000000 : ℚ) : ℝ) ≤ Real.log (960 : ℕ) / 2 := by
    have h := (log_br_960).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (960 : ℕ) / 2 ≤ ((68669333/20000000 : ℚ) : ℝ) := by
    have h := (log_br_960).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 70543231/100000000) (δ := 317347/10000000000) 1269 693
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_961 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (961 : ℕ) / 2)) - ((-9424949/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((1073121/312500 : ℚ) : ℝ) ≤ Real.log (961 : ℕ) / 2 := by
    have h := (log_br_961).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (961 : ℕ) / 2 ≤ ((13735949/4000000 : ℚ) : ℝ) := by
    have h := (log_br_961).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -35010183/50000000) (δ := 79357/2500000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_962 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (962 : ℕ) / 2)) - ((-1079497/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2146567/625000 : ℚ) : ℝ) ≤ Real.log (962 : ℕ) / 2 := by
    have h := (log_br_962).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (962 : ℕ) / 2 ≤ ((13738029/4000000 : ℚ) : ℝ) := by
    have h := (log_br_962).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -26761683/50000000) (δ := 79357/2500000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_963 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (963 : ℕ) / 2)) - ((889893/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34350267/10000000 : ℚ) : ℝ) ≤ Real.log (963 : ℕ) / 2 := by
    have h := (log_br_963).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (963 : ℕ) / 2 ≤ ((13740107/4000000 : ℚ) : ℝ) := by
    have h := (log_br_963).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37042229/100000000) (δ := 12691/400000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_964 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (964 : ℕ) / 2)) - ((849843/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((268402/78125 : ℚ) : ℝ) ≤ Real.log (964 : ℕ) / 2 := by
    have h := (log_br_964).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (964 : ℕ) / 2 ≤ ((68710913/20000000 : ℚ) : ℝ) := by
    have h := (log_br_964).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10290063/50000000) (δ := 79357/2500000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_965 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (965 : ℕ) / 2)) - ((1232963/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68721281/20000000 : ℚ) : ℝ) ≤ Real.log (965 : ℕ) / 2 := by
    have h := (log_br_965).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (965 : ℕ) / 2 ≤ ((34360641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_965).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -41323/1000000) (δ := 19833/625000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_966 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (966 : ℕ) / 2)) - ((8814561/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34365819/10000000 : ℚ) : ℝ) ≤ Real.log (966 : ℕ) / 2 := by
    have h := (log_br_966).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (966 : ℕ) / 2 ≤ ((68731639/20000000 : ℚ) : ℝ) := by
    have h := (log_br_966).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 12296491/100000000) (δ := 12691/400000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_967 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (967 : ℕ) / 2)) - ((512533/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2148187/625000 : ℚ) : ℝ) ≤ Real.log (967 : ℕ) / 2 := by
    have h := (log_br_967).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (967 : ℕ) / 2 ≤ ((13748397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_967).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 14353917/50000000) (δ := 79357/2500000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_968 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (968 : ℕ) / 2)) - ((-1156123/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((214851/62500 : ℚ) : ℝ) ≤ Real.log (968 : ℕ) / 2 := by
    have h := (log_br_968).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (968 : ℕ) / 2 ≤ ((68752321/20000000 : ℚ) : ℝ) := by
    have h := (log_br_968).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 22551657/50000000) (δ := 79357/2500000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_969 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (969 : ℕ) / 2)) - ((-7761399/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34381323/10000000 : ℚ) : ℝ) ≤ Real.log (969 : ℕ) / 2 := by
    have h := (log_br_969).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (969 : ℕ) / 2 ≤ ((68762647/20000000 : ℚ) : ℝ) := by
    have h := (log_br_969).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 61482931/100000000) (δ := 12691/400000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_970 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (970 : ℕ) / 2)) - ((-4998061/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((429831/125000 : ℚ) : ℝ) ≤ Real.log (970 : ℕ) / 2 := by
    have h := (log_br_970).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (970 : ℕ) / 2 ≤ ((68772961/20000000 : ℚ) : ℝ) := by
    have h := (log_br_970).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 38921757/50000000) (δ := 79357/2500000000) 1269 694
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_971 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (971 : ℕ) / 2)) - ((-8104147/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2149477/625000 : ℚ) : ℝ) ≤ Real.log (971 : ℕ) / 2 := by
    have h := (log_br_971).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (971 : ℕ) / 2 ≤ ((13756653/4000000 : ℚ) : ℝ) := by
    have h := (log_br_971).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -62891399/100000000) (δ := 3173/100000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_972 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (972 : ℕ) / 2)) - ((-143793/500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34396779/10000000 : ℚ) : ℝ) ≤ Real.log (972 : ℕ) / 2 := by
    have h := (log_br_972).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (972 : ℕ) / 2 ≤ ((68793559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_972).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -23281271/50000000) (δ := 317403/10000000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_973 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (973 : ℕ) / 2)) - ((441147/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((53753/15625 : ℚ) : ℝ) ≤ Real.log (973 : ℕ) / 2 := by
    have h := (log_br_973).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (973 : ℕ) / 2 ≤ ((68803841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_973).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -30252719/100000000) (δ := 3173/100000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_974 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (974 : ℕ) / 2)) - ((4240819/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68814113/20000000 : ℚ) : ℝ) ≤ Real.log (974 : ℕ) / 2 := by
    have h := (log_br_974).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (974 : ℕ) / 2 ≤ ((34407057/10000000 : ℚ) : ℝ) := by
    have h := (log_br_974).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13957173/100000000) (δ := 317303/10000000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_975 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (975 : ℕ) / 2)) - ((2489249/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34412187/10000000 : ℚ) : ℝ) ≤ Real.log (975 : ℕ) / 2 := by
    have h := (log_br_975).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (975 : ℕ) / 2 ≤ ((110119/32000 : ℚ) : ℝ) := by
    have h := (log_br_975).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1159669/50000000) (δ := 317403/10000000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_976 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (976 : ℕ) / 2)) - ((3681537/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((550677/160000 : ℚ) : ℝ) ≤ Real.log (976 : ℕ) / 2 := by
    have h := (log_br_976).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (976 : ℕ) / 2 ≤ ((34417313/10000000 : ℚ) : ℝ) := by
    have h := (log_br_976).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18579987/100000000) (δ := 317303/10000000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_977 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (977 : ℕ) / 2)) - ((17687/100000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34422433/10000000 : ℚ) : ℝ) ≤ Real.log (977 : ℕ) / 2 := by
    have h := (log_br_977).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (977 : ℕ) / 2 ≤ ((68844867/20000000 : ℚ) : ℝ) := by
    have h := (log_br_977).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 34824773/100000000) (δ := 317403/10000000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_978 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (978 : ℕ) / 2)) - ((-567543/1250000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((8606887/2500000 : ℚ) : ℝ) ≤ Real.log (978 : ℕ) / 2 := by
    have h := (log_br_978).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (978 : ℕ) / 2 ≤ ((68855097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_978).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 51052111/100000000) (δ := 3173/100000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_979 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (979 : ℕ) / 2)) - ((-4499951/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17216329/5000000 : ℚ) : ℝ) ≤ Real.log (979 : ℕ) / 2 := by
    have h := (log_br_979).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (979 : ℕ) / 2 ≤ ((68865317/20000000 : ℚ) : ℝ) := by
    have h := (log_br_979).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 33631793/50000000) (δ := 3173/100000000) 1269 695
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_980 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (980 : ℕ) / 2)) - ((-1961429/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2755021/800000 : ℚ) : ℝ) ≤ Real.log (980 : ℕ) / 2 := by
    have h := (log_br_980).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (980 : ℕ) / 2 ≤ ((34437763/10000000 : ℚ) : ℝ) := by
    have h := (log_br_980).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -73622021/100000000) (δ := 39679/1250000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_981 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (981 : ℕ) / 2)) - ((-6645997/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17221431/5000000 : ℚ) : ℝ) ≤ Real.log (981 : ℕ) / 2 := by
    have h := (log_br_981).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (981 : ℕ) / 2 ≤ ((2755429/800000 : ℚ) : ℝ) := by
    have h := (log_br_981).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -57443857/100000000) (δ := 79333/2500000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_982 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (982 : ℕ) / 2)) - ((-803791/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68895913/20000000 : ℚ) : ℝ) ≤ Real.log (982 : ℕ) / 2 := by
    have h := (log_br_982).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (982 : ℕ) / 2 ≤ ((34447957/10000000 : ℚ) : ℝ) := by
    have h := (log_br_982).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10320389/25000000) (δ := 39679/1250000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_983 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (983 : ℕ) / 2)) - ((535693/1000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68906091/20000000 : ℚ) : ℝ) ≤ Real.log (983 : ℕ) / 2 := by
    have h := (log_br_983).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (983 : ℕ) / 2 ≤ ((17226523/5000000 : ℚ) : ℝ) := by
    have h := (log_br_983).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -25136703/100000000) (δ := 317271/10000000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_984 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (984 : ℕ) / 2)) - ((9357657/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34458129/10000000 : ℚ) : ℝ) ≤ Real.log (984 : ℕ) / 2 := by
    have h := (log_br_984).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (984 : ℕ) / 2 ≤ ((68916259/20000000 : ℚ) : ℝ) := by
    have h := (log_br_984).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -9009299/100000000) (δ := 317371/10000000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_985 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (985 : ℕ) / 2)) - ((4799497/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4307901/1250000 : ℚ) : ℝ) ≤ Real.log (985 : ℕ) / 2 := by
    have h := (log_br_985).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (985 : ℕ) / 2 ≤ ((68926417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_985).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 1775957/25000000) (δ := 79333/2500000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_986 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (986 : ℕ) / 2)) - ((2997259/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68936563/20000000 : ℚ) : ℝ) ≤ Real.log (986 : ℕ) / 2 := by
    have h := (log_br_986).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (986 : ℕ) / 2 ≤ ((17234141/5000000 : ℚ) : ℝ) := by
    have h := (log_br_986).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 23199507/100000000) (δ := 317271/10000000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_987 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (987 : ℕ) / 2)) - ((-1883/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((689467/200000 : ℚ) : ℝ) ≤ Real.log (987 : ℕ) / 2 := by
    have h := (log_br_987).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (987 : ℕ) / 2 ≤ ((68946701/20000000 : ℚ) : ℝ) := by
    have h := (log_br_987).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 39279323/100000000) (δ := 79333/2500000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_988 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (988 : ℕ) / 2)) - ((-74937/125000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34478413/10000000 : ℚ) : ℝ) ≤ Real.log (988 : ℕ) / 2 := by
    have h := (log_br_988).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (988 : ℕ) / 2 ≤ ((68956827/20000000 : ℚ) : ℝ) := by
    have h := (log_br_988).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 55341691/100000000) (δ := 317371/10000000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_989 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (989 : ℕ) / 2)) - ((-2398449/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68966943/20000000 : ℚ) : ℝ) ≤ Real.log (989 : ℕ) / 2 := by
    have h := (log_br_989).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (989 : ℕ) / 2 ≤ ((2155217/625000 : ℚ) : ℝ) := by
    have h := (log_br_989).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 35694891/50000000) (δ := 317271/10000000000) 1269 696
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_990 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (990 : ℕ) / 2)) - ((-1875137/2000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68977049/20000000 : ℚ) : ℝ) ≤ Real.log (990 : ℕ) / 2 := by
    have h := (log_br_990).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (990 : ℕ) / 2 ≤ ((1379541/400000 : ℚ) : ℝ) := by
    have h := (log_br_990).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -8707401/12500000) (δ := 317343/10000000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_991 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (991 : ℕ) / 2)) - ((-5438187/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((13797429/4000000 : ℚ) : ℝ) ≤ Real.log (991 : ℕ) / 2 := by
    have h := (log_br_991).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (991 : ℕ) / 2 ≤ ((34493573/10000000 : ℚ) : ℝ) := by
    have h := (log_br_991).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -13411107/25000000) (δ := 317343/10000000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_992 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (992 : ℕ) / 2)) - ((324651/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((68997231/20000000 : ℚ) : ℝ) ≤ Real.log (992 : ℕ) / 2 := by
    have h := (log_br_992).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (992 : ℕ) / 2 ≤ ((4312327/1250000 : ℚ) : ℝ) := by
    have h := (log_br_992).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -37645511/100000000) (δ := 3967/125000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_993 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (993 : ℕ) / 2)) - ((6474507/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((34503653/10000000 : ℚ) : ℝ) ≤ Real.log (993 : ℕ) / 2 := by
    have h := (log_br_993).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (993 : ℕ) / 2 ≤ ((69007307/20000000 : ℚ) : ℝ) := by
    have h := (log_br_993).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -10832021/50000000) (δ := 15863/500000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_994 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (994 : ℕ) / 2)) - ((9741489/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17254343/5000000 : ℚ) : ℝ) ≤ Real.log (994 : ℕ) / 2 := by
    have h := (log_br_994).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (994 : ℕ) / 2 ≤ ((69017373/20000000 : ℚ) : ℝ) := by
    have h := (log_br_994).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -5696849/100000000) (δ := 317443/10000000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_995 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (995 : ℕ) / 2)) - ((9170747/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69027427/20000000 : ℚ) : ℝ) ≤ Real.log (995 : ℕ) / 2 := by
    have h := (log_br_995).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (995 : ℕ) / 2 ≤ ((17256857/5000000 : ℚ) : ℝ) := by
    have h := (log_br_995).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 5126447/50000000) (δ := 3967/125000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_996 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (996 : ℕ) / 2)) - ((4997631/10000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((2157421/625000 : ℚ) : ℝ) ≤ Real.log (996 : ℕ) / 2 := by
    have h := (log_br_996).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (996 : ℕ) / 2 ≤ ((69037473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_996).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 3273347/12500000) (δ := 317443/10000000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_997 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (997 : ℕ) / 2)) - ((-565763/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69047507/20000000 : ℚ) : ℝ) ≤ Real.log (997 : ℕ) / 2 := by
    have h := (log_br_997).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (997 : ℕ) / 2 ≤ ((17261877/5000000 : ℚ) : ℝ) := by
    have h := (log_br_997).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 21052397/50000000) (δ := 3967/125000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_998 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (998 : ℕ) / 2)) - ((-3406297/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((17264383/5000000 : ℚ) : ℝ) ≤ Real.log (998 : ℕ) / 2 := by
    have h := (log_br_998).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (998 : ℕ) / 2 ≤ ((69057533/20000000 : ℚ) : ℝ) := by
    have h := (log_br_998).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 58006951/100000000) (δ := 317443/10000000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_999 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (999 : ℕ) / 2)) - ((-2456943/2500000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((69067547/20000000 : ℚ) : ℝ) ≤ Real.log (999 : ℕ) / 2 := by
    have h := (log_br_999).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (999 : ℕ) / 2 ≤ ((17266887/5000000 : ℚ) : ℝ) := by
    have h := (log_br_999).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := 18473311/25000000) (δ := 3967/125000000) 1269 697
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos1269o2_br_1000 :
    |Real.cos (((1269 : ℕ) : ℝ) * (Real.log (1000 : ℕ) / 2)) - ((-4504507/5000000 : ℚ) : ℝ)|
      ≤ ((1/10000 : ℚ) : ℝ) := by
  have hlo : ((4317347/1250000 : ℚ) : ℝ) ≤ Real.log (1000 : ℕ) / 2 := by
    have h := (log_br_1000).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log (1000 : ℕ) / 2 ≤ ((69077553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_1000).2
    push_cast at h ⊢
    linarith
  exact cosMul_eval (r := -67315957/100000000) (δ := 63463/2000000000) 1269 698
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos1269o2_br_1000
end AxiomAudit
