import RequestProject.DVPCosSinEval

/-!
# The cosine table at `t = 74` (rung-74)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos74_br_2 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (2 : ℕ)) - ((517039/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1284261/5000000) (δ := 587/100000000) 74 8
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_3 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (3 : ℕ)) - ((28973/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3841/40000) (δ := 621/100000000) 74 13
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_4 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (4 : ℕ)) - ((-232671/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1284261/2500000) (δ := 433/100000000) 74 16
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_5 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (5 : ℕ)) - ((960469/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -705289/10000000) (δ := 339/50000000) 74 19
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_6 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (6 : ℕ)) - ((160023/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1608273/10000000) (δ := 507/100000000) 74 21
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_7 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (7 : ℕ)) - ((217461/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -644889/5000000) (δ := 79/20000000) 74 23
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_8 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (8 : ℕ)) - ((-499119/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3852783/5000000) (δ := 29/6250000) 74 24
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_9 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (9 : ℕ)) - ((719163/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1920499/10000000) (δ := 27/5000000) 74 26
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_10 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (10 : ℕ)) - ((734889/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1863233/10000000) (δ := 651/100000000) 74 27
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_11 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (11 : ℕ)) - ((27853/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3787653/10000000) (δ := 251/50000000) 74 28
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_12 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (12 : ℕ)) - ((-19951/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 835359/2000000) (δ := 391/100000000) 74 29
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_13 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (13 : ℕ)) - ((12859/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3276733/10000000) (δ := 423/100000000) 74 30
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_14 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (14 : ℕ)) - ((218003/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 159843/1250000) (δ := 549/100000000) 74 31
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_15 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (15 : ℕ)) - ((393083/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -832769/5000000) (δ := 759/100000000) 74 32
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_16 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (16 : ℕ)) - ((-566913/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -43471/80000) (δ := 19/3125000) 74 33
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_17 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (17 : ℕ)) - ((-84459/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 72271/125000) (δ := 7/1562500) 74 33
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_18 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (18 : ℕ)) - ((966593/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 81003/1250000) (δ := 213/50000000) 74 34
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_19 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (19 : ℕ)) - ((-8739/20000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -158047/312500) (δ := 557/100000000) 74 35
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_20 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (20 : ℕ)) - ((-200537/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1107939/2500000) (δ := 537/100000000) 74 35
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_21 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (21 : ℕ)) - ((310801/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2250027/10000000) (δ := 119/25000000) 74 36
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_22 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (22 : ℕ)) - ((-825831/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 397261/625000) (δ := 387/100000000) 74 36
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_23 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (23 : ℕ)) - ((56243/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1128211/10000000) (δ := 1/160000) 74 37
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_24 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (24 : ℕ)) - ((-90327/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6745317/10000000) (δ := 109/20000000) 74 37
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_25 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (25 : ℕ)) - ((169/200 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1410577/10000000) (δ := 287/50000000) 74 38
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_26 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (26 : ℕ)) - ((-347099/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1169051/2000000) (δ := 237/50000000) 74 38
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_27 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (27 : ℕ)) - ((101597/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -720187/2500000) (δ := 23/5000000) 74 39
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_28 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (28 : ℕ)) - ((6377/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1923633/5000000) (δ := 703/100000000) 74 39
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_29 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (29 : ℕ)) - ((-545281/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -5368803/10000000) (δ := 553/100000000) 74 40
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_30 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (30 : ℕ)) - ((233869/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 112873/1250000) (δ := 57/10000000) 74 40
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_31 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (31 : ℕ)) - ((-93801/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3484551/5000000) (δ := 713/100000000) 74 40
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_32 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (32 : ℕ)) - ((412007/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -358169/1250000) (δ := 361/50000000) 74 41
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_33 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (33 : ℕ)) - ((42579/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 706851/2500000) (δ := 421/100000000) 74 41
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_34 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (34 : ℕ)) - ((-490183/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7357761/10000000) (δ := 591/100000000) 74 42
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_35 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (35 : ℕ)) - ((698121/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -997533/5000000) (δ := 113/25000000) 74 42
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_36 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (36 : ℕ)) - ((17523/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1608273/5000000) (δ := 471/100000000) 74 42
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_37 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (37 : ℕ)) - ((-19703/20000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7422607/10000000) (δ := 661/100000000) 74 43
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_38 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (38 : ℕ)) - ((272003/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2488981/10000000) (δ := 221/50000000) 74 43
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_39 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (39 : ℕ)) - ((600561/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 579121/2500000) (δ := 401/100000000) 74 43
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_40 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (40 : ℕ)) - ((-47113/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3500139/5000000) (δ := 191/50000000) 74 43
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_41 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (41 : ℕ)) - ((-42461/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -129361/312500) (δ := 473/100000000) 74 44
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_42 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (42 : ℕ)) - ((123987/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 63699/2000000) (δ := 63/10000000) 74 44
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_43 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (43 : ℕ)) - ((-146737/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4671637/10000000) (δ := 13/2000000) 74 44
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_44 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (44 : ℕ)) - ((-909679/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1356653/2000000) (δ := 499/100000000) 74 45
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_45 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (45 : ℕ)) - ((248649/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2625787/10000000) (δ := 161/25000000) 74 45
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_46 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (46 : ℕ)) - ((41929/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1440311/10000000) (δ := 11/1562500) 74 45
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_47 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (47 : ℕ)) - ((-140497/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5418959/10000000) (δ := 739/100000000) 74 45
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_48 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (48 : ℕ)) - ((-166859/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1598531/2500000) (δ := 43/6250000) 74 46
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_49 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (49 : ℕ)) - ((64157/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -644889/2500000) (δ := 139/20000000) 74 46
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_50 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (50 : ℕ)) - ((894637/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 231589/2000000) (δ := 91/12500000) 74 46
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_51 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (51 : ℕ)) - ((-21887/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4821431/10000000) (δ := 33/6250000) 74 46
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_52 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (52 : ℕ)) - ((-195007/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3647093/5000000) (δ := 309/50000000) 74 47
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_53 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (53 : ℕ)) - ((62647/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -377027/1000000) (δ := 329/50000000) 74 47
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_54 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (54 : ℕ)) - ((992211/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -12489/400000) (δ := 199/50000000) 74 47
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_55 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (55 : ℕ)) - ((16573/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 616473/2000000) (δ := 121/20000000) 74 47
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_56 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (56 : ℕ)) - ((-419521/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6415789/10000000) (δ := 133/20000000) 74 47
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_57 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (57 : ℕ)) - ((-185543/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6017753/10000000) (δ := 119/25000000) 74 48
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_58 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (58 : ℕ)) - ((217791/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -70007/250000) (δ := 667/100000000) 74 48
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_59 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (59 : ℕ)) - ((247381/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 36219/1000000) (δ := 427/100000000) 74 48
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_60 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (60 : ℕ)) - ((181187/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3471507/10000000) (δ := 57/12500000) 74 48
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_61 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (61 : ℕ)) - ((-862897/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1632357/2500000) (δ := 119/25000000) 74 48
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_62 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (62 : ℕ)) - ((-78167/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6170339/10000000) (δ := 627/100000000) 74 49
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_63 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (63 : ℕ)) - ((11311/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -802569/2500000) (δ := 139/25000000) 74 49
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_64 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (64 : ℕ)) - ((3103/3125 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -29683/1000000) (δ := 607/100000000) 74 49
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_65 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (65 : ℕ)) - ((258019/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 642861/2500000) (δ := 487/100000000) 74 49
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_66 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (66 : ℕ)) - ((-69293/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5395927/10000000) (δ := 109/25000000) 74 49
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_67 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (67 : ℕ)) - ((-15494/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7530029/10000000) (δ := 303/50000000) 74 50
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_68 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (68 : ℕ)) - ((-169051/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2394619/5000000) (δ := 353/50000000) 74 50
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_69 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (69 : ℕ)) - ((670893/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2088461/10000000) (δ := 373/50000000) 74 50
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_70 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (70 : ℕ)) - ((973807/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 35841/625000) (δ := 223/50000000) 74 50
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_71 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (71 : ℕ)) - ((28763/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3197613/10000000) (δ := 537/100000000) 74 50
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_72 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (72 : ℕ)) - ((-67667/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1446267/2500000) (δ := 313/50000000) 74 50
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_73 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (73 : ℕ)) - ((-490703/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7371131/10000000) (δ := 19/4000000) 74 51
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_74 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (74 : ℕ)) - ((-90599/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -970817/2000000) (δ := 167/25000000) 74 51
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_75 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (75 : ℕ)) - ((1822/3125 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1185413/5000000) (δ := 131/20000000) 74 51
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_76 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (76 : ℕ)) - ((499747/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 79541/10000000) (δ := 91/20000000) 74 51
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_77 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (77 : ℕ)) - ((541017/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 624469/2500000) (δ := 119/20000000) 74 51
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_78 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (78 : ℕ)) - ((-46737/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2442503/5000000) (δ := 111/20000000) 74 51
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_79 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (79 : ℕ)) - ((-970161/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3620863/5000000) (δ := 97/25000000) 74 51
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_80 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (80 : ℕ)) - ((-96729/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6139163/10000000) (δ := 63/12500000) 74 52
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_81 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (81 : ℕ)) - ((34391/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3840997/10000000) (δ := 379/100000000) 74 52
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_82 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (82 : ℕ)) - ((404481/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -157103/1000000) (δ := 53/12500000) 74 52
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_83 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (83 : ℕ)) - ((120519/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 335711/5000000) (δ := 11/1562500) 74 52
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_84 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (84 : ℕ)) - ((80819/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2887017/10000000) (δ := 49/6250000) 74 52
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_85 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (85 : ℕ)) - ((-443733/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 634549/1250000) (δ := 399/100000000) 74 52
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_86 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (86 : ℕ)) - ((-970009/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7240159/10000000) (δ := 679/100000000) 74 52
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_87 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (87 : ℕ)) - ((-51229/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1582263/2500000) (δ := 633/100000000) 74 53
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_88 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (88 : ℕ)) - ((-114847/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4214743/10000000) (δ := 653/100000000) 74 53
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_89 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (89 : ℕ)) - ((330093/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -84973/400000) (δ := 51/10000000) 74 53
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_90 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (90 : ℕ)) - ((499869/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -11453/2000000) (δ := 49/10000000) 74 53
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_91 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (91 : ℕ)) - ((17511/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 397391/2000000) (δ := 77/10000000) 74 53
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_92 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (92 : ℕ)) - ((-32731/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4008833/10000000) (δ := 11/2000000) 74 53
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_93 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (93 : ℕ)) - ((-739781/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6008853/10000000) (δ := 69/10000000) 74 53
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_94 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (94 : ℕ)) - ((-39943/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3860241/5000000) (δ := 3/500000) 74 54
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_95 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (95 : ℕ)) - ((-670083/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -720349/1250000) (δ := 33/5000000) 74 54
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_96 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (96 : ℕ)) - ((1267/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1912801/5000000) (δ := 1/156250) 74 54
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_97 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (97 : ℕ)) - ((722493/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -954243/5000000) (δ := 7/1250000) 74 54
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_98 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (98 : ℕ)) - ((99999/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -11033/10000000) (δ := 29/5000000) 74 54
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_99 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (99 : ℕ)) - ((11466/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 373431/2000000) (δ := 403/100000000) 74 54
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos74_br_100 :
    |Real.cos (((74:ℕ):ℝ) * Real.log (100 : ℕ)) - ((20031/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3726467/10000000) (δ := 3/500000) 74 54
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos74_br_100
end AxiomAudit
