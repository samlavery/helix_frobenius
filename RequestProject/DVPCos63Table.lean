import RequestProject.DVPCosSinEval

/-!
# The cosine table at `t = 63`: `cos(63·log n)`, `n = 2..100`

Rung-63 of the channel extension: 99 kernel-certified enclosures
`|cos(63·log n) − v_n| ≤ 1/25000` through the parametric `cosMul_eval`,
off the height-independent `DVPLog58Table` brackets.
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos63_br_2 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (2 : ℕ)) - ((475549/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -392531/5000000) (δ := 507/100000000) 63 7
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_3 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (3 : ℕ)) - ((995247/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 243839/10000000) (δ := 539/100000000) 63 11
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_4 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (4 : ℕ)) - ((32367/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -392531/2500000) (δ := 191/50000000) 63 14
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_5 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (5 : ℕ)) - ((649687/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1079529/5000000) (δ := 59/10000000) 63 16
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_6 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (6 : ℕ)) - ((488329/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -541223/10000000) (δ := 207/50000000) 63 18
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_7 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (7 : ℕ)) - ((-199507/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7678417/10000000) (δ := 327/100000000) 63 20
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_8 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (8 : ℕ)) - ((36757/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1177593/5000000) (δ := 47/12500000) 63 21
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_9 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (9 : ℕ)) - ((490517/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 487679/10000000) (δ := 487/100000000) 63 22
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_10 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (10 : ℕ)) - ((426367/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 343499/2500000) (δ := 137/25000000) 63 23
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_11 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (11 : ℕ)) - ((240879/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 677387/10000000) (δ := 459/100000000) 63 24
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_12 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (12 : ℕ)) - ((862547/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -265257/2000000) (δ := 43/12500000) 63 25
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_13 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (13 : ℕ)) - ((-99439/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2213761/5000000) (δ := 33/10000000) 63 26
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_14 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (14 : ℕ)) - ((-242607/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1811121/2500000) (δ := 463/100000000) 63 26
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_15 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (15 : ℕ)) - ((57257/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1201449/5000000) (δ := 321/50000000) 63 27
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_16 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (16 : ℕ)) - ((38691/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -392531/1250000) (δ := 501/100000000) 63 28
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_17 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (17 : ℕ)) - ((-837371/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 640813/1000000) (δ := 361/100000000) 63 28
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_18 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (18 : ℕ)) - ((992933/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -297383/10000000) (δ := 181/50000000) 63 29
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_19 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (19 : ℕ)) - ((-494703/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -7489759/10000000) (δ := 493/100000000) 63 30
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_20 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (20 : ℕ)) - ((972381/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 117787/2000000) (δ := 463/100000000) 63 30
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_21 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (21 : ℕ)) - ((-985961/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3717289/5000000) (δ := 419/100000000) 63 31
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_22 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (22 : ℕ)) - ((999073/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -4307/400000) (δ := 167/50000000) 63 31
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_23 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (23 : ℕ)) - ((-463549/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6893477/10000000) (δ := 559/100000000) 63 31
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_24 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (24 : ℕ)) - ((166019/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2111347/10000000) (δ := 469/100000000) 63 32
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_25 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (25 : ℕ)) - ((-155813/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4318117/10000000) (δ := 509/100000000) 63 32
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_26 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (26 : ℕ)) - ((-491871/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -651573/1250000) (δ := 107/25000000) 63 33
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_27 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (27 : ℕ)) - ((191499/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 365759/5000000) (δ := 79/20000000) 63 33
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_28 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (28 : ℕ)) - ((-848409/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3229711/5000000) (δ := 147/25000000) 63 33
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_29 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (29 : ℕ)) - ((82041/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1860829/5000000) (δ := 447/100000000) 63 34
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_30 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (30 : ℕ)) - ((159563/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 404459/2500000) (δ := 31/6250000) 63 34
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_31 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (31 : ℕ)) - ((-909507/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6782233/10000000) (δ := 627/100000000) 63 34
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_32 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (32 : ℕ)) - ((21/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -392531/1000000) (δ := 313/50000000) 63 35
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_33 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (33 : ℕ)) - ((116609/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 460613/5000000) (δ := 367/100000000) 63 35
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_34 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (34 : ℕ)) - ((-156893/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1405767/2500000) (δ := 243/50000000) 63 35
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_35 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (35 : ℕ)) - ((-74343/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2759679/5000000) (δ := 387/100000000) 63 36
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_36 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (36 : ℕ)) - ((22693/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -216489/2000000) (δ := 99/25000000) 63 36
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_37 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (37 : ℕ)) - ((137043/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3232893/10000000) (δ := 9/1562500) 63 36
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_38 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (38 : ℕ)) - ((-197173/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3716571/5000000) (δ := 357/100000000) 63 36
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_39 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (39 : ℕ)) - ((-3203/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2091841/5000000) (δ := 71/20000000) 63 37
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_40 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (40 : ℕ)) - ((249231/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -196127/10000000) (δ := 169/50000000) 63 37
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_41 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (41 : ℕ)) - ((23369/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3692959/10000000) (δ := 199/50000000) 63 37
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_42 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (42 : ℕ)) - ((-989323/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7488323/10000000) (δ := 111/20000000) 63 37
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_43 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (43 : ℕ)) - ((-232491/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2256793/5000000) (δ := 267/50000000) 63 38
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_44 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (44 : ℕ)) - ((234229/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -892737/10000000) (δ := 53/12500000) 63 38
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_45 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (45 : ℕ)) - ((49001/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2646737/10000000) (δ := 529/100000000) 63 38
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_46 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (46 : ℕ)) - ((-765983/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 1221683/2000000) (δ := 579/100000000) 63 38
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_47 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (47 : ℕ)) - ((-792033/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6212321/10000000) (δ := 653/100000000) 63 39
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_48 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (48 : ℕ)) - ((25041/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2896409/10000000) (δ := 593/100000000) 63 39
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_49 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (49 : ℕ)) - ((990153/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 351129/10000000) (δ := 3/500000) 63 39
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_50 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (50 : ℕ)) - ((156923/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 706611/2000000) (δ := 633/100000000) 63 39
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_51 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (51 : ℕ)) - ((-886623/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 6651969/10000000) (δ := 453/100000000) 63 39
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_52 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (52 : ℕ)) - ((-736757/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2998823/5000000) (δ := 553/100000000) 63 40
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_53 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (53 : ℕ)) - ((363269/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -599511/2000000) (δ := 573/100000000) 63 40
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_54 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (54 : ℕ)) - ((999771/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6693/1250000) (δ := 363/100000000) 63 40
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_55 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (55 : ℕ)) - ((84503/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 567289/2000000) (δ := 1/200000) 63 40
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_56 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (56 : ℕ)) - ((-160853/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 141859/250000) (δ := 11/2000000) 63 40
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_57 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (57 : ℕ)) - ((-485283/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -45287/62500) (δ := 401/100000000) 63 41
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_58 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (58 : ℕ)) - ((-229819/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -28167/62500) (δ := 143/25000000) 63 41
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_59 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (59 : ℕ)) - ((748009/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1814347/10000000) (δ := 93/25000000) 63 41
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_60 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (60 : ℕ)) - ((94503/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 416387/5000000) (δ := 371/100000000) 63 41
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_61 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (61 : ℕ)) - ((97541/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3436139/10000000) (δ := 381/100000000) 63 41
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_62 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (62 : ℕ)) - ((-736629/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5997171/10000000) (δ := 511/100000000) 63 41
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_63 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (63 : ℕ)) - ((-193003/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3595369/5000000) (δ := 471/100000000) 63 42
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_64 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (64 : ℕ)) - ((-1233/4000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1177593/2500000) (δ := 2/390625) 63 42
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_65 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (65 : ℕ)) - ((9622/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -2268463/10000000) (δ := 103/25000000) 63 42
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_66 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (66 : ℕ)) - ((998517/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 34041/2500000) (δ := 391/100000000) 63 42
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_67 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (67 : ℕ)) - ((538743/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 250463/1000000) (δ := 521/100000000) 63 42
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_68 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (68 : ℕ)) - ((-178197/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2419003/5000000) (δ := 611/100000000) 63 42
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_69 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (69 : ℕ)) - ((-119899/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7137317/10000000) (δ := 611/100000000) 63 42
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_70 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (70 : ℕ)) - ((-40699/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -315221/500000) (δ := 371/100000000) 63 43
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_71 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (71 : ℕ)) - ((-14327/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -203517/500000) (δ := 241/50000000) 63 43
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_72 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (72 : ℕ)) - ((733729/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1867507/10000000) (δ := 521/100000000) 63 43
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_73 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (73 : ℕ)) - ((99257/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 304941/10000000) (δ := 391/100000000) 63 43
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_74 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (74 : ℕ)) - ((557743/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2447831/10000000) (δ := 281/50000000) 63 43
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_75 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (75 : ℕ)) - ((-50253/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4561957/10000000) (δ := 561/100000000) 63 43
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_76 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (76 : ℕ)) - ((-442951/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 83101/125000) (δ := 401/100000000) 63 43
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_77 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (77 : ℕ)) - ((-23559/25000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -700103/1000000) (δ := 1/200000) 63 44
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_78 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (78 : ℕ)) - ((-202373/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -621093/1250000) (δ := 3/625000) 63 44
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_79 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (79 : ℕ)) - ((376353/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -740587/2500000) (δ := 17/5000000) 63 44
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_80 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (80 : ℕ)) - ((184793/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -981189/10000000) (δ := 21/5000000) 63 44
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_81 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (81 : ℕ)) - ((184971/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 487679/5000000) (δ := 343/100000000) 63 44
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_82 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (82 : ℕ)) - ((198221/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2907897/10000000) (δ := 9/2500000) 63 44
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_83 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (83 : ℕ)) - ((-69707/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 4817011/10000000) (δ := 31/5000000) 63 44
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_84 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (84 : ℕ)) - ((-35837/40000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 3351631/5000000) (δ := 1/156250) 63 44
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_85 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (85 : ℕ)) - ((-479791/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -285631/400000) (δ := 81/25000000) 63 45
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_86 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (86 : ℕ)) - ((-521547/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -662331/1250000) (δ := 151/25000000) 63 45
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_87 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (87 : ℕ)) - ((11169/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3477819/10000000) (δ := 539/100000000) 63 45
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_88 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (88 : ℕ)) - ((391563/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -1677799/10000000) (δ := 549/100000000) 63 45
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_89 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (89 : ℕ)) - ((99917/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 101881/10000000) (δ := 217/50000000) 63 45
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_90 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (90 : ℕ)) - ((735311/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 465419/2500000) (δ := 111/25000000) 63 45
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_91 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (91 : ℕ)) - ((129621/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 144081/400000) (δ := 83/12500000) 63 45
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_92 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (92 : ℕ)) - ((-529953/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 5323353/10000000) (δ := 227/50000000) 63 45
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_93 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (93 : ℕ)) - ((-189133/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 7026073/10000000) (δ := 73/12500000) 63 45
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_94 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (94 : ℕ)) - ((-941871/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -6997383/10000000) (δ := 97/20000000) 63 46
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_95 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (95 : ℕ)) - ((-532443/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -53307/100000) (δ := 23/4000000) 63 46
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_96 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (96 : ℕ)) - ((1961/20000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -3681471/10000000) (δ := 109/20000000) 63 46
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_97 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (97 : ℕ)) - ((682417/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -512333/2500000) (δ := 93/20000000) 63 46
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_98 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (98 : ℕ)) - ((492487/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := -433933/10000000) (δ := 19/4000000) 63 46
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_99 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (99 : ℕ)) - ((893361/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 582533/5000000) (δ := 159/50000000) 63 46
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos63_br_100 :
    |Real.cos (((63:ℕ):ℝ) * Real.log (100 : ℕ)) - ((454311/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cosMul_eval (r := 2747993/10000000) (δ := 101/20000000) 63 46
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos63_br_2
#print axioms CriticalLinePhasor.DVP.cos63_br_100
end AxiomAudit
