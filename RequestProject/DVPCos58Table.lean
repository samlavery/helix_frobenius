import RequestProject.DVPCos58Eval

/-!
# The cosine table at `t = 58`: `cos(58·log n)`, `n = 2..100`

Ninety-nine kernel-certified enclosures `|cos(58·log n) − v_n| ≤ 1/25000`
through `cos58_eval`, off the `DVPLog58Table` brackets.  These are the
STATION-FREE data of the segment certificate: at fixed `t = 58` the
σ-dependence of `Re ζ` enters only through monotone weights, so this one
table serves every `σ ∈ [1/2, 2]` at once.
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem cos58_br_2 :
    |Real.cos (58 * Real.log (2 : ℕ)) - ((-200797/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 6258561/10000000) (δ := 223/50000000) 6
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_3 :
    |Real.cos (58 * Real.log (3 : ℕ)) - ((631229/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 2219149/10000000) (δ := 509/100000000) 10
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_4 :
    |Real.cos (58 * Real.log (4 : ℕ)) - ((290223/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -3190841/10000000) (δ := 321/100000000) 13
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_5 :
    |Real.cos (58 * Real.log (5 : ℕ)) - ((9708/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -281369/1250000) (δ := 521/100000000) 15
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_6 :
    |Real.cos (58 * Real.log (6 : ℕ)) - ((-484519/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -7230253/10000000) (δ := 3/781250) 17
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_7 :
    |Real.cos (58 * Real.log (7 : ℕ)) - ((48631/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -4581/78125) (δ := 329/100000000) 18
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_8 :
    |Real.cos (58 * Real.log (8 : ℕ)) - ((16849/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 3067721/10000000) (δ := 179/50000000) 19
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_9 :
    |Real.cos (58 * Real.log (9 : ℕ)) - ((-2031/10000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 2219149/5000000) (δ := 109/25000000) 20
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_10 :
    |Real.cos (58 * Real.log (10 : ℕ)) - ((-16121/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 4007609/10000000) (δ := 507/100000000) 21
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_11 :
    |Real.cos (58 * Real.log (11 : ℕ)) - ((330799/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1059811/5000000) (δ := 397/100000000) 22
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_12 :
    |Real.cos (58 * Real.log (12 : ℕ)) - ((925411/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -971691/10000000) (δ := 59/20000000) 23
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_13 :
    |Real.cos (58 * Real.log (13 : ℕ)) - ((-442683/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -2536731/5000000) (δ := 319/100000000) 24
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_14 :
    |Real.cos (58 * Real.log (14 : ℕ)) - ((-642749/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 2836097/5000000) (δ := 53/12500000) 24
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_15 :
    |Real.cos (58 * Real.log (15 : ℕ)) - ((999919/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -31803/10000000) (δ := 297/50000000) 25
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_16 :
    |Real.cos (58 * Real.log (16 : ℕ)) - ((-831541/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -6381681/10000000) (δ := 483/100000000) 26
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_17 :
    |Real.cos (58 * Real.log (17 : ℕ)) - ((142651/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 2408889/10000000) (δ := 363/100000000) 26
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_18 :
    |Real.cos (58 * Real.log (18 : ℕ)) - ((-420181/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -156597/312500) (δ := 311/100000000) 27
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_19 :
    |Real.cos (58 * Real.log (19 : ℕ)) - ((425341/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 2828643/10000000) (δ := 431/100000000) 27
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_20 :
    |Real.cos (58 * Real.log (20 : ℕ)) - ((-569519/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -42514/78125) (δ := 211/50000000) 28
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_21 :
    |Real.cos (58 * Real.log (21 : ℕ)) - ((198549/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1632781/10000000) (δ := 401/100000000) 28
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_22 :
    |Real.cos (58 * Real.log (22 : ℕ)) - ((-978097/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -366489/500000) (δ := 311/100000000) 29
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_23 :
    |Real.cos (58 * Real.log (23 : ℕ)) - ((469047/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -442137/5000000) (δ := 511/100000000) 29
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_24 :
    |Real.cos (58 * Real.log (24 : ℕ)) - ((-517521/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 528687/1000000) (δ := 431/100000000) 29
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_25 :
    |Real.cos (58 * Real.log (25 : ℕ)) - ((-28493/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -281369/625000) (δ := 23/5000000) 30
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_26 :
    |Real.cos (58 * Real.log (26 : ℕ)) - ((222433/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1185099/10000000) (δ := 1/250000) 30
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_27 :
    |Real.cos (58 * Real.log (27 : ℕ)) - ((-443817/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 6657447/10000000) (δ := 363/100000000) 30
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_28 :
    |Real.cos (58 * Real.log (28 : ℕ)) - ((59877/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -472151/1250000) (δ := 549/100000000) 31
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_29 :
    |Real.cos (58 * Real.log (29 : ℕ)) - ((432809/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 655517/5000000) (δ := 409/100000000) 31
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_30 :
    |Real.cos (58 * Real.log (30 : ℕ)) - ((-159109/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 6226759/10000000) (δ := 237/50000000) 31
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_31 :
    |Real.cos (58 * Real.log (31 : ℕ)) - ((-314449/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -118167/250000) (δ := 559/100000000) 32
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_32 :
    |Real.cos (58 * Real.log (32 : ℕ)) - ((249697/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -123119/10000000) (δ := 579/100000000) 32
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_33 :
    |Real.cos (58 * Real.log (33 : ℕ)) - ((-2562/15625 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 4338771/10000000) (δ := 81/25000000) 32
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_34 :
    |Real.cos (58 * Real.log (34 : ℕ)) - ((-947527/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -55004/78125) (δ := 7/1562500) 33
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_35 :
    |Real.cos (58 * Real.log (35 : ℕ)) - ((211099/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -2837319/10000000) (δ := 71/20000000) 33
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_36 :
    |Real.cos (58 * Real.log (36 : ℕ)) - ((87807/100000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 623729/5000000) (δ := 23/6250000) 33
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_37 :
    |Real.cos (58 * Real.log (37 : ℕ)) - ((-494559/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 5220309/10000000) (δ := 33/6250000) 33
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_38 :
    |Real.cos (58 * Real.log (38 : ℕ)) - ((-44039/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -3310379/5000000) (δ := 173/50000000) 34
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_39 :
    |Real.cos (58 * Real.log (39 : ℕ)) - ((208013/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -2854313/10000000) (δ := 337/100000000) 34
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_40 :
    |Real.cos (58 * Real.log (40 : ℕ)) - ((29597/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 816769/10000000) (δ := 297/100000000) 34
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_41 :
    |Real.cos (58 * Real.log (41 : ℕ)) - ((-5843/31250 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 2198599/5000000) (δ := 183/50000000) 34
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_42 :
    |Real.cos (58 * Real.log (42 : ℕ)) - ((-62493/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -390831/500000) (δ := 243/50000000) 35
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_43 :
    |Real.cos (58 * Real.log (43 : ℕ)) - ((-94961/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -2202349/5000000) (δ := 253/50000000) 35
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_44 :
    |Real.cos (58 * Real.log (44 : ℕ)) - ((181919/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -535609/5000000) (δ := 203/50000000) 35
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_45 :
    |Real.cos (58 * Real.log (45 : ℕ)) - ((160261/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1093673/5000000) (δ := 497/100000000) 35
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_46 :
    |Real.cos (58 * Real.log (46 : ℕ)) - ((-547119/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 335893/625000) (δ := 557/100000000) 35
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_47 :
    |Real.cos (58 * Real.log (47 : ℕ)) - ((-483771/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -1803819/2500000) (δ := 149/25000000) 36
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_48 :
    |Real.cos (58 * Real.log (48 : ℕ)) - ((-94077/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -1040633/2500000) (δ := 139/25000000) 36
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_49 :
    |Real.cos (58 * Real.log (49 : ℕ)) - ((445989/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -234547/2000000) (δ := 547/100000000) 36
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_50 :
    |Real.cos (58 * Real.log (50 : ℕ)) - ((190781/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 878329/5000000) (δ := 139/25000000) 36
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_51 :
    |Real.cos (58 * Real.log (51 : ℕ)) - ((-276759/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 4628039/10000000) (δ := 99/25000000) 36
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_52 :
    |Real.cos (58 * Real.log (52 : ℕ)) - ((-986561/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 7443661/10000000) (δ := 31/6250000) 36
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_53 :
    |Real.cos (58 * Real.log (53 : ℕ)) - ((-589249/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -2751157/5000000) (δ := 21/4000000) 37
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_54 :
    |Real.cos (58 * Real.log (54 : ℕ)) - ((438577/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -558391/2000000) (δ := 69/20000000) 37
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_55 :
    |Real.cos (58 * Real.log (55 : ℕ)) - ((998621/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -13133/1000000) (δ := 229/50000000) 37
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_56 :
    |Real.cos (58 * Real.log (56 : ℕ)) - ((546563/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1240677/5000000) (δ := 259/50000000) 37
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_57 :
    |Real.cos (58 * Real.log (57 : ℕ)) - ((-433453/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 315487/625000) (δ := 179/50000000) 37
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_58 :
    |Real.cos (58 * Real.log (58 : ℕ)) - ((-993537/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1513919/2000000) (δ := 109/20000000) 37
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_59 :
    |Real.cos (58 * Real.log (59 : ℕ)) - ((-127781/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -226387/400000) (δ := 167/50000000) 38
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_60 :
    |Real.cos (58 * Real.log (60 : ℕ)) - ((278027/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -3222643/10000000) (δ := 349/100000000) 38
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_61 :
    |Real.cos (58 * Real.log (61 : ℕ)) - ((472963/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -412947/5000000) (δ := 369/100000000) 38
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_62 :
    |Real.cos (58 * Real.log (62 : ℕ)) - ((204517/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1531881/10000000) (δ := 469/100000000) 38
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_63 :
    |Real.cos (58 * Real.log (63 : ℕ)) - ((30019/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 3851931/10000000) (δ := 217/50000000) 38
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_64 :
    |Real.cos (58 * Real.log (64 : ℕ)) - ((-96611/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 3067721/5000000) (δ := 449/100000000) 38
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_65 :
    |Real.cos (58 * Real.log (65 : ℕ)) - ((-61103/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -3662207/5000000) (δ := 19/5000000) 39
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_66 :
    |Real.cos (58 * Real.log (66 : ℕ)) - ((-91193/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -511063/1000000) (δ := 343/100000000) 39
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_67 :
    |Real.cos (58 * Real.log (67 : ℕ)) - ((388259/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -1465069/5000000) (δ := 483/100000000) 39
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_68 :
    |Real.cos (58 * Real.log (68 : ℕ)) - ((475741/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -781951/10000000) (δ := 583/100000000) 39
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_69 :
    |Real.cos (58 * Real.log (69 : ℕ)) - ((860803/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 10679/80000) (δ := 583/100000000) 39
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_70 :
    |Real.cos (58 * Real.log (70 : ℕ)) - ((100461/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1710621/5000000) (δ := 363/100000000) 39
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_71 :
    |Real.cos (58 * Real.log (71 : ℕ)) - ((-72671/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 2739007/5000000) (δ := 21/5000000) 39
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_72 :
    |Real.cos (58 * Real.log (72 : ℕ)) - ((-990329/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 7506019/10000000) (δ := 503/100000000) 39
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_73 :
    |Real.cos (58 * Real.log (73 : ℕ)) - ((-197371/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -775239/1250000) (δ := 353/100000000) 40
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_74 :
    |Real.cos (58 * Real.log (74 : ℕ)) - ((-120547/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -4229093/10000000) (δ := 51/10000000) 40
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_75 :
    |Real.cos (58 * Real.log (75 : ℕ)) - ((305647/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -456551/2000000) (δ := 533/100000000) 40
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_76 :
    |Real.cos (58 * Real.log (76 : ℕ)) - ((989523/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -362197/10000000) (δ := 373/100000000) 40
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_77 :
    |Real.cos (58 * Real.log (77 : ℕ)) - ((102219/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 306651/2000000) (δ := 473/100000000) 40
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_78 :
    |Real.cos (58 * Real.log (78 : ℕ)) - ((25947/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 3404249/10000000) (δ := 433/100000000) 40
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_79 :
    |Real.cos (58 * Real.log (79 : ℕ)) - ((-126333/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 5251407/10000000) (δ := 313/100000000) 40
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_80 :
    |Real.cos (58 * Real.log (80 : ℕ)) - ((-951887/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 7075331/10000000) (δ := 393/100000000) 40
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_81 :
    |Real.cos (58 * Real.log (81 : ℕ)) - ((-917501/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -6831367/10000000) (δ := 301/100000000) 41
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_82 :
    |Real.cos (58 * Real.log (82 : ℕ)) - ((-217521/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -1263051/2500000) (δ := 171/50000000) 41
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_83 :
    |Real.cos (58 * Real.log (83 : ℕ)) - ((50053/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -1647303/5000000) (δ := 271/50000000) 41
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_84 :
    |Real.cos (58 * Real.log (84 : ℕ)) - ((812001/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -1558059/10000000) (δ := 311/50000000) 41
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_85 :
    |Real.cos (58 * Real.log (85 : ℕ)) - ((199601/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 78969/5000000) (δ := 321/100000000) 41
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_86 :
    |Real.cos (58 * Real.log (86 : ℕ)) - ((368713/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1853863/10000000) (δ := 521/100000000) 41
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_87 :
    |Real.cos (58 * Real.log (87 : ℕ)) - ((79029/500000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 3530183/10000000) (δ := 241/50000000) 41
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_88 :
    |Real.cos (58 * Real.log (88 : ℕ)) - ((-30191/62500 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 324209/625000) (δ := 251/50000000) 41
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_89 :
    |Real.cos (58 * Real.log (89 : ℕ)) - ((-916609/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 6825779/10000000) (δ := 381/100000000) 41
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_90 :
    |Real.cos (58 * Real.log (90 : ℕ)) - ((-972101/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -907757/1250000) (δ := 93/25000000) 42
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_91 :
    |Real.cos (58 * Real.log (91 : ℕ)) - ((-79869/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -5659829/10000000) (δ := 153/25000000) 42
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_92 :
    |Real.cos (58 * Real.log (92 : ℕ)) - ((-11843/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -2037557/5000000) (δ := 27/6250000) 42
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_93 :
    |Real.cos (58 * Real.log (93 : ℕ)) - ((107553/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -2507531/10000000) (δ := 133/25000000) 42
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_94 :
    |Real.cos (58 * Real.log (94 : ℕ)) - ((185533/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -478357/5000000) (δ := 59/12500000) 42
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_95 :
    |Real.cos (58 * Real.log (95 : ℕ)) - ((48671/50000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 144423/2500000) (δ := 133/25000000) 42
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_96 :
    |Real.cos (58 * Real.log (96 : ℕ)) - ((167161/250000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 209603/1000000) (δ := 2/390625) 42
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_97 :
    |Real.cos (58 * Real.log (97 : ℕ)) - ((26193/200000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 1799317/5000000) (δ := 27/6250000) 42
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_98 :
    |Real.cos (58 * Real.log (98 : ℕ)) - ((-55889/125000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 5085827/10000000) (δ := 113/25000000) 42
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_99 :
    |Real.cos (58 * Real.log (99 : ℕ)) - ((-868601/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := 6557921/10000000) (δ := 73/25000000) 42
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem cos58_br_100 :
    |Real.cos (58 * Real.log (100 : ℕ)) - ((-997921/1000000 : ℚ) : ℝ)|
      ≤ ((1/25000 : ℚ) : ℝ) :=
  cos58_eval (r := -961593/1250000) (δ := 241/50000000) 43
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.cos58_br_2
#print axioms CriticalLinePhasor.DVP.cos58_br_100
end AxiomAudit
