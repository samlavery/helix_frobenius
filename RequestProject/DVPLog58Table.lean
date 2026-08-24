import RequestProject.DVPLogBracket

/-!
# The `log n` bracket table, `n = 2..100`

Ninety-nine seven-decimal log enclosures through the packaged certificate
`log_bracket` (order-9 `expTaylor` kernel checks; every bracket verified
against exact rational arithmetic before statement).  Instruments for the
`t = 58` segment certificate: the angles `58·log n` of the cosine table.
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_2 :
    ((6931471/10000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ)
      ∧ Real.log (2 : ℕ) ≤ ((433217/625000 : ℚ) : ℝ) :=
  log_bracket 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3 :
    ((5493061/5000000 : ℚ) : ℝ) ≤ Real.log (3 : ℕ)
      ∧ Real.log (3 : ℕ) ≤ ((10986123/10000000 : ℚ) : ℝ) :=
  log_bracket 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_4 :
    ((13862943/10000000 : ℚ) : ℝ) ≤ Real.log (4 : ℕ)
      ∧ Real.log (4 : ℕ) ≤ ((433217/312500 : ℚ) : ℝ) :=
  log_bracket 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_5 :
    ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log (5 : ℕ)
      ∧ Real.log (5 : ℕ) ≤ ((804719/500000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_6 :
    ((8958797/5000000 : ℚ) : ℝ) ≤ Real.log (6 : ℕ)
      ∧ Real.log (6 : ℕ) ≤ ((3583519/2000000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_7 :
    ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log (7 : ℕ)
      ∧ Real.log (7 : ℕ) ≤ ((9729551/5000000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_8 :
    ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log (8 : ℕ)
      ∧ Real.log (8 : ℕ) ≤ ((1299651/625000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_9 :
    ((4394449/2000000 : ℚ) : ℝ) ≤ Real.log (9 : ℕ)
      ∧ Real.log (9 : ℕ) ≤ ((10986123/5000000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_10 :
    ((460517/200000 : ℚ) : ℝ) ≤ Real.log (10 : ℕ)
      ∧ Real.log (10 : ℕ) ≤ ((23025851/10000000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_11 :
    ((2997369/1250000 : ℚ) : ℝ) ≤ Real.log (11 : ℕ)
      ∧ Real.log (11 : ℕ) ≤ ((23978953/10000000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_12 :
    ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log (12 : ℕ)
      ∧ Real.log (12 : ℕ) ≤ ((24849067/10000000 : ℚ) : ℝ) :=
  log_bracket 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_13 :
    ((25649493/10000000 : ℚ) : ℝ) ≤ Real.log (13 : ℕ)
      ∧ Real.log (13 : ℕ) ≤ ((12824747/5000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_14 :
    ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log (14 : ℕ)
      ∧ Real.log (14 : ℕ) ≤ ((13195287/5000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_15 :
    ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log (15 : ℕ)
      ∧ Real.log (15 : ℕ) ≤ ((27080503/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_16 :
    ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log (16 : ℕ)
      ∧ Real.log (16 : ℕ) ≤ ((433217/156250 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_17 :
    ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log (17 : ℕ)
      ∧ Real.log (17 : ℕ) ≤ ((14166067/5000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_18 :
    ((28903717/10000000 : ℚ) : ℝ) ≤ Real.log (18 : ℕ)
      ∧ Real.log (18 : ℕ) ≤ ((14451859/5000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_19 :
    ((29444389/10000000 : ℚ) : ℝ) ≤ Real.log (19 : ℕ)
      ∧ Real.log (19 : ℕ) ≤ ((2944439/1000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_20 :
    ((14978661/5000000 : ℚ) : ℝ) ≤ Real.log (20 : ℕ)
      ∧ Real.log (20 : ℕ) ≤ ((29957323/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_21 :
    ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log (21 : ℕ)
      ∧ Real.log (21 : ℕ) ≤ ((1217809/400000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_22 :
    ((3863803/1250000 : ℚ) : ℝ) ≤ Real.log (22 : ℕ)
      ∧ Real.log (22 : ℕ) ≤ ((1236417/400000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_23 :
    ((15677471/5000000 : ℚ) : ℝ) ≤ Real.log (23 : ℕ)
      ∧ Real.log (23 : ℕ) ≤ ((31354943/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_24 :
    ((15890269/5000000 : ℚ) : ℝ) ≤ Real.log (24 : ℕ)
      ∧ Real.log (24 : ℕ) ≤ ((31780539/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_25 :
    ((16094379/5000000 : ℚ) : ℝ) ≤ Real.log (25 : ℕ)
      ∧ Real.log (25 : ℕ) ≤ ((32188759/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_26 :
    ((6516193/2000000 : ℚ) : ℝ) ≤ Real.log (26 : ℕ)
      ∧ Real.log (26 : ℕ) ≤ ((16290483/5000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_27 :
    ((1029949/312500 : ℚ) : ℝ) ≤ Real.log (27 : ℕ)
      ∧ Real.log (27 : ℕ) ≤ ((32958369/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_28 :
    ((6664409/2000000 : ℚ) : ℝ) ≤ Real.log (28 : ℕ)
      ∧ Real.log (28 : ℕ) ≤ ((16661023/5000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_29 :
    ((16836479/5000000 : ℚ) : ℝ) ≤ Real.log (29 : ℕ)
      ∧ Real.log (29 : ℕ) ≤ ((33672959/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_30 :
    ((34011973/10000000 : ℚ) : ℝ) ≤ Real.log (30 : ℕ)
      ∧ Real.log (30 : ℕ) ≤ ((17005987/5000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_31 :
    ((1073121/312500 : ℚ) : ℝ) ≤ Real.log (31 : ℕ)
      ∧ Real.log (31 : ℕ) ≤ ((34339873/10000000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_32 :
    ((34657359/10000000 : ℚ) : ℝ) ≤ Real.log (32 : ℕ)
      ∧ Real.log (32 : ℕ) ≤ ((433217/125000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_33 :
    ((1398603/400000 : ℚ) : ℝ) ≤ Real.log (33 : ℕ)
      ∧ Real.log (33 : ℕ) ≤ ((8741269/2500000 : ℚ) : ℝ) :=
  log_bracket 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_34 :
    ((7052721/2000000 : ℚ) : ℝ) ≤ Real.log (34 : ℕ)
      ∧ Real.log (34 : ℕ) ≤ ((17631803/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_35 :
    ((888837/250000 : ℚ) : ℝ) ≤ Real.log (35 : ℕ)
      ∧ Real.log (35 : ℕ) ≤ ((35553481/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_36 :
    ((35835189/10000000 : ℚ) : ℝ) ≤ Real.log (36 : ℕ)
      ∧ Real.log (36 : ℕ) ≤ ((3583519/1000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_37 :
    ((36109179/10000000 : ℚ) : ℝ) ≤ Real.log (37 : ℕ)
      ∧ Real.log (37 : ℕ) ≤ ((1805459/500000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_38 :
    ((36375861/10000000 : ℚ) : ℝ) ≤ Real.log (38 : ℕ)
      ∧ Real.log (38 : ℕ) ≤ ((18187931/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_39 :
    ((1144863/312500 : ℚ) : ℝ) ≤ Real.log (39 : ℕ)
      ∧ Real.log (39 : ℕ) ≤ ((36635617/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_40 :
    ((18444397/5000000 : ℚ) : ℝ) ≤ Real.log (40 : ℕ)
      ∧ Real.log (40 : ℕ) ≤ ((7377759/2000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_41 :
    ((928393/250000 : ℚ) : ℝ) ≤ Real.log (41 : ℕ)
      ∧ Real.log (41 : ℕ) ≤ ((37135721/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_42 :
    ((4672087/1250000 : ℚ) : ℝ) ≤ Real.log (42 : ℕ)
      ∧ Real.log (42 : ℕ) ≤ ((37376697/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_43 :
    ((37612001/10000000 : ℚ) : ℝ) ≤ Real.log (43 : ℕ)
      ∧ Real.log (43 : ℕ) ≤ ((18806001/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_44 :
    ((4730237/1250000 : ℚ) : ℝ) ≤ Real.log (44 : ℕ)
      ∧ Real.log (44 : ℕ) ≤ ((37841897/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_45 :
    ((594791/156250 : ℚ) : ℝ) ≤ Real.log (45 : ℕ)
      ∧ Real.log (45 : ℕ) ≤ ((304533/80000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_46 :
    ((38286413/10000000 : ℚ) : ℝ) ≤ Real.log (46 : ℕ)
      ∧ Real.log (46 : ℕ) ≤ ((19143207/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_47 :
    ((9625369/2500000 : ℚ) : ℝ) ≤ Real.log (47 : ℕ)
      ∧ Real.log (47 : ℕ) ≤ ((38501477/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_48 :
    ((3871201/1000000 : ℚ) : ℝ) ≤ Real.log (48 : ℕ)
      ∧ Real.log (48 : ℕ) ≤ ((38712011/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_49 :
    ((19459101/5000000 : ℚ) : ℝ) ≤ Real.log (49 : ℕ)
      ∧ Real.log (49 : ℕ) ≤ ((38918203/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_50 :
    ((3912023/1000000 : ℚ) : ℝ) ≤ Real.log (50 : ℕ)
      ∧ Real.log (50 : ℕ) ≤ ((39120231/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_51 :
    ((2457391/625000 : ℚ) : ℝ) ≤ Real.log (51 : ℕ)
      ∧ Real.log (51 : ℕ) ≤ ((39318257/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_52 :
    ((39512437/10000000 : ℚ) : ℝ) ≤ Real.log (52 : ℕ)
      ∧ Real.log (52 : ℕ) ≤ ((19756219/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_53 :
    ((39702919/10000000 : ℚ) : ℝ) ≤ Real.log (53 : ℕ)
      ∧ Real.log (53 : ℕ) ≤ ((992573/250000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_54 :
    ((498623/125000 : ℚ) : ℝ) ≤ Real.log (54 : ℕ)
      ∧ Real.log (54 : ℕ) ≤ ((39889841/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_55 :
    ((40073331/10000000 : ℚ) : ℝ) ≤ Real.log (55 : ℕ)
      ∧ Real.log (55 : ℕ) ≤ ((10018333/2500000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_56 :
    ((10063379/2500000 : ℚ) : ℝ) ≤ Real.log (56 : ℕ)
      ∧ Real.log (56 : ℕ) ≤ ((40253517/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_57 :
    ((2526907/625000 : ℚ) : ℝ) ≤ Real.log (57 : ℕ)
      ∧ Real.log (57 : ℕ) ≤ ((40430513/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_58 :
    ((4060443/1000000 : ℚ) : ℝ) ≤ Real.log (58 : ℕ)
      ∧ Real.log (58 : ℕ) ≤ ((40604431/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_59 :
    ((20387687/5000000 : ℚ) : ℝ) ≤ Real.log (59 : ℕ)
      ∧ Real.log (59 : ℕ) ≤ ((326203/80000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_60 :
    ((8188689/2000000 : ℚ) : ℝ) ≤ Real.log (60 : ℕ)
      ∧ Real.log (60 : ℕ) ≤ ((20471723/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_61 :
    ((20554369/5000000 : ℚ) : ℝ) ≤ Real.log (61 : ℕ)
      ∧ Real.log (61 : ℕ) ≤ ((41108739/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_62 :
    ((41271343/10000000 : ℚ) : ℝ) ≤ Real.log (62 : ℕ)
      ∧ Real.log (62 : ℕ) ≤ ((2579459/625000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_63 :
    ((41431347/10000000 : ℚ) : ℝ) ≤ Real.log (63 : ℕ)
      ∧ Real.log (63 : ℕ) ≤ ((10357837/2500000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_64 :
    ((4158883/1000000 : ℚ) : ℝ) ≤ Real.log (64 : ℕ)
      ∧ Real.log (64 : ℕ) ≤ ((41588831/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_65 :
    ((326124/78125 : ℚ) : ℝ) ≤ Real.log (65 : ℕ)
      ∧ Real.log (65 : ℕ) ≤ ((41743873/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_66 :
    ((41896547/10000000 : ℚ) : ℝ) ≤ Real.log (66 : ℕ)
      ∧ Real.log (66 : ℕ) ≤ ((10474137/2500000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_67 :
    ((21023463/5000000 : ℚ) : ℝ) ≤ Real.log (67 : ℕ)
      ∧ Real.log (67 : ℕ) ≤ ((42046927/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_68 :
    ((42195077/10000000 : ℚ) : ℝ) ≤ Real.log (68 : ℕ)
      ∧ Real.log (68 : ℕ) ≤ ((21097539/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_69 :
    ((8468213/2000000 : ℚ) : ℝ) ≤ Real.log (69 : ℕ)
      ∧ Real.log (69 : ℕ) ≤ ((21170533/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_70 :
    ((5310619/1250000 : ℚ) : ℝ) ≤ Real.log (70 : ℕ)
      ∧ Real.log (70 : ℕ) ≤ ((42484953/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_71 :
    ((21313399/5000000 : ℚ) : ℝ) ≤ Real.log (71 : ℕ)
      ∧ Real.log (71 : ℕ) ≤ ((42626799/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_72 :
    ((42766661/10000000 : ℚ) : ℝ) ≤ Real.log (72 : ℕ)
      ∧ Real.log (72 : ℕ) ≤ ((21383331/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_73 :
    ((21452297/5000000 : ℚ) : ℝ) ≤ Real.log (73 : ℕ)
      ∧ Real.log (73 : ℕ) ≤ ((8580919/2000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_74 :
    ((860813/200000 : ℚ) : ℝ) ≤ Real.log (74 : ℕ)
      ∧ Real.log (74 : ℕ) ≤ ((43040651/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_75 :
    ((43174881/10000000 : ℚ) : ℝ) ≤ Real.log (75 : ℕ)
      ∧ Real.log (75 : ℕ) ≤ ((21587441/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_76 :
    ((43307333/10000000 : ℚ) : ℝ) ≤ Real.log (76 : ℕ)
      ∧ Real.log (76 : ℕ) ≤ ((21653667/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_77 :
    ((21719027/5000000 : ℚ) : ℝ) ≤ Real.log (77 : ℕ)
      ∧ Real.log (77 : ℕ) ≤ ((8687611/2000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_78 :
    ((2722943/625000 : ℚ) : ℝ) ≤ Real.log (78 : ℕ)
      ∧ Real.log (78 : ℕ) ≤ ((43567089/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_79 :
    ((21847239/5000000 : ℚ) : ℝ) ≤ Real.log (79 : ℕ)
      ∧ Real.log (79 : ℕ) ≤ ((43694479/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_80 :
    ((21910133/5000000 : ℚ) : ℝ) ≤ Real.log (80 : ℕ)
      ∧ Real.log (80 : ℕ) ≤ ((43820267/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_81 :
    ((43944491/10000000 : ℚ) : ℝ) ≤ Real.log (81 : ℕ)
      ∧ Real.log (81 : ℕ) ≤ ((10986123/2500000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_82 :
    ((5508399/1250000 : ℚ) : ℝ) ≤ Real.log (82 : ℕ)
      ∧ Real.log (82 : ℕ) ≤ ((44067193/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_83 :
    ((22094203/5000000 : ℚ) : ℝ) ≤ Real.log (83 : ℕ)
      ∧ Real.log (83 : ℕ) ≤ ((44188407/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_84 :
    ((44308167/10000000 : ℚ) : ℝ) ≤ Real.log (84 : ℕ)
      ∧ Real.log (84 : ℕ) ≤ ((44308169/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_85 :
    ((2776657/625000 : ℚ) : ℝ) ≤ Real.log (85 : ℕ)
      ∧ Real.log (85 : ℕ) ≤ ((44426513/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_86 :
    ((2783967/625000 : ℚ) : ℝ) ≤ Real.log (86 : ℕ)
      ∧ Real.log (86 : ℕ) ≤ ((44543473/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_87 :
    ((44659081/10000000 : ℚ) : ℝ) ≤ Real.log (87 : ℕ)
      ∧ Real.log (87 : ℕ) ≤ ((22329541/5000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_88 :
    ((5596671/1250000 : ℚ) : ℝ) ≤ Real.log (88 : ℕ)
      ∧ Real.log (88 : ℕ) ≤ ((44773369/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_89 :
    ((44886363/10000000 : ℚ) : ℝ) ≤ Real.log (89 : ℕ)
      ∧ Real.log (89 : ℕ) ≤ ((11221591/2500000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_90 :
    ((2812381/625000 : ℚ) : ℝ) ≤ Real.log (90 : ℕ)
      ∧ Real.log (90 : ℕ) ≤ ((44998097/10000000 : ℚ) : ℝ) :=
  log_bracket 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_91 :
    ((22554297/5000000 : ℚ) : ℝ) ≤ Real.log (91 : ℕ)
      ∧ Real.log (91 : ℕ) ≤ ((11277149/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_92 :
    ((9043577/2000000 : ℚ) : ℝ) ≤ Real.log (92 : ℕ)
      ∧ Real.log (92 : ℕ) ≤ ((22608943/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_93 :
    ((22662997/5000000 : ℚ) : ℝ) ≤ Real.log (93 : ℕ)
      ∧ Real.log (93 : ℕ) ≤ ((9065199/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_94 :
    ((45432947/10000000 : ℚ) : ℝ) ≤ Real.log (94 : ℕ)
      ∧ Real.log (94 : ℕ) ≤ ((11358237/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_95 :
    ((2846173/625000 : ℚ) : ℝ) ≤ Real.log (95 : ℕ)
      ∧ Real.log (95 : ℕ) ≤ ((45538769/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_96 :
    ((45643481/10000000 : ℚ) : ℝ) ≤ Real.log (96 : ℕ)
      ∧ Real.log (96 : ℕ) ≤ ((22821741/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_97 :
    ((45747109/10000000 : ℚ) : ℝ) ≤ Real.log (97 : ℕ)
      ∧ Real.log (97 : ℕ) ≤ ((4574711/1000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_98 :
    ((22924837/5000000 : ℚ) : ℝ) ≤ Real.log (98 : ℕ)
      ∧ Real.log (98 : ℕ) ≤ ((1833987/400000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_99 :
    ((22975599/5000000 : ℚ) : ℝ) ≤ Real.log (99 : ℕ)
      ∧ Real.log (99 : ℕ) ≤ ((45951199/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_100 :
    ((46051701/10000000 : ℚ) : ℝ) ≤ Real.log (100 : ℕ)
      ∧ Real.log (100 : ℕ) ≤ ((23025851/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_br_2
#print axioms CriticalLinePhasor.DVP.log_br_100
end AxiomAudit
