import RequestProject.DVPLogBracket

/-!
# Sharp natural-log brackets 501-2000 (1e-8 width)

The shared `DVPLog1000Table` / `DVPLog2000Table` carry 1e-7 brackets, which is
ample for the ordinary stations.  A station at height `M` needs `M·(hi−lo) ≤ 2δ`
in `cosMulShift_eval`'s angle window, so the deep rungs (`M ≳ 2000`) need a
decade more.  These are the same brackets at 1e-8, matching `DVPLog4000Table`.
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_brs_501 :
    ((62166061/10000000 : ℚ) : ℝ) ≤ Real.log (501 : ℕ)
      ∧ Real.log (501 : ℕ) ≤ ((621660611/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_502 :
    ((621860011/100000000 : ℚ) : ℝ) ≤ Real.log (502 : ℕ)
      ∧ Real.log (502 : ℕ) ≤ ((621860013/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_503 :
    ((77757377/12500000 : ℚ) : ℝ) ≤ Real.log (503 : ℕ)
      ∧ Real.log (503 : ℕ) ≤ ((311029509/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_504 :
    ((311128813/50000000 : ℚ) : ℝ) ≤ Real.log (504 : ℕ)
      ∧ Real.log (504 : ℕ) ≤ ((622257627/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_505 :
    ((311227921/50000000 : ℚ) : ℝ) ≤ Real.log (505 : ℕ)
      ∧ Real.log (505 : ℕ) ≤ ((622455843/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_506 :
    ((311326833/50000000 : ℚ) : ℝ) ≤ Real.log (506 : ℕ)
      ∧ Real.log (506 : ℕ) ≤ ((622653667/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_507 :
    ((6228511/1000000 : ℚ) : ℝ) ≤ Real.log (507 : ℕ)
      ∧ Real.log (507 : ℕ) ≤ ((622851101/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_508 :
    ((38940509/6250000 : ℚ) : ℝ) ≤ Real.log (508 : ℕ)
      ∧ Real.log (508 : ℕ) ≤ ((124609629/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_509 :
    ((623244801/100000000 : ℚ) : ℝ) ≤ Real.log (509 : ℕ)
      ∧ Real.log (509 : ℕ) ≤ ((311622401/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_510 :
    ((38965067/6250000 : ℚ) : ℝ) ≤ Real.log (510 : ℕ)
      ∧ Real.log (510 : ℕ) ≤ ((623441073/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_511 :
    ((311818479/50000000 : ℚ) : ℝ) ≤ Real.log (511 : ℕ)
      ∧ Real.log (511 : ℕ) ≤ ((3897731/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_512 :
    ((311916231/50000000 : ℚ) : ℝ) ≤ Real.log (512 : ℕ)
      ∧ Real.log (512 : ℕ) ≤ ((623832463/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_513 :
    ((9750431/1562500 : ℚ) : ℝ) ≤ Real.log (513 : ℕ)
      ∧ Real.log (513 : ℕ) ≤ ((124805517/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_514 :
    ((312111163/50000000 : ℚ) : ℝ) ≤ Real.log (514 : ℕ)
      ∧ Real.log (514 : ℕ) ≤ ((624222327/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_515 :
    ((62441669/10000000 : ℚ) : ℝ) ≤ Real.log (515 : ℕ)
      ∧ Real.log (515 : ℕ) ≤ ((624416691/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_516 :
    ((156152669/25000000 : ℚ) : ℝ) ≤ Real.log (516 : ℕ)
      ∧ Real.log (516 : ℕ) ≤ ((624610677/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_517 :
    ((624804287/100000000 : ℚ) : ℝ) ≤ Real.log (517 : ℕ)
      ∧ Real.log (517 : ℕ) ≤ ((9762567/1562500 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_518 :
    ((156249381/25000000 : ℚ) : ℝ) ≤ Real.log (518 : ℕ)
      ∧ Real.log (518 : ℕ) ≤ ((24999901/4000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_519 :
    ((156297597/25000000 : ℚ) : ℝ) ≤ Real.log (519 : ℕ)
      ∧ Real.log (519 : ℕ) ≤ ((625190389/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_520 :
    ((625382881/100000000 : ℚ) : ℝ) ≤ Real.log (520 : ℕ)
      ∧ Real.log (520 : ℕ) ≤ ((312691441/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_521 :
    ((156393751/25000000 : ℚ) : ℝ) ≤ Real.log (521 : ℕ)
      ∧ Real.log (521 : ℕ) ≤ ((125115001/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_522 :
    ((312883379/50000000 : ℚ) : ℝ) ≤ Real.log (522 : ℕ)
      ∧ Real.log (522 : ℕ) ≤ ((625766759/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_523 :
    ((312979073/50000000 : ℚ) : ℝ) ≤ Real.log (523 : ℕ)
      ∧ Real.log (523 : ℕ) ≤ ((625958147/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_524 :
    ((39134323/6250000 : ℚ) : ℝ) ≤ Real.log (524 : ℕ)
      ∧ Real.log (524 : ℕ) ≤ ((626149169/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_525 :
    ((313169913/50000000 : ℚ) : ℝ) ≤ Real.log (525 : ℕ)
      ∧ Real.log (525 : ℕ) ≤ ((626339827/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_526 :
    ((626530121/100000000 : ℚ) : ℝ) ≤ Real.log (526 : ℕ)
      ∧ Real.log (526 : ℕ) ≤ ((313265061/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_527 :
    ((313360027/50000000 : ℚ) : ℝ) ≤ Real.log (527 : ℕ)
      ∧ Real.log (527 : ℕ) ≤ ((125344011/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_528 :
    ((156727407/25000000 : ℚ) : ℝ) ≤ Real.log (528 : ℕ)
      ∧ Real.log (528 : ℕ) ≤ ((626909629/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_529 :
    ((627098843/100000000 : ℚ) : ℝ) ≤ Real.log (529 : ℕ)
      ∧ Real.log (529 : ℕ) ≤ ((156774711/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_530 :
    ((6272877/1000000 : ℚ) : ℝ) ≤ Real.log (530 : ℕ)
      ∧ Real.log (530 : ℕ) ≤ ((627287701/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_531 :
    ((313738101/50000000 : ℚ) : ℝ) ≤ Real.log (531 : ℕ)
      ∧ Real.log (531 : ℕ) ≤ ((627476203/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_532 :
    ((156916087/25000000 : ℚ) : ℝ) ≤ Real.log (532 : ℕ)
      ∧ Real.log (532 : ℕ) ≤ ((627664349/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_533 :
    ((313926071/50000000 : ℚ) : ℝ) ≤ Real.log (533 : ℕ)
      ∧ Real.log (533 : ℕ) ≤ ((627852143/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_534 :
    ((628039583/100000000 : ℚ) : ℝ) ≤ Real.log (534 : ℕ)
      ∧ Real.log (534 : ℕ) ≤ ((19626237/3125000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_535 :
    ((314113337/50000000 : ℚ) : ℝ) ≤ Real.log (535 : ℕ)
      ∧ Real.log (535 : ℕ) ≤ ((25129067/4000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_536 :
    ((78551677/12500000 : ℚ) : ℝ) ≤ Real.log (536 : ℕ)
      ∧ Real.log (536 : ℕ) ≤ ((628413417/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_537 :
    ((628599809/100000000 : ℚ) : ℝ) ≤ Real.log (537 : ℕ)
      ∧ Real.log (537 : ℕ) ≤ ((62859981/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_538 :
    ((125757171/20000000 : ℚ) : ℝ) ≤ Real.log (538 : ℕ)
      ∧ Real.log (538 : ℕ) ≤ ((628785857/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_539 :
    ((628971557/100000000 : ℚ) : ℝ) ≤ Real.log (539 : ℕ)
      ∧ Real.log (539 : ℕ) ≤ ((314485779/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_540 :
    ((629156913/100000000 : ℚ) : ℝ) ≤ Real.log (540 : ℕ)
      ∧ Real.log (540 : ℕ) ≤ ((314578457/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_541 :
    ((629341927/100000000 : ℚ) : ℝ) ≤ Real.log (541 : ℕ)
      ∧ Real.log (541 : ℕ) ≤ ((78667741/12500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_542 :
    ((3147633/500000 : ℚ) : ℝ) ≤ Real.log (542 : ℕ)
      ∧ Real.log (542 : ℕ) ≤ ((629526601/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_543 :
    ((629710931/100000000 : ℚ) : ℝ) ≤ Real.log (543 : ℕ)
      ∧ Real.log (543 : ℕ) ≤ ((629710933/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_544 :
    ((157473731/25000000 : ℚ) : ℝ) ≤ Real.log (544 : ℕ)
      ∧ Real.log (544 : ℕ) ≤ ((25195797/4000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_545 :
    ((630078579/100000000 : ℚ) : ℝ) ≤ Real.log (545 : ℕ)
      ∧ Real.log (545 : ℕ) ≤ ((31503929/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_546 :
    ((630261897/100000000 : ℚ) : ℝ) ≤ Real.log (546 : ℕ)
      ∧ Real.log (546 : ℕ) ≤ ((315130949/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_547 :
    ((7880561/1250000 : ℚ) : ℝ) ≤ Real.log (547 : ℕ)
      ∧ Real.log (547 : ℕ) ≤ ((630444881/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_548 :
    ((78828441/12500000 : ℚ) : ℝ) ≤ Real.log (548 : ℕ)
      ∧ Real.log (548 : ℕ) ≤ ((630627529/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_549 :
    ((157702461/25000000 : ℚ) : ℝ) ≤ Real.log (549 : ℕ)
      ∧ Real.log (549 : ℕ) ≤ ((126161969/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_550 :
    ((630991827/100000000 : ℚ) : ℝ) ≤ Real.log (550 : ℕ)
      ∧ Real.log (550 : ℕ) ≤ ((157747957/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_551 :
    ((15779337/2500000 : ℚ) : ℝ) ≤ Real.log (551 : ℕ)
      ∧ Real.log (551 : ℕ) ≤ ((631173481/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_552 :
    ((157838701/25000000 : ℚ) : ℝ) ≤ Real.log (552 : ℕ)
      ∧ Real.log (552 : ℕ) ≤ ((126270961/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_553 :
    ((3157679/500000 : ℚ) : ℝ) ≤ Real.log (553 : ℕ)
      ∧ Real.log (553 : ℕ) ≤ ((631535801/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_554 :
    ((157929117/25000000 : ℚ) : ℝ) ≤ Real.log (554 : ℕ)
      ∧ Real.log (554 : ℕ) ≤ ((631716469/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_555 :
    ((631896811/100000000 : ℚ) : ℝ) ≤ Real.log (555 : ℕ)
      ∧ Real.log (555 : ℕ) ≤ ((157974203/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_556 :
    ((632076829/100000000 : ℚ) : ℝ) ≤ Real.log (556 : ℕ)
      ∧ Real.log (556 : ℕ) ≤ ((63207683/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_557 :
    ((632256523/100000000 : ℚ) : ℝ) ≤ Real.log (557 : ℕ)
      ∧ Real.log (557 : ℕ) ≤ ((25290261/4000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_558 :
    ((79054487/12500000 : ℚ) : ℝ) ≤ Real.log (558 : ℕ)
      ∧ Real.log (558 : ℕ) ≤ ((632435897/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_559 :
    ((632614947/100000000 : ℚ) : ℝ) ≤ Real.log (559 : ℕ)
      ∧ Real.log (559 : ℕ) ≤ ((158153737/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_560 :
    ((316396839/50000000 : ℚ) : ℝ) ≤ Real.log (560 : ℕ)
      ∧ Real.log (560 : ℕ) ≤ ((632793679/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_561 :
    ((63297209/10000000 : ℚ) : ℝ) ≤ Real.log (561 : ℕ)
      ∧ Real.log (561 : ℕ) ≤ ((632972091/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_562 :
    ((79143773/12500000 : ℚ) : ℝ) ≤ Real.log (562 : ℕ)
      ∧ Real.log (562 : ℕ) ≤ ((316575093/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_563 :
    ((316663981/50000000 : ℚ) : ℝ) ≤ Real.log (563 : ℕ)
      ∧ Real.log (563 : ℕ) ≤ ((633327963/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_564 :
    ((25340217/4000000 : ℚ) : ℝ) ≤ Real.log (564 : ℕ)
      ∧ Real.log (564 : ℕ) ≤ ((316752713/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_565 :
    ((633682573/100000000 : ℚ) : ℝ) ≤ Real.log (565 : ℕ)
      ∧ Real.log (565 : ℕ) ≤ ((316841287/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_566 :
    ((633859407/100000000 : ℚ) : ℝ) ≤ Real.log (566 : ℕ)
      ∧ Real.log (566 : ℕ) ≤ ((39616213/6250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_567 :
    ((63403593/10000000 : ℚ) : ℝ) ≤ Real.log (567 : ℕ)
      ∧ Real.log (567 : ℕ) ≤ ((634035931/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_568 :
    ((634212141/100000000 : ℚ) : ℝ) ≤ Real.log (568 : ℕ)
      ∧ Real.log (568 : ℕ) ≤ ((317106071/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_569 :
    ((634388043/100000000 : ℚ) : ℝ) ≤ Real.log (569 : ℕ)
      ∧ Real.log (569 : ℕ) ≤ ((158597011/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_570 :
    ((158640909/25000000 : ℚ) : ℝ) ≤ Real.log (570 : ℕ)
      ∧ Real.log (570 : ℕ) ≤ ((634563637/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_571 :
    ((15868473/2500000 : ℚ) : ℝ) ≤ Real.log (571 : ℕ)
      ∧ Real.log (571 : ℕ) ≤ ((317369461/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_572 :
    ((634913899/100000000 : ℚ) : ℝ) ≤ Real.log (572 : ℕ)
      ∧ Real.log (572 : ℕ) ≤ ((6349139/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_573 :
    ((635088571/100000000 : ℚ) : ℝ) ≤ Real.log (573 : ℕ)
      ∧ Real.log (573 : ℕ) ≤ ((158772143/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_574 :
    ((635262939/100000000 : ℚ) : ℝ) ≤ Real.log (574 : ℕ)
      ∧ Real.log (574 : ℕ) ≤ ((31763147/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_575 :
    ((158859251/25000000 : ℚ) : ℝ) ≤ Real.log (575 : ℕ)
      ∧ Real.log (575 : ℕ) ≤ ((127087401/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_576 :
    ((317805383/50000000 : ℚ) : ℝ) ≤ Real.log (576 : ℕ)
      ∧ Real.log (576 : ℕ) ≤ ((635610767/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_577 :
    ((317892113/50000000 : ℚ) : ℝ) ≤ Real.log (577 : ℕ)
      ∧ Real.log (577 : ℕ) ≤ ((635784227/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_578 :
    ((317978693/50000000 : ℚ) : ℝ) ≤ Real.log (578 : ℕ)
      ∧ Real.log (578 : ℕ) ≤ ((635957387/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_579 :
    ((636130247/100000000 : ℚ) : ℝ) ≤ Real.log (579 : ℕ)
      ∧ Real.log (579 : ℕ) ≤ ((79516281/12500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_580 :
    ((63630281/10000000 : ℚ) : ℝ) ≤ Real.log (580 : ℕ)
      ∧ Real.log (580 : ℕ) ≤ ((636302811/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_581 :
    ((25459003/4000000 : ℚ) : ℝ) ≤ Real.log (581 : ℕ)
      ∧ Real.log (581 : ℕ) ≤ ((159118769/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_582 :
    ((159161761/25000000 : ℚ) : ℝ) ≤ Real.log (582 : ℕ)
      ∧ Real.log (582 : ℕ) ≤ ((127329409/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_583 :
    ((318409359/50000000 : ℚ) : ℝ) ≤ Real.log (583 : ℕ)
      ∧ Real.log (583 : ℕ) ≤ ((636818719/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_584 :
    ((318495049/50000000 : ℚ) : ℝ) ≤ Real.log (584 : ℕ)
      ∧ Real.log (584 : ℕ) ≤ ((636990099/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_585 :
    ((19911287/3125000 : ℚ) : ℝ) ≤ Real.log (585 : ℕ)
      ∧ Real.log (585 : ℕ) ≤ ((127432237/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_586 :
    ((318665989/50000000 : ℚ) : ℝ) ≤ Real.log (586 : ℕ)
      ∧ Real.log (586 : ℕ) ≤ ((31866599/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_587 :
    ((637502481/100000000 : ℚ) : ℝ) ≤ Real.log (587 : ℕ)
      ∧ Real.log (587 : ℕ) ≤ ((637502483/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_588 :
    ((318836347/50000000 : ℚ) : ℝ) ≤ Real.log (588 : ℕ)
      ∧ Real.log (588 : ℕ) ≤ ((127534539/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_589 :
    ((318921309/50000000 : ℚ) : ℝ) ≤ Real.log (589 : ℕ)
      ∧ Real.log (589 : ℕ) ≤ ((637842619/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_590 :
    ((638012253/100000000 : ℚ) : ℝ) ≤ Real.log (590 : ℕ)
      ∧ Real.log (590 : ℕ) ≤ ((319006127/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_591 :
    ((638181601/100000000 : ℚ) : ℝ) ≤ Real.log (591 : ℕ)
      ∧ Real.log (591 : ℕ) ≤ ((319090801/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_592 :
    ((638350663/100000000 : ℚ) : ℝ) ≤ Real.log (592 : ℕ)
      ∧ Real.log (592 : ℕ) ≤ ((79793833/12500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_593 :
    ((638519439/100000000 : ℚ) : ℝ) ≤ Real.log (593 : ℕ)
      ∧ Real.log (593 : ℕ) ≤ ((638519441/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_594 :
    ((638687931/100000000 : ℚ) : ℝ) ≤ Real.log (594 : ℕ)
      ∧ Real.log (594 : ℕ) ≤ ((638687933/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_595 :
    ((31942807/5000000 : ℚ) : ℝ) ≤ Real.log (595 : ℕ)
      ∧ Real.log (595 : ℕ) ≤ ((638856141/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_596 :
    ((319512033/50000000 : ℚ) : ℝ) ≤ Real.log (596 : ℕ)
      ∧ Real.log (596 : ℕ) ≤ ((639024067/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_597 :
    ((639191711/100000000 : ℚ) : ℝ) ≤ Real.log (597 : ℕ)
      ∧ Real.log (597 : ℕ) ≤ ((19974741/3125000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_598 :
    ((25574363/4000000 : ℚ) : ℝ) ≤ Real.log (598 : ℕ)
      ∧ Real.log (598 : ℕ) ≤ ((159839769/25000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_599 :
    ((639526159/100000000 : ℚ) : ℝ) ≤ Real.log (599 : ℕ)
      ∧ Real.log (599 : ℕ) ≤ ((7994077/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_600 :
    ((127938593/20000000 : ℚ) : ℝ) ≤ Real.log (600 : ℕ)
      ∧ Real.log (600 : ℕ) ≤ ((319846483/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_601 :
    ((639859493/100000000 : ℚ) : ℝ) ≤ Real.log (601 : ℕ)
      ∧ Real.log (601 : ℕ) ≤ ((319929747/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_602 :
    ((40001609/6250000 : ℚ) : ℝ) ≤ Real.log (602 : ℕ)
      ∧ Real.log (602 : ℕ) ≤ ((128005149/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_603 :
    ((640191719/100000000 : ℚ) : ℝ) ≤ Real.log (603 : ℕ)
      ∧ Real.log (603 : ℕ) ≤ ((16004793/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_604 :
    ((640357419/100000000 : ℚ) : ℝ) ≤ Real.log (604 : ℕ)
      ∧ Real.log (604 : ℕ) ≤ ((32017871/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_605 :
    ((128104569/20000000 : ℚ) : ℝ) ≤ Real.log (605 : ℕ)
      ∧ Real.log (605 : ℕ) ≤ ((320261423/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_606 :
    ((320343999/50000000 : ℚ) : ℝ) ≤ Real.log (606 : ℕ)
      ∧ Real.log (606 : ℕ) ≤ ((640687999/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_607 :
    ((640852879/100000000 : ℚ) : ℝ) ≤ Real.log (607 : ℕ)
      ∧ Real.log (607 : ℕ) ≤ ((8010661/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_608 :
    ((40063593/6250000 : ℚ) : ℝ) ≤ Real.log (608 : ℕ)
      ∧ Real.log (608 : ℕ) ≤ ((641017489/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_609 :
    ((320590913/50000000 : ℚ) : ℝ) ≤ Real.log (609 : ℕ)
      ∧ Real.log (609 : ℕ) ≤ ((641181827/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_610 :
    ((128269179/20000000 : ℚ) : ℝ) ≤ Real.log (610 : ℕ)
      ∧ Real.log (610 : ℕ) ≤ ((80168237/12500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_611 :
    ((128301939/20000000 : ℚ) : ℝ) ≤ Real.log (611 : ℕ)
      ∧ Real.log (611 : ℕ) ≤ ((641509697/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_612 :
    ((160418307/25000000 : ℚ) : ℝ) ≤ Real.log (612 : ℕ)
      ∧ Real.log (612 : ℕ) ≤ ((641673229/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_613 :
    ((641836493/100000000 : ℚ) : ℝ) ≤ Real.log (613 : ℕ)
      ∧ Real.log (613 : ℕ) ≤ ((320918247/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_614 :
    ((160499873/25000000 : ℚ) : ℝ) ≤ Real.log (614 : ℕ)
      ∧ Real.log (614 : ℕ) ≤ ((320999747/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_615 :
    ((321081113/50000000 : ℚ) : ℝ) ≤ Real.log (615 : ℕ)
      ∧ Real.log (615 : ℕ) ≤ ((642162227/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_616 :
    ((80290587/12500000 : ℚ) : ℝ) ≤ Real.log (616 : ℕ)
      ∧ Real.log (616 : ℕ) ≤ ((642324697/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_617 :
    ((321243451/50000000 : ℚ) : ℝ) ≤ Real.log (617 : ℕ)
      ∧ Real.log (617 : ℕ) ≤ ((642486903/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_618 :
    ((128529769/20000000 : ℚ) : ℝ) ≤ Real.log (618 : ℕ)
      ∧ Real.log (618 : ℕ) ≤ ((321324423/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_619 :
    ((642810527/100000000 : ℚ) : ℝ) ≤ Real.log (619 : ℕ)
      ∧ Real.log (619 : ℕ) ≤ ((20087829/3125000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_620 :
    ((642971947/100000000 : ℚ) : ℝ) ≤ Real.log (620 : ℕ)
      ∧ Real.log (620 : ℕ) ≤ ((642971949/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_621 :
    ((160783277/25000000 : ℚ) : ℝ) ≤ Real.log (621 : ℕ)
      ∧ Real.log (621 : ℕ) ≤ ((643133109/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_622 :
    ((643294009/100000000 : ℚ) : ℝ) ≤ Real.log (622 : ℕ)
      ∧ Real.log (622 : ℕ) ≤ ((64329401/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_623 :
    ((643454651/100000000 : ℚ) : ℝ) ≤ Real.log (623 : ℕ)
      ∧ Real.log (623 : ℕ) ≤ ((643454653/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_624 :
    ((160903759/25000000 : ℚ) : ℝ) ≤ Real.log (624 : ℕ)
      ∧ Real.log (624 : ℕ) ≤ ((321807519/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_625 :
    ((160943791/25000000 : ℚ) : ℝ) ≤ Real.log (625 : ℕ)
      ∧ Real.log (625 : ℕ) ≤ ((321887583/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_626 :
    ((643935037/100000000 : ℚ) : ℝ) ≤ Real.log (626 : ℕ)
      ∧ Real.log (626 : ℕ) ≤ ((321967519/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_627 :
    ((322047327/50000000 : ℚ) : ℝ) ≤ Real.log (627 : ℕ)
      ∧ Real.log (627 : ℕ) ≤ ((128818931/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_628 :
    ((10066469/1562500 : ℚ) : ℝ) ≤ Real.log (628 : ℕ)
      ∧ Real.log (628 : ℕ) ≤ ((644254017/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_629 :
    ((1031061/160000 : ℚ) : ℝ) ≤ Real.log (629 : ℕ)
      ∧ Real.log (629 : ℕ) ≤ ((322206563/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_630 :
    ((644571981/100000000 : ℚ) : ℝ) ≤ Real.log (630 : ℕ)
      ∧ Real.log (630 : ℕ) ≤ ((644571983/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_631 :
    ((322365293/50000000 : ℚ) : ℝ) ≤ Real.log (631 : ℕ)
      ∧ Real.log (631 : ℕ) ≤ ((644730587/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_632 :
    ((644888939/100000000 : ℚ) : ℝ) ≤ Real.log (632 : ℕ)
      ∧ Real.log (632 : ℕ) ≤ ((32244447/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_633 :
    ((322523521/50000000 : ℚ) : ℝ) ≤ Real.log (633 : ℕ)
      ∧ Real.log (633 : ℕ) ≤ ((645047043/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_634 :
    ((129040979/20000000 : ℚ) : ℝ) ≤ Real.log (634 : ℕ)
      ∧ Real.log (634 : ℕ) ≤ ((20162653/3125000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_635 :
    ((645362499/100000000 : ℚ) : ℝ) ≤ Real.log (635 : ℕ)
      ∧ Real.log (635 : ℕ) ≤ ((645362501/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_636 :
    ((40344991/6250000 : ℚ) : ℝ) ≤ Real.log (636 : ℕ)
      ∧ Real.log (636 : ℕ) ≤ ((645519857/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_637 :
    ((129135393/20000000 : ℚ) : ℝ) ≤ Real.log (637 : ℕ)
      ∧ Real.log (637 : ℕ) ≤ ((322838483/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_638 :
    ((161458457/25000000 : ℚ) : ℝ) ≤ Real.log (638 : ℕ)
      ∧ Real.log (638 : ℕ) ≤ ((645833829/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_639 :
    ((129198089/20000000 : ℚ) : ℝ) ≤ Real.log (639 : ℕ)
      ∧ Real.log (639 : ℕ) ≤ ((322995223/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_640 :
    ((646146817/100000000 : ℚ) : ℝ) ≤ Real.log (640 : ℕ)
      ∧ Real.log (640 : ℕ) ≤ ((646146819/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_641 :
    ((129260589/20000000 : ℚ) : ℝ) ≤ Real.log (641 : ℕ)
      ∧ Real.log (641 : ℕ) ≤ ((646302947/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_642 :
    ((64645883/10000000 : ℚ) : ℝ) ≤ Real.log (642 : ℕ)
      ∧ Real.log (642 : ℕ) ≤ ((646458831/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_643 :
    ((80826809/12500000 : ℚ) : ℝ) ≤ Real.log (643 : ℕ)
      ∧ Real.log (643 : ℕ) ≤ ((646614473/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_644 :
    ((40423117/6250000 : ℚ) : ℝ) ≤ Real.log (644 : ℕ)
      ∧ Real.log (644 : ℕ) ≤ ((323384937/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_645 :
    ((646925031/100000000 : ℚ) : ℝ) ≤ Real.log (645 : ℕ)
      ∧ Real.log (645 : ℕ) ≤ ((646925033/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_646 :
    ((12941599/2000000 : ℚ) : ℝ) ≤ Real.log (646 : ℕ)
      ∧ Real.log (646 : ℕ) ≤ ((647079951/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_647 :
    ((647234629/100000000 : ℚ) : ℝ) ≤ Real.log (647 : ℕ)
      ∧ Real.log (647 : ℕ) ≤ ((64723463/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_648 :
    ((647389069/100000000 : ℚ) : ℝ) ≤ Real.log (648 : ℕ)
      ∧ Real.log (648 : ℕ) ≤ ((647389071/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_649 :
    ((647543271/100000000 : ℚ) : ℝ) ≤ Real.log (649 : ℕ)
      ∧ Real.log (649 : ℕ) ≤ ((647543273/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_650 :
    ((161924309/25000000 : ℚ) : ℝ) ≤ Real.log (650 : ℕ)
      ∧ Real.log (650 : ℕ) ≤ ((647697237/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_651 :
    ((161962741/25000000 : ℚ) : ℝ) ≤ Real.log (651 : ℕ)
      ∧ Real.log (651 : ℕ) ≤ ((129570193/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_652 :
    ((81000557/12500000 : ℚ) : ℝ) ≤ Real.log (652 : ℕ)
      ∧ Real.log (652 : ℕ) ≤ ((648004457/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_653 :
    ((40509857/6250000 : ℚ) : ℝ) ≤ Real.log (653 : ℕ)
      ∧ Real.log (653 : ℕ) ≤ ((324078857/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_654 :
    ((129662147/20000000 : ℚ) : ℝ) ≤ Real.log (654 : ℕ)
      ∧ Real.log (654 : ℕ) ≤ ((40519421/6250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_655 :
    ((648463523/100000000 : ℚ) : ℝ) ≤ Real.log (655 : ℕ)
      ∧ Real.log (655 : ℕ) ≤ ((25938541/4000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_656 :
    ((324308039/50000000 : ℚ) : ℝ) ≤ Real.log (656 : ℕ)
      ∧ Real.log (656 : ℕ) ≤ ((8107701/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_657 :
    ((648768401/100000000 : ℚ) : ℝ) ≤ Real.log (657 : ℕ)
      ∧ Real.log (657 : ℕ) ≤ ((648768403/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_658 :
    ((648920493/100000000 : ℚ) : ℝ) ≤ Real.log (658 : ℕ)
      ∧ Real.log (658 : ℕ) ≤ ((324460247/50000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_659 :
    ((649072353/100000000 : ℚ) : ℝ) ≤ Real.log (659 : ℕ)
      ∧ Real.log (659 : ℕ) ≤ ((129814471/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_660 :
    ((649223983/100000000 : ℚ) : ℝ) ≤ Real.log (660 : ℕ)
      ∧ Real.log (660 : ℕ) ≤ ((129844797/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_661 :
    ((649375383/100000000 : ℚ) : ℝ) ≤ Real.log (661 : ℕ)
      ∧ Real.log (661 : ℕ) ≤ ((129875077/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_662 :
    ((129905311/20000000 : ℚ) : ℝ) ≤ Real.log (662 : ℕ)
      ∧ Real.log (662 : ℕ) ≤ ((649526557/100000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_663 :
    ((324838749/50000000 : ℚ) : ℝ) ≤ Real.log (663 : ℕ)
      ∧ Real.log (663 : ℕ) ≤ ((259871/40000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_664 :
    ((324914107/50000000 : ℚ) : ℝ) ≤ Real.log (664 : ℕ)
      ∧ Real.log (664 : ℕ) ≤ ((81228527/12500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_665 :
    ((40623669/6250000 : ℚ) : ℝ) ≤ Real.log (665 : ℕ)
      ∧ Real.log (665 : ℕ) ≤ ((129995741/20000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_666 :
    ((130025793/20000000 : ℚ) : ℝ) ≤ Real.log (666 : ℕ)
      ∧ Real.log (666 : ℕ) ≤ ((81266121/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_667 :
    ((325139501/50000000 : ℚ) : ℝ) ≤ Real.log (667 : ℕ)
      ∧ Real.log (667 : ℕ) ≤ ((130055801/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_668 :
    ((130085763/20000000 : ℚ) : ℝ) ≤ Real.log (668 : ℕ)
      ∧ Real.log (668 : ℕ) ≤ ((325214409/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_669 :
    ((162644601/25000000 : ℚ) : ℝ) ≤ Real.log (669 : ℕ)
      ∧ Real.log (669 : ℕ) ≤ ((650578407/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_670 :
    ((650727769/100000000 : ℚ) : ℝ) ≤ Real.log (670 : ℕ)
      ∧ Real.log (670 : ℕ) ≤ ((162681943/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_671 :
    ((40679807/6250000 : ℚ) : ℝ) ≤ Real.log (671 : ℕ)
      ∧ Real.log (671 : ℕ) ≤ ((325438457/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_672 :
    ((81378229/12500000 : ℚ) : ℝ) ≤ Real.log (672 : ℕ)
      ∧ Real.log (672 : ℕ) ≤ ((130205167/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_673 :
    ((651174531/100000000 : ℚ) : ℝ) ≤ Real.log (673 : ℕ)
      ∧ Real.log (673 : ℕ) ≤ ((325587267/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_674 :
    ((651323009/100000000 : ℚ) : ℝ) ≤ Real.log (674 : ℕ)
      ∧ Real.log (674 : ℕ) ≤ ((162830753/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_675 :
    ((651471267/100000000 : ℚ) : ℝ) ≤ Real.log (675 : ℕ)
      ∧ Real.log (675 : ℕ) ≤ ((65147127/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_676 :
    ((325809653/50000000 : ℚ) : ℝ) ≤ Real.log (676 : ℕ)
      ∧ Real.log (676 : ℕ) ≤ ((162904827/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_677 :
    ((5214137/800000 : ℚ) : ℝ) ≤ Real.log (677 : ℕ)
      ∧ Real.log (677 : ℕ) ≤ ((81470891/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_678 :
    ((651914727/100000000 : ℚ) : ℝ) ≤ Real.log (678 : ℕ)
      ∧ Real.log (678 : ℕ) ≤ ((651914729/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_679 :
    ((652062111/100000000 : ℚ) : ℝ) ≤ Real.log (679 : ℕ)
      ∧ Real.log (679 : ℕ) ≤ ((652062113/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_680 :
    ((326104639/50000000 : ℚ) : ℝ) ≤ Real.log (680 : ℕ)
      ∧ Real.log (680 : ℕ) ≤ ((1019077/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_681 :
    ((652356229/100000000 : ℚ) : ℝ) ≤ Real.log (681 : ℕ)
      ∧ Real.log (681 : ℕ) ≤ ((652356231/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_682 :
    ((163125741/25000000 : ℚ) : ℝ) ≤ Real.log (682 : ℕ)
      ∧ Real.log (682 : ℕ) ≤ ((326251483/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_683 :
    ((163162371/25000000 : ℚ) : ℝ) ≤ Real.log (683 : ℕ)
      ∧ Real.log (683 : ℕ) ≤ ((652649487/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_684 :
    ((65279579/10000000 : ℚ) : ℝ) ≤ Real.log (684 : ℕ)
      ∧ Real.log (684 : ℕ) ≤ ((40799737/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_685 :
    ((326470941/50000000 : ℚ) : ℝ) ≤ Real.log (685 : ℕ)
      ∧ Real.log (685 : ℕ) ≤ ((163235471/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_686 :
    ((653087761/100000000 : ℚ) : ℝ) ≤ Real.log (686 : ℕ)
      ∧ Real.log (686 : ℕ) ≤ ((653087763/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_687 :
    ((163308357/25000000 : ℚ) : ℝ) ≤ Real.log (687 : ℕ)
      ∧ Real.log (687 : ℕ) ≤ ((65323343/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_688 :
    ((326689441/50000000 : ℚ) : ℝ) ≤ Real.log (688 : ℕ)
      ∧ Real.log (688 : ℕ) ≤ ((163344721/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_689 :
    ((326762063/50000000 : ℚ) : ℝ) ≤ Real.log (689 : ℕ)
      ∧ Real.log (689 : ℕ) ≤ ((20422629/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_690 :
    ((326834579/50000000 : ℚ) : ℝ) ≤ Real.log (690 : ℕ)
      ∧ Real.log (690 : ℕ) ≤ ((16341729/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_691 :
    ((653813981/100000000 : ℚ) : ℝ) ≤ Real.log (691 : ℕ)
      ∧ Real.log (691 : ℕ) ≤ ((653813983/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_692 :
    ((326979297/50000000 : ℚ) : ℝ) ≤ Real.log (692 : ℕ)
      ∧ Real.log (692 : ℕ) ≤ ((163489649/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_693 :
    ((654102999/100000000 : ℚ) : ℝ) ≤ Real.log (693 : ℕ)
      ∧ Real.log (693 : ℕ) ≤ ((654103001/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_694 :
    ((130849439/20000000 : ℚ) : ℝ) ≤ Real.log (694 : ℕ)
      ∧ Real.log (694 : ℕ) ≤ ((654247197/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_695 :
    ((654391183/100000000 : ℚ) : ℝ) ≤ Real.log (695 : ℕ)
      ∧ Real.log (695 : ℕ) ≤ ((130878237/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_696 :
    ((130906993/20000000 : ℚ) : ℝ) ≤ Real.log (696 : ℕ)
      ∧ Real.log (696 : ℕ) ≤ ((654534967/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_697 :
    ((32733927/5000000 : ℚ) : ℝ) ≤ Real.log (697 : ℕ)
      ∧ Real.log (697 : ℕ) ≤ ((327339271/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_698 :
    ((654821909/100000000 : ℚ) : ℝ) ≤ Real.log (698 : ℕ)
      ∧ Real.log (698 : ℕ) ≤ ((654821911/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_699 :
    ((654965073/100000000 : ℚ) : ℝ) ≤ Real.log (699 : ℕ)
      ∧ Real.log (699 : ℕ) ≤ ((26198603/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_700 :
    ((10236063/1562500 : ℚ) : ℝ) ≤ Real.log (700 : ℕ)
      ∧ Real.log (700 : ℕ) ≤ ((327554017/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_701 :
    ((163812697/25000000 : ℚ) : ℝ) ≤ Real.log (701 : ℕ)
      ∧ Real.log (701 : ℕ) ≤ ((655250789/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_702 :
    ((655393339/100000000 : ℚ) : ℝ) ≤ Real.log (702 : ℕ)
      ∧ Real.log (702 : ℕ) ≤ ((655393341/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_703 :
    ((81941961/12500000 : ℚ) : ℝ) ≤ Real.log (703 : ℕ)
      ∧ Real.log (703 : ℕ) ≤ ((65553569/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_704 :
    ((327838917/50000000 : ℚ) : ℝ) ≤ Real.log (704 : ℕ)
      ∧ Real.log (704 : ℕ) ≤ ((163919459/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_705 :
    ((655819779/100000000 : ℚ) : ℝ) ≤ Real.log (705 : ℕ)
      ∧ Real.log (705 : ℕ) ≤ ((655819781/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_706 :
    ((655961523/100000000 : ℚ) : ℝ) ≤ Real.log (706 : ℕ)
      ∧ Real.log (706 : ℕ) ≤ ((163990381/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_707 :
    ((328051533/50000000 : ℚ) : ℝ) ≤ Real.log (707 : ℕ)
      ∧ Real.log (707 : ℕ) ≤ ((656103067/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_708 :
    ((82030551/12500000 : ℚ) : ℝ) ≤ Real.log (708 : ℕ)
      ∧ Real.log (708 : ℕ) ≤ ((65624441/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_709 :
    ((41024097/6250000 : ℚ) : ℝ) ≤ Real.log (709 : ℕ)
      ∧ Real.log (709 : ℕ) ≤ ((656385553/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_710 :
    ((20516453/3125000 : ℚ) : ℝ) ≤ Real.log (710 : ℕ)
      ∧ Real.log (710 : ℕ) ≤ ((328263249/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_711 :
    ((328333621/50000000 : ℚ) : ℝ) ≤ Real.log (711 : ℕ)
      ∧ Real.log (711 : ℕ) ≤ ((164166811/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_712 :
    ((65680779/10000000 : ℚ) : ℝ) ≤ Real.log (712 : ℕ)
      ∧ Real.log (712 : ℕ) ≤ ((41050487/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_713 :
    ((656948141/100000000 : ℚ) : ℝ) ≤ Real.log (713 : ℕ)
      ∧ Real.log (713 : ℕ) ≤ ((656948143/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_714 :
    ((131417659/20000000 : ℚ) : ℝ) ≤ Real.log (714 : ℕ)
      ∧ Real.log (714 : ℕ) ≤ ((657088297/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_715 :
    ((657228253/100000000 : ℚ) : ℝ) ≤ Real.log (715 : ℕ)
      ∧ Real.log (715 : ℕ) ≤ ((131445651/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_716 :
    ((41085501/6250000 : ℚ) : ℝ) ≤ Real.log (716 : ℕ)
      ∧ Real.log (716 : ℕ) ≤ ((657368017/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_717 :
    ((657507583/100000000 : ℚ) : ℝ) ≤ Real.log (717 : ℕ)
      ∧ Real.log (717 : ℕ) ≤ ((131501517/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_718 :
    ((164411739/25000000 : ℚ) : ℝ) ≤ Real.log (718 : ℕ)
      ∧ Real.log (718 : ℕ) ≤ ((657646957/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_719 :
    ((131557227/20000000 : ℚ) : ℝ) ≤ Real.log (719 : ℕ)
      ∧ Real.log (719 : ℕ) ≤ ((82223267/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_720 :
    ((514004/78125 : ℚ) : ℝ) ≤ Real.log (720 : ℕ)
      ∧ Real.log (720 : ℕ) ≤ ((328962561/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_721 :
    ((658063913/100000000 : ℚ) : ℝ) ≤ Real.log (721 : ℕ)
      ∧ Real.log (721 : ℕ) ≤ ((329031957/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_722 :
    ((658202513/100000000 : ℚ) : ℝ) ≤ Real.log (722 : ℕ)
      ∧ Real.log (722 : ℕ) ≤ ((329101257/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_723 :
    ((658340921/100000000 : ℚ) : ℝ) ≤ Real.log (723 : ℕ)
      ∧ Real.log (723 : ℕ) ≤ ((658340923/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_724 :
    ((329239569/50000000 : ℚ) : ℝ) ≤ Real.log (724 : ℕ)
      ∧ Real.log (724 : ℕ) ≤ ((32923957/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_725 :
    ((131723433/20000000 : ℚ) : ℝ) ≤ Real.log (725 : ℕ)
      ∧ Real.log (725 : ℕ) ≤ ((329308583/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_726 :
    ((658755001/100000000 : ℚ) : ℝ) ≤ Real.log (726 : ℕ)
      ∧ Real.log (726 : ℕ) ≤ ((329377501/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_727 :
    ((658892647/100000000 : ℚ) : ℝ) ≤ Real.log (727 : ℕ)
      ∧ Real.log (727 : ℕ) ≤ ((82361581/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_728 :
    ((82378763/12500000 : ℚ) : ℝ) ≤ Real.log (728 : ℕ)
      ∧ Real.log (728 : ℕ) ≤ ((131806021/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_729 :
    ((164791843/25000000 : ℚ) : ℝ) ≤ Real.log (729 : ℕ)
      ∧ Real.log (729 : ℕ) ≤ ((329583687/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_730 :
    ((659304453/100000000 : ℚ) : ℝ) ≤ Real.log (730 : ℕ)
      ∧ Real.log (730 : ℕ) ≤ ((329652227/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_731 :
    ((131888269/20000000 : ℚ) : ℝ) ≤ Real.log (731 : ℕ)
      ∧ Real.log (731 : ℕ) ≤ ((659441347/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_732 :
    ((659578051/100000000 : ℚ) : ℝ) ≤ Real.log (732 : ℕ)
      ∧ Real.log (732 : ℕ) ≤ ((164894513/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_733 :
    ((659714569/100000000 : ℚ) : ℝ) ≤ Real.log (733 : ℕ)
      ∧ Real.log (733 : ℕ) ≤ ((659714571/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_734 :
    ((329925451/50000000 : ℚ) : ℝ) ≤ Real.log (734 : ℕ)
      ∧ Real.log (734 : ℕ) ≤ ((659850903/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_735 :
    ((659987049/100000000 : ℚ) : ℝ) ≤ Real.log (735 : ℕ)
      ∧ Real.log (735 : ℕ) ≤ ((13199741/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_736 :
    ((660123011/100000000 : ℚ) : ℝ) ≤ Real.log (736 : ℕ)
      ∧ Real.log (736 : ℕ) ≤ ((165030753/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_737 :
    ((165064697/25000000 : ℚ) : ℝ) ≤ Real.log (737 : ℕ)
      ∧ Real.log (737 : ℕ) ≤ ((66025879/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_738 :
    ((330197191/50000000 : ℚ) : ℝ) ≤ Real.log (738 : ℕ)
      ∧ Real.log (738 : ℕ) ≤ ((660394383/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_739 :
    ((660529791/100000000 : ℚ) : ℝ) ≤ Real.log (739 : ℕ)
      ∧ Real.log (739 : ℕ) ≤ ((660529793/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_740 :
    ((330332509/50000000 : ℚ) : ℝ) ≤ Real.log (740 : ℕ)
      ∧ Real.log (740 : ℕ) ≤ ((660665019/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_741 :
    ((330400031/50000000 : ℚ) : ℝ) ≤ Real.log (741 : ℕ)
      ∧ Real.log (741 : ℕ) ≤ ((660800063/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_742 :
    ((165233731/25000000 : ℚ) : ℝ) ≤ Real.log (742 : ℕ)
      ∧ Real.log (742 : ℕ) ≤ ((26437397/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_743 :
    ((165267401/25000000 : ℚ) : ℝ) ≤ Real.log (743 : ℕ)
      ∧ Real.log (743 : ℕ) ≤ ((132213921/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_744 :
    ((661204103/100000000 : ℚ) : ℝ) ≤ Real.log (744 : ℕ)
      ∧ Real.log (744 : ℕ) ≤ ((82650513/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_745 :
    ((661338421/100000000 : ℚ) : ℝ) ≤ Real.log (745 : ℕ)
      ∧ Real.log (745 : ℕ) ≤ ((330669211/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_746 :
    ((661472559/100000000 : ℚ) : ℝ) ≤ Real.log (746 : ℕ)
      ∧ Real.log (746 : ℕ) ≤ ((661472561/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_747 :
    ((330803259/50000000 : ℚ) : ℝ) ≤ Real.log (747 : ℕ)
      ∧ Real.log (747 : ℕ) ≤ ((661606519/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_748 :
    ((661740297/100000000 : ℚ) : ℝ) ≤ Real.log (748 : ℕ)
      ∧ Real.log (748 : ℕ) ≤ ((330870149/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_749 :
    ((330936949/50000000 : ℚ) : ℝ) ≤ Real.log (749 : ℕ)
      ∧ Real.log (749 : ℕ) ≤ ((661873899/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_750 :
    ((16550183/2500000 : ℚ) : ℝ) ≤ Real.log (750 : ℕ)
      ∧ Real.log (750 : ℕ) ≤ ((662007321/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_751 :
    ((132428113/20000000 : ℚ) : ℝ) ≤ Real.log (751 : ℕ)
      ∧ Real.log (751 : ℕ) ≤ ((331070283/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_752 :
    ((20696051/3125000 : ℚ) : ℝ) ≤ Real.log (752 : ℕ)
      ∧ Real.log (752 : ℕ) ≤ ((662273633/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_753 :
    ((331203261/50000000 : ℚ) : ℝ) ≤ Real.log (753 : ℕ)
      ∧ Real.log (753 : ℕ) ≤ ((662406523/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_754 :
    ((165634809/25000000 : ℚ) : ℝ) ≤ Real.log (754 : ℕ)
      ∧ Real.log (754 : ℕ) ≤ ((662539237/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_755 :
    ((331335887/50000000 : ℚ) : ℝ) ≤ Real.log (755 : ℕ)
      ∧ Real.log (755 : ℕ) ≤ ((26506871/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_756 :
    ((662804137/100000000 : ℚ) : ℝ) ≤ Real.log (756 : ℕ)
      ∧ Real.log (756 : ℕ) ≤ ((331402069/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_757 :
    ((26517453/4000000 : ℚ) : ℝ) ≤ Real.log (757 : ℕ)
      ∧ Real.log (757 : ℕ) ≤ ((331468163/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_758 :
    ((331534169/50000000 : ℚ) : ℝ) ≤ Real.log (758 : ℕ)
      ∧ Real.log (758 : ℕ) ≤ ((663068339/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_759 :
    ((663200177/100000000 : ℚ) : ℝ) ≤ Real.log (759 : ℕ)
      ∧ Real.log (759 : ℕ) ≤ ((331600089/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_760 :
    ((663331843/100000000 : ℚ) : ℝ) ≤ Real.log (760 : ℕ)
      ∧ Real.log (760 : ℕ) ≤ ((165832961/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_761 :
    ((132692667/20000000 : ℚ) : ℝ) ≤ Real.log (761 : ℕ)
      ∧ Real.log (761 : ℕ) ≤ ((82932917/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_762 :
    ((132718931/20000000 : ℚ) : ℝ) ≤ Real.log (762 : ℕ)
      ∧ Real.log (762 : ℕ) ≤ ((20737333/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_763 :
    ((663725803/100000000 : ℚ) : ℝ) ≤ Real.log (763 : ℕ)
      ∧ Real.log (763 : ℕ) ≤ ((165931451/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_764 :
    ((331928389/50000000 : ℚ) : ℝ) ≤ Real.log (764 : ℕ)
      ∧ Real.log (764 : ℕ) ≤ ((663856779/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_765 :
    ((663987583/100000000 : ℚ) : ℝ) ≤ Real.log (765 : ℕ)
      ∧ Real.log (765 : ℕ) ≤ ((5187403/781250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_766 :
    ((83014777/12500000 : ℚ) : ℝ) ≤ Real.log (766 : ℕ)
      ∧ Real.log (766 : ℕ) ≤ ((332059109/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_767 :
    ((16606217/2500000 : ℚ) : ℝ) ≤ Real.log (767 : ℕ)
      ∧ Real.log (767 : ℕ) ≤ ((664248681/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_768 :
    ((664378973/100000000 : ℚ) : ℝ) ≤ Real.log (768 : ℕ)
      ∧ Real.log (768 : ℕ) ≤ ((332189487/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_769 :
    ((83063637/12500000 : ℚ) : ℝ) ≤ Real.log (769 : ℕ)
      ∧ Real.log (769 : ℕ) ≤ ((664509097/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_770 :
    ((664639051/100000000 : ℚ) : ℝ) ≤ Real.log (770 : ℕ)
      ∧ Real.log (770 : ℕ) ≤ ((166159763/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_771 :
    ((664768837/100000000 : ℚ) : ℝ) ≤ Real.log (771 : ℕ)
      ∧ Real.log (771 : ℕ) ≤ ((332384419/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_772 :
    ((332449227/50000000 : ℚ) : ℝ) ≤ Real.log (772 : ℕ)
      ∧ Real.log (772 : ℕ) ≤ ((83112307/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_773 :
    ((10391061/1562500 : ℚ) : ℝ) ≤ Real.log (773 : ℕ)
      ∧ Real.log (773 : ℕ) ≤ ((133005581/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_774 :
    ((665157187/100000000 : ℚ) : ℝ) ≤ Real.log (774 : ℕ)
      ∧ Real.log (774 : ℕ) ≤ ((166289297/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_775 :
    ((332643151/50000000 : ℚ) : ℝ) ≤ Real.log (775 : ℕ)
      ∧ Real.log (775 : ℕ) ≤ ((665286303/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_776 :
    ((665415251/100000000 : ℚ) : ℝ) ≤ Real.log (776 : ℕ)
      ∧ Real.log (776 : ℕ) ≤ ((665415253/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_777 :
    ((332772017/50000000 : ℚ) : ℝ) ≤ Real.log (777 : ℕ)
      ∧ Real.log (777 : ℕ) ≤ ((166386009/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_778 :
    ((166418163/25000000 : ℚ) : ℝ) ≤ Real.log (778 : ℕ)
      ∧ Real.log (778 : ℕ) ≤ ((665672653/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_779 :
    ((41612569/6250000 : ℚ) : ℝ) ≤ Real.log (779 : ℕ)
      ∧ Real.log (779 : ℕ) ≤ ((133160221/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_780 :
    ((665929391/100000000 : ℚ) : ℝ) ≤ Real.log (780 : ℕ)
      ∧ Real.log (780 : ℕ) ≤ ((665929393/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_781 :
    ((333028757/50000000 : ℚ) : ℝ) ≤ Real.log (781 : ℕ)
      ∧ Real.log (781 : ℕ) ≤ ((166514379/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_782 :
    ((666185473/100000000 : ℚ) : ℝ) ≤ Real.log (782 : ℕ)
      ∧ Real.log (782 : ℕ) ≤ ((26647419/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_783 :
    ((666313269/100000000 : ℚ) : ℝ) ≤ Real.log (783 : ℕ)
      ∧ Real.log (783 : ℕ) ≤ ((66631327/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_784 :
    ((666440901/100000000 : ℚ) : ℝ) ≤ Real.log (784 : ℕ)
      ∧ Real.log (784 : ℕ) ≤ ((666440903/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_785 :
    ((666568371/100000000 : ℚ) : ℝ) ≤ Real.log (785 : ℕ)
      ∧ Real.log (785 : ℕ) ≤ ((166642093/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_786 :
    ((666695679/100000000 : ℚ) : ℝ) ≤ Real.log (786 : ℕ)
      ∧ Real.log (786 : ℕ) ≤ ((520856/78125 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_787 :
    ((83352853/12500000 : ℚ) : ℝ) ≤ Real.log (787 : ℕ)
      ∧ Real.log (787 : ℕ) ≤ ((26672913/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_788 :
    ((41684363/6250000 : ℚ) : ℝ) ≤ Real.log (788 : ℕ)
      ∧ Real.log (788 : ℕ) ≤ ((66694981/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_789 :
    ((83384579/12500000 : ℚ) : ℝ) ≤ Real.log (789 : ℕ)
      ∧ Real.log (789 : ℕ) ≤ ((667076633/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_790 :
    ((333601647/50000000 : ℚ) : ℝ) ≤ Real.log (790 : ℕ)
      ∧ Real.log (790 : ℕ) ≤ ((133440659/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_791 :
    ((166832449/25000000 : ℚ) : ℝ) ≤ Real.log (791 : ℕ)
      ∧ Real.log (791 : ℕ) ≤ ((667329797/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_792 :
    ((667456139/100000000 : ℚ) : ℝ) ≤ Real.log (792 : ℕ)
      ∧ Real.log (792 : ℕ) ≤ ((33372807/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_793 :
    ((333791161/50000000 : ℚ) : ℝ) ≤ Real.log (793 : ℕ)
      ∧ Real.log (793 : ℕ) ≤ ((667582323/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_794 :
    ((333854173/50000000 : ℚ) : ℝ) ≤ Real.log (794 : ℕ)
      ∧ Real.log (794 : ℕ) ≤ ((667708347/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_795 :
    ((667834211/100000000 : ℚ) : ℝ) ≤ Real.log (795 : ℕ)
      ∧ Real.log (795 : ℕ) ≤ ((166958553/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_796 :
    ((333979959/50000000 : ℚ) : ℝ) ≤ Real.log (796 : ℕ)
      ∧ Real.log (796 : ℕ) ≤ ((667959919/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_797 :
    ((668085467/100000000 : ℚ) : ℝ) ≤ Real.log (797 : ℕ)
      ∧ Real.log (797 : ℕ) ≤ ((167021367/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_798 :
    ((668210859/100000000 : ℚ) : ℝ) ≤ Real.log (798 : ℕ)
      ∧ Real.log (798 : ℕ) ≤ ((33410543/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_799 :
    ((334168047/50000000 : ℚ) : ℝ) ≤ Real.log (799 : ℕ)
      ∧ Real.log (799 : ℕ) ≤ ((133667219/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_800 :
    ((167115293/25000000 : ℚ) : ℝ) ≤ Real.log (800 : ℕ)
      ∧ Real.log (800 : ℕ) ≤ ((668461173/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_801 :
    ((334293047/50000000 : ℚ) : ℝ) ≤ Real.log (801 : ℕ)
      ∧ Real.log (801 : ℕ) ≤ ((133717219/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_802 :
    ((33435543/5000000 : ℚ) : ℝ) ≤ Real.log (802 : ℕ)
      ∧ Real.log (802 : ℕ) ≤ ((668710861/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_803 :
    ((668835471/100000000 : ℚ) : ℝ) ≤ Real.log (803 : ℕ)
      ∧ Real.log (803 : ℕ) ≤ ((41802217/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_804 :
    ((334479963/50000000 : ℚ) : ℝ) ≤ Real.log (804 : ℕ)
      ∧ Real.log (804 : ℕ) ≤ ((668959927/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_805 :
    ((669084227/100000000 : ℚ) : ℝ) ≤ Real.log (805 : ℕ)
      ∧ Real.log (805 : ℕ) ≤ ((167271057/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_806 :
    ((334604187/50000000 : ℚ) : ℝ) ≤ Real.log (806 : ℕ)
      ∧ Real.log (806 : ℕ) ≤ ((5353667/800000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_807 :
    ((334666183/50000000 : ℚ) : ℝ) ≤ Real.log (807 : ℕ)
      ∧ Real.log (807 : ℕ) ≤ ((669332367/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_808 :
    ((133891241/20000000 : ℚ) : ℝ) ≤ Real.log (808 : ℕ)
      ∧ Real.log (808 : ℕ) ≤ ((334728103/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_809 :
    ((669579891/100000000 : ℚ) : ℝ) ≤ Real.log (809 : ℕ)
      ∧ Real.log (809 : ℕ) ≤ ((167394973/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_810 :
    ((2616029/390625 : ℚ) : ℝ) ≤ Real.log (810 : ℕ)
      ∧ Real.log (810 : ℕ) ≤ ((26788137/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_811 :
    ((133965361/20000000 : ℚ) : ℝ) ≤ Real.log (811 : ℕ)
      ∧ Real.log (811 : ℕ) ≤ ((334913403/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_812 :
    ((669950033/100000000 : ℚ) : ℝ) ≤ Real.log (812 : ℕ)
      ∧ Real.log (812 : ℕ) ≤ ((133990007/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_813 :
    ((67007311/10000000 : ℚ) : ℝ) ≤ Real.log (813 : ℕ)
      ∧ Real.log (813 : ℕ) ≤ ((670073111/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_814 :
    ((167549009/25000000 : ℚ) : ℝ) ≤ Real.log (814 : ℕ)
      ∧ Real.log (814 : ℕ) ≤ ((670196037/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_815 :
    ((670318811/100000000 : ℚ) : ℝ) ≤ Real.log (815 : ℕ)
      ∧ Real.log (815 : ℕ) ≤ ((167579703/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_816 :
    ((134088287/20000000 : ℚ) : ℝ) ≤ Real.log (816 : ℕ)
      ∧ Real.log (816 : ℕ) ≤ ((167610359/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_817 :
    ((670563909/100000000 : ℚ) : ℝ) ≤ Real.log (817 : ℕ)
      ∧ Real.log (817 : ℕ) ≤ ((67056391/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_818 :
    ((670686233/100000000 : ℚ) : ℝ) ≤ Real.log (818 : ℕ)
      ∧ Real.log (818 : ℕ) ≤ ((335343117/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_819 :
    ((83851051/12500000 : ℚ) : ℝ) ≤ Real.log (819 : ℕ)
      ∧ Real.log (819 : ℕ) ≤ ((670808409/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_820 :
    ((670930433/100000000 : ℚ) : ℝ) ≤ Real.log (820 : ℕ)
      ∧ Real.log (820 : ℕ) ≤ ((134186087/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_821 :
    ((67105231/10000000 : ℚ) : ℝ) ≤ Real.log (821 : ℕ)
      ∧ Real.log (821 : ℕ) ≤ ((671052311/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_822 :
    ((671174039/100000000 : ℚ) : ℝ) ≤ Real.log (822 : ℕ)
      ∧ Real.log (822 : ℕ) ≤ ((16779351/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_823 :
    ((33564781/5000000 : ℚ) : ℝ) ≤ Real.log (823 : ℕ)
      ∧ Real.log (823 : ℕ) ≤ ((671295621/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_824 :
    ((167854263/25000000 : ℚ) : ℝ) ≤ Real.log (824 : ℕ)
      ∧ Real.log (824 : ℕ) ≤ ((335708527/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_825 :
    ((335769169/50000000 : ℚ) : ℝ) ≤ Real.log (825 : ℕ)
      ∧ Real.log (825 : ℕ) ≤ ((671538339/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_826 :
    ((671659477/100000000 : ℚ) : ℝ) ≤ Real.log (826 : ℕ)
      ∧ Real.log (826 : ℕ) ≤ ((335829739/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_827 :
    ((671780469/100000000 : ℚ) : ℝ) ≤ Real.log (827 : ℕ)
      ∧ Real.log (827 : ℕ) ≤ ((67178047/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_828 :
    ((134380263/20000000 : ℚ) : ℝ) ≤ Real.log (828 : ℕ)
      ∧ Real.log (828 : ℕ) ≤ ((167975329/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_829 :
    ((134404403/20000000 : ℚ) : ℝ) ≤ Real.log (829 : ℕ)
      ∧ Real.log (829 : ℕ) ≤ ((2625086/390625 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_830 :
    ((67214257/10000000 : ℚ) : ℝ) ≤ Real.log (830 : ℕ)
      ∧ Real.log (830 : ℕ) ≤ ((672142571/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_831 :
    ((672262979/100000000 : ℚ) : ℝ) ≤ Real.log (831 : ℕ)
      ∧ Real.log (831 : ℕ) ≤ ((33613149/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_832 :
    ((168095811/25000000 : ℚ) : ℝ) ≤ Real.log (832 : ℕ)
      ∧ Real.log (832 : ℕ) ≤ ((134476649/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_833 :
    ((168125841/25000000 : ℚ) : ℝ) ≤ Real.log (833 : ℕ)
      ∧ Real.log (833 : ℕ) ≤ ((134500673/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_834 :
    ((33631167/5000000 : ℚ) : ℝ) ≤ Real.log (834 : ℕ)
      ∧ Real.log (834 : ℕ) ≤ ((672623341/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_835 :
    ((168185793/25000000 : ℚ) : ℝ) ≤ Real.log (835 : ℕ)
      ∧ Real.log (835 : ℕ) ≤ ((672743173/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_836 :
    ((672862861/100000000 : ℚ) : ℝ) ≤ Real.log (836 : ℕ)
      ∧ Real.log (836 : ℕ) ≤ ((336431431/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_837 :
    ((672982407/100000000 : ℚ) : ℝ) ≤ Real.log (837 : ℕ)
      ∧ Real.log (837 : ℕ) ≤ ((84122801/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_838 :
    ((67310181/10000000 : ℚ) : ℝ) ≤ Real.log (838 : ℕ)
      ∧ Real.log (838 : ℕ) ≤ ((673101811/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_839 :
    ((67322107/10000000 : ℚ) : ℝ) ≤ Real.log (839 : ℕ)
      ∧ Real.log (839 : ℕ) ≤ ((673221071/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_840 :
    ((673340189/100000000 : ℚ) : ℝ) ≤ Real.log (840 : ℕ)
      ∧ Real.log (840 : ℕ) ≤ ((67334019/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_841 :
    ((134691833/20000000 : ℚ) : ℝ) ≤ Real.log (841 : ℕ)
      ∧ Real.log (841 : ℕ) ≤ ((673459167/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_842 :
    ((673578001/100000000 : ℚ) : ℝ) ≤ Real.log (842 : ℕ)
      ∧ Real.log (842 : ℕ) ≤ ((336789001/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_843 :
    ((134739339/20000000 : ℚ) : ℝ) ≤ Real.log (843 : ℕ)
      ∧ Real.log (843 : ℕ) ≤ ((84212087/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_844 :
    ((673815249/100000000 : ℚ) : ℝ) ≤ Real.log (844 : ℕ)
      ∧ Real.log (844 : ℕ) ≤ ((2695261/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_845 :
    ((336966831/50000000 : ℚ) : ℝ) ≤ Real.log (845 : ℕ)
      ∧ Real.log (845 : ℕ) ≤ ((673933663/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_846 :
    ((134810387/20000000 : ℚ) : ℝ) ≤ Real.log (846 : ℕ)
      ∧ Real.log (846 : ℕ) ≤ ((674051937/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_847 :
    ((674170069/100000000 : ℚ) : ℝ) ≤ Real.log (847 : ℕ)
      ∧ Real.log (847 : ℕ) ≤ ((67417007/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_848 :
    ((674288063/100000000 : ℚ) : ℝ) ≤ Real.log (848 : ℕ)
      ∧ Real.log (848 : ℕ) ≤ ((10535751/1562500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_849 :
    ((337202959/50000000 : ℚ) : ℝ) ≤ Real.log (849 : ℕ)
      ∧ Real.log (849 : ℕ) ≤ ((674405919/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_850 :
    ((337261817/50000000 : ℚ) : ℝ) ≤ Real.log (850 : ℕ)
      ∧ Real.log (850 : ℕ) ≤ ((134904727/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_851 :
    ((168660303/25000000 : ℚ) : ℝ) ≤ Real.log (851 : ℕ)
      ∧ Real.log (851 : ℕ) ≤ ((674641213/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_852 :
    ((168689663/25000000 : ℚ) : ℝ) ≤ Real.log (852 : ℕ)
      ∧ Real.log (852 : ℕ) ≤ ((674758653/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_853 :
    ((337437977/50000000 : ℚ) : ℝ) ≤ Real.log (853 : ℕ)
      ∧ Real.log (853 : ℕ) ≤ ((134975191/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_854 :
    ((674993119/100000000 : ℚ) : ℝ) ≤ Real.log (854 : ℕ)
      ∧ Real.log (854 : ℕ) ≤ ((4218707/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_855 :
    ((337555073/50000000 : ℚ) : ℝ) ≤ Real.log (855 : ℕ)
      ∧ Real.log (855 : ℕ) ≤ ((675110147/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_856 :
    ((675227037/100000000 : ℚ) : ℝ) ≤ Real.log (856 : ℕ)
      ∧ Real.log (856 : ℕ) ≤ ((337613519/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_857 :
    ((675343791/100000000 : ℚ) : ℝ) ≤ Real.log (857 : ℕ)
      ∧ Real.log (857 : ℕ) ≤ ((42208987/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_858 :
    ((675460409/100000000 : ℚ) : ℝ) ≤ Real.log (858 : ℕ)
      ∧ Real.log (858 : ℕ) ≤ ((67546041/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_859 :
    ((168894223/25000000 : ℚ) : ℝ) ≤ Real.log (859 : ℕ)
      ∧ Real.log (859 : ℕ) ≤ ((675576893/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_860 :
    ((337846619/50000000 : ℚ) : ℝ) ≤ Real.log (860 : ℕ)
      ∧ Real.log (860 : ℕ) ≤ ((675693239/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_861 :
    ((13516189/2000000 : ℚ) : ℝ) ≤ Real.log (861 : ℕ)
      ∧ Real.log (861 : ℕ) ≤ ((675809451/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_862 :
    ((675925527/100000000 : ℚ) : ℝ) ≤ Real.log (862 : ℕ)
      ∧ Real.log (862 : ℕ) ≤ ((84490691/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_863 :
    ((676041469/100000000 : ℚ) : ℝ) ≤ Real.log (863 : ℕ)
      ∧ Real.log (863 : ℕ) ≤ ((67604147/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_864 :
    ((169039319/25000000 : ℚ) : ℝ) ≤ Real.log (864 : ℕ)
      ∧ Real.log (864 : ℕ) ≤ ((676157277/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_865 :
    ((13525459/2000000 : ℚ) : ℝ) ≤ Real.log (865 : ℕ)
      ∧ Real.log (865 : ℕ) ≤ ((676272951/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_866 :
    ((67638849/10000000 : ℚ) : ℝ) ≤ Real.log (866 : ℕ)
      ∧ Real.log (866 : ℕ) ≤ ((676388491/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_867 :
    ((676503897/100000000 : ℚ) : ℝ) ≤ Real.log (867 : ℕ)
      ∧ Real.log (867 : ℕ) ≤ ((338251949/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_868 :
    ((676619171/100000000 : ℚ) : ℝ) ≤ Real.log (868 : ℕ)
      ∧ Real.log (868 : ℕ) ≤ ((169154793/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_869 :
    ((84591789/12500000 : ℚ) : ℝ) ≤ Real.log (869 : ℕ)
      ∧ Real.log (869 : ℕ) ≤ ((676734313/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_870 :
    ((676849321/100000000 : ℚ) : ℝ) ≤ Real.log (870 : ℕ)
      ∧ Real.log (870 : ℕ) ≤ ((338424661/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_871 :
    ((676964197/100000000 : ℚ) : ℝ) ≤ Real.log (871 : ℕ)
      ∧ Real.log (871 : ℕ) ≤ ((338482099/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_872 :
    ((338539471/50000000 : ℚ) : ℝ) ≤ Real.log (872 : ℕ)
      ∧ Real.log (872 : ℕ) ≤ ((677078943/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_873 :
    ((135438711/20000000 : ℚ) : ℝ) ≤ Real.log (873 : ℕ)
      ∧ Real.log (873 : ℕ) ≤ ((169298389/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_874 :
    ((677308037/100000000 : ℚ) : ℝ) ≤ Real.log (874 : ℕ)
      ∧ Real.log (874 : ℕ) ≤ ((338654019/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_875 :
    ((169355597/25000000 : ℚ) : ℝ) ≤ Real.log (875 : ℕ)
      ∧ Real.log (875 : ℕ) ≤ ((677422389/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_876 :
    ((677536609/100000000 : ℚ) : ℝ) ≤ Real.log (876 : ℕ)
      ∧ Real.log (876 : ℕ) ≤ ((67753661/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_877 :
    ((677650699/100000000 : ℚ) : ℝ) ≤ Real.log (877 : ℕ)
      ∧ Real.log (877 : ℕ) ≤ ((6776507/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_878 :
    ((677764659/100000000 : ℚ) : ℝ) ≤ Real.log (878 : ℕ)
      ∧ Real.log (878 : ℕ) ≤ ((33888233/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_879 :
    ((677878489/100000000 : ℚ) : ℝ) ≤ Real.log (879 : ℕ)
      ∧ Real.log (879 : ℕ) ≤ ((67787849/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_880 :
    ((67799219/10000000 : ℚ) : ℝ) ≤ Real.log (880 : ℕ)
      ∧ Real.log (880 : ℕ) ≤ ((677992191/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_881 :
    ((339052881/50000000 : ℚ) : ℝ) ≤ Real.log (881 : ℕ)
      ∧ Real.log (881 : ℕ) ≤ ((678105763/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_882 :
    ((135643841/20000000 : ℚ) : ℝ) ≤ Real.log (882 : ℕ)
      ∧ Real.log (882 : ℕ) ≤ ((339109603/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_883 :
    ((16958313/2500000 : ℚ) : ℝ) ≤ Real.log (883 : ℕ)
      ∧ Real.log (883 : ℕ) ≤ ((678332521/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_884 :
    ((339222853/50000000 : ℚ) : ℝ) ≤ Real.log (884 : ℕ)
      ∧ Real.log (884 : ℕ) ≤ ((678445707/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_885 :
    ((169639691/25000000 : ℚ) : ℝ) ≤ Real.log (885 : ℕ)
      ∧ Real.log (885 : ℕ) ≤ ((135711753/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_886 :
    ((135734339/20000000 : ℚ) : ℝ) ≤ Real.log (886 : ℕ)
      ∧ Real.log (886 : ℕ) ≤ ((42416981/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_887 :
    ((339392249/50000000 : ℚ) : ℝ) ≤ Real.log (887 : ℕ)
      ∧ Real.log (887 : ℕ) ≤ ((678784499/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_888 :
    ((339448587/50000000 : ℚ) : ℝ) ≤ Real.log (888 : ℕ)
      ∧ Real.log (888 : ℕ) ≤ ((27155887/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_889 :
    ((679009723/100000000 : ℚ) : ℝ) ≤ Real.log (889 : ℕ)
      ∧ Real.log (889 : ℕ) ≤ ((169752431/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_890 :
    ((339561073/50000000 : ℚ) : ℝ) ≤ Real.log (890 : ℕ)
      ∧ Real.log (890 : ℕ) ≤ ((679122147/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_891 :
    ((339617221/50000000 : ℚ) : ℝ) ≤ Real.log (891 : ℕ)
      ∧ Real.log (891 : ℕ) ≤ ((679234443/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_892 :
    ((679346613/100000000 : ℚ) : ℝ) ≤ Real.log (892 : ℕ)
      ∧ Real.log (892 : ℕ) ≤ ((339673307/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_893 :
    ((339729329/50000000 : ℚ) : ℝ) ≤ Real.log (893 : ℕ)
      ∧ Real.log (893 : ℕ) ≤ ((679458659/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_894 :
    ((679570577/100000000 : ℚ) : ℝ) ≤ Real.log (894 : ℕ)
      ∧ Real.log (894 : ℕ) ≤ ((339785289/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_895 :
    ((679682371/100000000 : ℚ) : ℝ) ≤ Real.log (895 : ℕ)
      ∧ Real.log (895 : ℕ) ≤ ((169920593/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_896 :
    ((679794041/100000000 : ℚ) : ℝ) ≤ Real.log (896 : ℕ)
      ∧ Real.log (896 : ℕ) ≤ ((339897021/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_897 :
    ((339952793/50000000 : ℚ) : ℝ) ≤ Real.log (897 : ℕ)
      ∧ Real.log (897 : ℕ) ≤ ((679905587/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_898 :
    ((340008503/50000000 : ℚ) : ℝ) ≤ Real.log (898 : ℕ)
      ∧ Real.log (898 : ℕ) ≤ ((680017007/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_899 :
    ((680128303/100000000 : ℚ) : ℝ) ≤ Real.log (899 : ℕ)
      ∧ Real.log (899 : ℕ) ≤ ((42508019/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_900 :
    ((170059869/25000000 : ℚ) : ℝ) ≤ Real.log (900 : ℕ)
      ∧ Real.log (900 : ℕ) ≤ ((680239477/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_901 :
    ((27214021/4000000 : ℚ) : ℝ) ≤ Real.log (901 : ℕ)
      ∧ Real.log (901 : ℕ) ≤ ((340175263/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_902 :
    ((680461451/100000000 : ℚ) : ℝ) ≤ Real.log (902 : ℕ)
      ∧ Real.log (902 : ℕ) ≤ ((680461453/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_903 :
    ((136114451/20000000 : ℚ) : ℝ) ≤ Real.log (903 : ℕ)
      ∧ Real.log (903 : ℕ) ≤ ((21267883/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_904 :
    ((85085367/12500000 : ℚ) : ℝ) ≤ Real.log (904 : ℕ)
      ∧ Real.log (904 : ℕ) ≤ ((680682937/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_905 :
    ((340396747/50000000 : ℚ) : ℝ) ≤ Real.log (905 : ℕ)
      ∧ Real.log (905 : ℕ) ≤ ((136158699/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_906 :
    ((68090393/10000000 : ℚ) : ℝ) ≤ Real.log (906 : ℕ)
      ∧ Real.log (906 : ℕ) ≤ ((680903931/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_907 :
    ((170253561/25000000 : ℚ) : ℝ) ≤ Real.log (907 : ℕ)
      ∧ Real.log (907 : ℕ) ≤ ((340507123/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_908 :
    ((681124437/100000000 : ℚ) : ℝ) ≤ Real.log (908 : ℕ)
      ∧ Real.log (908 : ℕ) ≤ ((340562219/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_909 :
    ((681234509/100000000 : ℚ) : ℝ) ≤ Real.log (909 : ℕ)
      ∧ Real.log (909 : ℕ) ≤ ((68123451/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_910 :
    ((681344459/100000000 : ℚ) : ℝ) ≤ Real.log (910 : ℕ)
      ∧ Real.log (910 : ℕ) ≤ ((34067223/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_911 :
    ((681454289/100000000 : ℚ) : ℝ) ≤ Real.log (911 : ℕ)
      ∧ Real.log (911 : ℕ) ≤ ((68145429/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_912 :
    ((340781999/50000000 : ℚ) : ℝ) ≤ Real.log (912 : ℕ)
      ∧ Real.log (912 : ℕ) ≤ ((170391/25000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_913 :
    ((170418397/25000000 : ℚ) : ℝ) ≤ Real.log (913 : ℕ)
      ∧ Real.log (913 : ℕ) ≤ ((681673589/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_914 :
    ((681783057/100000000 : ℚ) : ℝ) ≤ Real.log (914 : ℕ)
      ∧ Real.log (914 : ℕ) ≤ ((340891529/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_915 :
    ((340946203/50000000 : ℚ) : ℝ) ≤ Real.log (915 : ℕ)
      ∧ Real.log (915 : ℕ) ≤ ((681892407/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_916 :
    ((170500409/25000000 : ℚ) : ℝ) ≤ Real.log (916 : ℕ)
      ∧ Real.log (916 : ℕ) ≤ ((682001637/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_917 :
    ((682110747/100000000 : ℚ) : ℝ) ≤ Real.log (917 : ℕ)
      ∧ Real.log (917 : ℕ) ≤ ((170527687/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_918 :
    ((682219739/100000000 : ℚ) : ℝ) ≤ Real.log (918 : ℕ)
      ∧ Real.log (918 : ℕ) ≤ ((34110987/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_919 :
    ((170582153/25000000 : ℚ) : ℝ) ≤ Real.log (919 : ℕ)
      ∧ Real.log (919 : ℕ) ≤ ((682328613/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_920 :
    ((341218683/50000000 : ℚ) : ℝ) ≤ Real.log (920 : ℕ)
      ∧ Real.log (920 : ℕ) ≤ ((85304671/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_921 :
    ((682546003/100000000 : ℚ) : ℝ) ≤ Real.log (921 : ℕ)
      ∧ Real.log (921 : ℕ) ≤ ((170636501/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_922 :
    ((341327261/50000000 : ℚ) : ℝ) ≤ Real.log (922 : ℕ)
      ∧ Real.log (922 : ℕ) ≤ ((682654523/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_923 :
    ((682762923/100000000 : ℚ) : ℝ) ≤ Real.log (923 : ℕ)
      ∧ Real.log (923 : ℕ) ≤ ((170690731/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_924 :
    ((682871207/100000000 : ℚ) : ℝ) ≤ Real.log (924 : ℕ)
      ∧ Real.log (924 : ℕ) ≤ ((85358901/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_925 :
    ((682979373/100000000 : ℚ) : ℝ) ≤ Real.log (925 : ℕ)
      ∧ Real.log (925 : ℕ) ≤ ((341489687/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_926 :
    ((683087423/100000000 : ℚ) : ℝ) ≤ Real.log (926 : ℕ)
      ∧ Real.log (926 : ℕ) ≤ ((10673241/1562500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_927 :
    ((170798839/25000000 : ℚ) : ℝ) ≤ Real.log (927 : ℕ)
      ∧ Real.log (927 : ℕ) ≤ ((683195357/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_928 :
    ((683303173/100000000 : ℚ) : ℝ) ≤ Real.log (928 : ℕ)
      ∧ Real.log (928 : ℕ) ≤ ((341651587/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_929 :
    ((683410873/100000000 : ℚ) : ℝ) ≤ Real.log (929 : ℕ)
      ∧ Real.log (929 : ℕ) ≤ ((341705437/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_930 :
    ((341759229/50000000 : ℚ) : ℝ) ≤ Real.log (930 : ℕ)
      ∧ Real.log (930 : ℕ) ≤ ((683518459/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_931 :
    ((683625927/100000000 : ℚ) : ℝ) ≤ Real.log (931 : ℕ)
      ∧ Real.log (931 : ℕ) ≤ ((85453241/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_932 :
    ((683733281/100000000 : ℚ) : ℝ) ≤ Real.log (932 : ℕ)
      ∧ Real.log (932 : ℕ) ≤ ((341866641/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_933 :
    ((17096013/2500000 : ℚ) : ℝ) ≤ Real.log (933 : ℕ)
      ∧ Real.log (933 : ℕ) ≤ ((683840521/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_934 :
    ((683947643/100000000 : ℚ) : ℝ) ≤ Real.log (934 : ℕ)
      ∧ Real.log (934 : ℕ) ≤ ((170986911/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_935 :
    ((171013663/25000000 : ℚ) : ℝ) ≤ Real.log (935 : ℕ)
      ∧ Real.log (935 : ℕ) ≤ ((684054653/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_936 :
    ((684161547/100000000 : ℚ) : ℝ) ≤ Real.log (936 : ℕ)
      ∧ Real.log (936 : ℕ) ≤ ((171040387/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_937 :
    ((85533541/12500000 : ℚ) : ℝ) ≤ Real.log (937 : ℕ)
      ∧ Real.log (937 : ℕ) ≤ ((684268329/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_938 :
    ((342187497/50000000 : ℚ) : ℝ) ≤ Real.log (938 : ℕ)
      ∧ Real.log (938 : ℕ) ≤ ((136874999/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_939 :
    ((684481547/100000000 : ℚ) : ℝ) ≤ Real.log (939 : ℕ)
      ∧ Real.log (939 : ℕ) ≤ ((171120387/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_940 :
    ((684587987/100000000 : ℚ) : ℝ) ≤ Real.log (940 : ℕ)
      ∧ Real.log (940 : ℕ) ≤ ((171146997/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_941 :
    ((684694313/100000000 : ℚ) : ℝ) ≤ Real.log (941 : ℕ)
      ∧ Real.log (941 : ℕ) ≤ ((342347157/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_942 :
    ((684800527/100000000 : ℚ) : ℝ) ≤ Real.log (942 : ℕ)
      ∧ Real.log (942 : ℕ) ≤ ((42800033/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_943 :
    ((171226657/25000000 : ℚ) : ℝ) ≤ Real.log (943 : ℕ)
      ∧ Real.log (943 : ℕ) ≤ ((684906629/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_944 :
    ((85626577/12500000 : ℚ) : ℝ) ≤ Real.log (944 : ℕ)
      ∧ Real.log (944 : ℕ) ≤ ((685012617/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_945 :
    ((171279623/25000000 : ℚ) : ℝ) ≤ Real.log (945 : ℕ)
      ∧ Real.log (945 : ℕ) ≤ ((685118493/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_946 :
    ((10706629/1562500 : ℚ) : ℝ) ≤ Real.log (946 : ℕ)
      ∧ Real.log (946 : ℕ) ≤ ((685224257/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_947 :
    ((685329909/100000000 : ℚ) : ℝ) ≤ Real.log (947 : ℕ)
      ∧ Real.log (947 : ℕ) ≤ ((68532991/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_948 :
    ((13708709/2000000 : ℚ) : ℝ) ≤ Real.log (948 : ℕ)
      ∧ Real.log (948 : ℕ) ≤ ((685435451/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_949 :
    ((685540879/100000000 : ℚ) : ℝ) ≤ Real.log (949 : ℕ)
      ∧ Real.log (949 : ℕ) ≤ ((8569261/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_950 :
    ((342823099/50000000 : ℚ) : ℝ) ≤ Real.log (950 : ℕ)
      ∧ Real.log (950 : ℕ) ≤ ((685646199/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_951 :
    ((342875703/50000000 : ℚ) : ℝ) ≤ Real.log (951 : ℕ)
      ∧ Real.log (951 : ℕ) ≤ ((685751407/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_952 :
    ((685856503/100000000 : ℚ) : ℝ) ≤ Real.log (952 : ℕ)
      ∧ Real.log (952 : ℕ) ≤ ((85732063/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_953 :
    ((68596149/10000000 : ℚ) : ℝ) ≤ Real.log (953 : ℕ)
      ∧ Real.log (953 : ℕ) ≤ ((685961491/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_954 :
    ((686066367/100000000 : ℚ) : ℝ) ≤ Real.log (954 : ℕ)
      ∧ Real.log (954 : ℕ) ≤ ((10719787/1562500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_955 :
    ((343085567/50000000 : ℚ) : ℝ) ≤ Real.log (955 : ℕ)
      ∧ Real.log (955 : ℕ) ≤ ((137234227/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_956 :
    ((686275791/100000000 : ℚ) : ℝ) ≤ Real.log (956 : ℕ)
      ∧ Real.log (956 : ℕ) ≤ ((42892237/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_957 :
    ((686380339/100000000 : ℚ) : ℝ) ≤ Real.log (957 : ℕ)
      ∧ Real.log (957 : ℕ) ≤ ((34319017/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_958 :
    ((686484777/100000000 : ℚ) : ℝ) ≤ Real.log (958 : ℕ)
      ∧ Real.log (958 : ℕ) ≤ ((343242389/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_959 :
    ((686589107/100000000 : ℚ) : ℝ) ≤ Real.log (959 : ℕ)
      ∧ Real.log (959 : ℕ) ≤ ((171647277/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_960 :
    ((42918333/6250000 : ℚ) : ℝ) ≤ Real.log (960 : ℕ)
      ∧ Real.log (960 : ℕ) ≤ ((686693329/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_961 :
    ((1073121/156250 : ℚ) : ℝ) ≤ Real.log (961 : ℕ)
      ∧ Real.log (961 : ℕ) ≤ ((686797441/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_962 :
    ((137380289/20000000 : ℚ) : ℝ) ≤ Real.log (962 : ℕ)
      ∧ Real.log (962 : ℕ) ≤ ((343450723/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_963 :
    ((687005341/100000000 : ℚ) : ℝ) ≤ Real.log (963 : ℕ)
      ∧ Real.log (963 : ℕ) ≤ ((343502671/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_964 :
    ((687109129/100000000 : ℚ) : ℝ) ≤ Real.log (964 : ℕ)
      ∧ Real.log (964 : ℕ) ≤ ((68710913/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_965 :
    ((68721281/10000000 : ℚ) : ℝ) ≤ Real.log (965 : ℕ)
      ∧ Real.log (965 : ℕ) ≤ ((687212811/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_966 :
    ((687316383/100000000 : ℚ) : ℝ) ≤ Real.log (966 : ℕ)
      ∧ Real.log (966 : ℕ) ≤ ((21478637/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_967 :
    ((687419849/100000000 : ℚ) : ℝ) ≤ Real.log (967 : ℕ)
      ∧ Real.log (967 : ℕ) ≤ ((13748397/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_968 :
    ((85940401/12500000 : ℚ) : ℝ) ≤ Real.log (968 : ℕ)
      ∧ Real.log (968 : ℕ) ≤ ((687523209/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_969 :
    ((687626461/100000000 : ℚ) : ℝ) ≤ Real.log (969 : ℕ)
      ∧ Real.log (969 : ℕ) ≤ ((343813231/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_970 :
    ((687729607/100000000 : ℚ) : ℝ) ≤ Real.log (970 : ℕ)
      ∧ Real.log (970 : ℕ) ≤ ((85966201/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_971 :
    ((343916323/50000000 : ℚ) : ℝ) ≤ Real.log (971 : ℕ)
      ∧ Real.log (971 : ℕ) ≤ ((687832647/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_972 :
    ((34396779/5000000 : ℚ) : ℝ) ≤ Real.log (972 : ℕ)
      ∧ Real.log (972 : ℕ) ≤ ((687935581/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_973 :
    ((86004801/12500000 : ℚ) : ℝ) ≤ Real.log (973 : ℕ)
      ∧ Real.log (973 : ℕ) ≤ ((688038409/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_974 :
    ((68814113/10000000 : ℚ) : ℝ) ≤ Real.log (974 : ℕ)
      ∧ Real.log (974 : ℕ) ≤ ((688141131/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_975 :
    ((688243747/100000000 : ℚ) : ℝ) ≤ Real.log (975 : ℕ)
      ∧ Real.log (975 : ℕ) ≤ ((172060937/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_976 :
    ((344173129/50000000 : ℚ) : ℝ) ≤ Real.log (976 : ℕ)
      ∧ Real.log (976 : ℕ) ≤ ((688346259/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_977 :
    ((137689733/20000000 : ℚ) : ℝ) ≤ Real.log (977 : ℕ)
      ∧ Real.log (977 : ℕ) ≤ ((344224333/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_978 :
    ((344275483/50000000 : ℚ) : ℝ) ≤ Real.log (978 : ℕ)
      ∧ Real.log (978 : ℕ) ≤ ((86068871/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_979 :
    ((172163291/25000000 : ℚ) : ℝ) ≤ Real.log (979 : ℕ)
      ∧ Real.log (979 : ℕ) ≤ ((137730633/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_980 :
    ((688755257/100000000 : ℚ) : ℝ) ≤ Real.log (980 : ℕ)
      ∧ Real.log (980 : ℕ) ≤ ((344377629/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_981 :
    ((137771449/20000000 : ℚ) : ℝ) ≤ Real.log (981 : ℕ)
      ∧ Real.log (981 : ℕ) ≤ ((344428623/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_982 :
    ((68895913/10000000 : ℚ) : ℝ) ≤ Real.log (982 : ℕ)
      ∧ Real.log (982 : ℕ) ≤ ((688959131/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_983 :
    ((689060911/100000000 : ℚ) : ℝ) ≤ Real.log (983 : ℕ)
      ∧ Real.log (983 : ℕ) ≤ ((689060913/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_984 :
    ((689162589/100000000 : ℚ) : ℝ) ≤ Real.log (984 : ℕ)
      ∧ Real.log (984 : ℕ) ≤ ((68916259/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_985 :
    ((172316041/25000000 : ℚ) : ℝ) ≤ Real.log (985 : ℕ)
      ∧ Real.log (985 : ℕ) ≤ ((137852833/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_986 :
    ((137873127/20000000 : ℚ) : ℝ) ≤ Real.log (986 : ℕ)
      ∧ Real.log (986 : ℕ) ≤ ((172341409/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_987 :
    ((689467003/100000000 : ℚ) : ℝ) ≤ Real.log (987 : ℕ)
      ∧ Real.log (987 : ℕ) ≤ ((172366751/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_988 :
    ((689568269/100000000 : ℚ) : ℝ) ≤ Real.log (988 : ℕ)
      ∧ Real.log (988 : ℕ) ≤ ((68956827/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_989 :
    ((689669433/100000000 : ℚ) : ℝ) ≤ Real.log (989 : ℕ)
      ∧ Real.log (989 : ℕ) ≤ ((344834717/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_990 :
    ((344885247/50000000 : ℚ) : ℝ) ≤ Real.log (990 : ℕ)
      ∧ Real.log (990 : ℕ) ≤ ((137954099/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_991 :
    ((689871453/100000000 : ℚ) : ℝ) ≤ Real.log (991 : ℕ)
      ∧ Real.log (991 : ℕ) ≤ ((344935727/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_992 :
    ((68997231/10000000 : ℚ) : ℝ) ≤ Real.log (992 : ℕ)
      ∧ Real.log (992 : ℕ) ≤ ((689972311/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_993 :
    ((345036533/50000000 : ℚ) : ℝ) ≤ Real.log (993 : ℕ)
      ∧ Real.log (993 : ℕ) ≤ ((690073067/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_994 :
    ((17254343/2500000 : ℚ) : ℝ) ≤ Real.log (994 : ℕ)
      ∧ Real.log (994 : ℕ) ≤ ((690173721/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_995 :
    ((690274273/100000000 : ℚ) : ℝ) ≤ Real.log (995 : ℕ)
      ∧ Real.log (995 : ℕ) ≤ ((345137137/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_996 :
    ((27614989/4000000 : ℚ) : ℝ) ≤ Real.log (996 : ℕ)
      ∧ Real.log (996 : ℕ) ≤ ((345187363/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_997 :
    ((172618769/25000000 : ℚ) : ℝ) ≤ Real.log (997 : ℕ)
      ∧ Real.log (997 : ℕ) ≤ ((345237539/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_998 :
    ((690575327/100000000 : ℚ) : ℝ) ≤ Real.log (998 : ℕ)
      ∧ Real.log (998 : ℕ) ≤ ((21580479/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_999 :
    ((690675477/100000000 : ℚ) : ℝ) ≤ Real.log (999 : ℕ)
      ∧ Real.log (999 : ℕ) ≤ ((345337739/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1000 :
    ((690775527/100000000 : ℚ) : ℝ) ≤ Real.log (1000 : ℕ)
      ∧ Real.log (1000 : ℕ) ≤ ((86346941/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1001 :
    ((690875477/100000000 : ℚ) : ℝ) ≤ Real.log (1001 : ℕ)
      ∧ Real.log (1001 : ℕ) ≤ ((345437739/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1002 :
    ((21592979/3125000 : ℚ) : ℝ) ≤ Real.log (1002 : ℕ)
      ∧ Real.log (1002 : ℕ) ≤ ((690975329/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1003 :
    ((345537539/50000000 : ℚ) : ℝ) ≤ Real.log (1003 : ℕ)
      ∧ Real.log (1003 : ℕ) ≤ ((691075079/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1004 :
    ((691174729/100000000 : ℚ) : ℝ) ≤ Real.log (1004 : ℕ)
      ∧ Real.log (1004 : ℕ) ≤ ((691174731/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1005 :
    ((345637141/50000000 : ℚ) : ℝ) ≤ Real.log (1005 : ℕ)
      ∧ Real.log (1005 : ℕ) ≤ ((691274283/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1006 :
    ((138274747/20000000 : ℚ) : ℝ) ≤ Real.log (1006 : ℕ)
      ∧ Real.log (1006 : ℕ) ≤ ((86421717/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1007 :
    ((691473089/100000000 : ℚ) : ℝ) ≤ Real.log (1007 : ℕ)
      ∧ Real.log (1007 : ℕ) ≤ ((69147309/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1008 :
    ((86446543/12500000 : ℚ) : ℝ) ≤ Real.log (1008 : ℕ)
      ∧ Real.log (1008 : ℕ) ≤ ((138314469/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1009 :
    ((691671501/100000000 : ℚ) : ℝ) ≤ Real.log (1009 : ℕ)
      ∧ Real.log (1009 : ℕ) ≤ ((691671503/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1010 :
    ((2161783/312500 : ℚ) : ℝ) ≤ Real.log (1010 : ℕ)
      ∧ Real.log (1010 : ℕ) ≤ ((345885281/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1011 :
    ((691869521/100000000 : ℚ) : ℝ) ≤ Real.log (1011 : ℕ)
      ∧ Real.log (1011 : ℕ) ≤ ((345934761/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1012 :
    ((5406003/781250 : ℚ) : ℝ) ≤ Real.log (1012 : ℕ)
      ∧ Real.log (1012 : ℕ) ≤ ((345984193/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1013 :
    ((13841343/2000000 : ℚ) : ℝ) ≤ Real.log (1013 : ℕ)
      ∧ Real.log (1013 : ℕ) ≤ ((692067151/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1014 :
    ((346082909/50000000 : ℚ) : ℝ) ≤ Real.log (1014 : ℕ)
      ∧ Real.log (1014 : ℕ) ≤ ((692165819/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1015 :
    ((692264389/100000000 : ℚ) : ℝ) ≤ Real.log (1015 : ℕ)
      ∧ Real.log (1015 : ℕ) ≤ ((69226439/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1016 :
    ((346181431/50000000 : ℚ) : ℝ) ≤ Real.log (1016 : ℕ)
      ∧ Real.log (1016 : ℕ) ≤ ((692362863/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1017 :
    ((692461239/100000000 : ℚ) : ℝ) ≤ Real.log (1017 : ℕ)
      ∧ Real.log (1017 : ℕ) ≤ ((17311531/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1018 :
    ((692559519/100000000 : ℚ) : ℝ) ≤ Real.log (1018 : ℕ)
      ∧ Real.log (1018 : ℕ) ≤ ((4328497/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1019 :
    ((692657703/100000000 : ℚ) : ℝ) ≤ Real.log (1019 : ℕ)
      ∧ Real.log (1019 : ℕ) ≤ ((86582213/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1020 :
    ((69275579/10000000 : ℚ) : ℝ) ≤ Real.log (1020 : ℕ)
      ∧ Real.log (1020 : ℕ) ≤ ((692755791/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1021 :
    ((692853781/100000000 : ℚ) : ℝ) ≤ Real.log (1021 : ℕ)
      ∧ Real.log (1021 : ℕ) ≤ ((346426891/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1022 :
    ((692951677/100000000 : ℚ) : ℝ) ≤ Real.log (1022 : ℕ)
      ∧ Real.log (1022 : ℕ) ≤ ((346475839/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1023 :
    ((173262369/25000000 : ℚ) : ℝ) ≤ Real.log (1023 : ℕ)
      ∧ Real.log (1023 : ℕ) ≤ ((693049477/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1024 :
    ((34657359/5000000 : ℚ) : ℝ) ≤ Real.log (1024 : ℕ)
      ∧ Real.log (1024 : ℕ) ≤ ((693147181/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1025 :
    ((693244789/100000000 : ℚ) : ℝ) ≤ Real.log (1025 : ℕ)
      ∧ Real.log (1025 : ℕ) ≤ ((69324479/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1026 :
    ((346671151/50000000 : ℚ) : ℝ) ≤ Real.log (1026 : ℕ)
      ∧ Real.log (1026 : ℕ) ≤ ((693342303/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1027 :
    ((17335993/2500000 : ℚ) : ℝ) ≤ Real.log (1027 : ℕ)
      ∧ Real.log (1027 : ℕ) ≤ ((346719861/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1028 :
    ((173384261/25000000 : ℚ) : ℝ) ≤ Real.log (1028 : ℕ)
      ∧ Real.log (1028 : ℕ) ≤ ((138707409/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1029 :
    ((693634273/100000000 : ℚ) : ℝ) ≤ Real.log (1029 : ℕ)
      ∧ Real.log (1029 : ℕ) ≤ ((346817137/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1030 :
    ((43358213/6250000 : ℚ) : ℝ) ≤ Real.log (1030 : ℕ)
      ∧ Real.log (1030 : ℕ) ≤ ((693731409/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1031 :
    ((21682139/3125000 : ℚ) : ℝ) ≤ Real.log (1031 : ℕ)
      ∧ Real.log (1031 : ℕ) ≤ ((693828449/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1032 :
    ((346962697/50000000 : ℚ) : ℝ) ≤ Real.log (1032 : ℕ)
      ∧ Real.log (1032 : ℕ) ≤ ((138785079/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1033 :
    ((347011123/50000000 : ℚ) : ℝ) ≤ Real.log (1033 : ℕ)
      ∧ Real.log (1033 : ℕ) ≤ ((694022247/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1034 :
    ((138823801/20000000 : ℚ) : ℝ) ≤ Real.log (1034 : ℕ)
      ∧ Real.log (1034 : ℕ) ≤ ((347059503/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1035 :
    ((69421567/10000000 : ℚ) : ℝ) ≤ Real.log (1035 : ℕ)
      ∧ Real.log (1035 : ℕ) ≤ ((694215671/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1036 :
    ((347156121/50000000 : ℚ) : ℝ) ≤ Real.log (1036 : ℕ)
      ∧ Real.log (1036 : ℕ) ≤ ((694312243/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1037 :
    ((8680109/1250000 : ℚ) : ℝ) ≤ Real.log (1037 : ℕ)
      ∧ Real.log (1037 : ℕ) ≤ ((694408721/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1038 :
    ((347252553/50000000 : ℚ) : ℝ) ≤ Real.log (1038 : ℕ)
      ∧ Real.log (1038 : ℕ) ≤ ((694505107/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1039 :
    ((694601399/100000000 : ℚ) : ℝ) ≤ Real.log (1039 : ℕ)
      ∧ Real.log (1039 : ℕ) ≤ ((3473007/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1040 :
    ((694697599/100000000 : ℚ) : ℝ) ≤ Real.log (1040 : ℕ)
      ∧ Real.log (1040 : ℕ) ≤ ((217093/31250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1041 :
    ((347396853/50000000 : ℚ) : ℝ) ≤ Real.log (1041 : ℕ)
      ∧ Real.log (1041 : ℕ) ≤ ((694793707/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1042 :
    ((347444861/50000000 : ℚ) : ℝ) ≤ Real.log (1042 : ℕ)
      ∧ Real.log (1042 : ℕ) ≤ ((694889723/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1043 :
    ((138997129/20000000 : ℚ) : ℝ) ≤ Real.log (1043 : ℕ)
      ∧ Real.log (1043 : ℕ) ≤ ((347492823/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1044 :
    ((173770369/25000000 : ℚ) : ℝ) ≤ Real.log (1044 : ℕ)
      ∧ Real.log (1044 : ℕ) ≤ ((695081477/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1045 :
    ((2715536/390625 : ℚ) : ℝ) ≤ Real.log (1045 : ℕ)
      ∧ Real.log (1045 : ℕ) ≤ ((695177217/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1046 :
    ((21727277/3125000 : ℚ) : ℝ) ≤ Real.log (1046 : ℕ)
      ∧ Real.log (1046 : ℕ) ≤ ((139054573/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1047 :
    ((695368421/100000000 : ℚ) : ℝ) ≤ Real.log (1047 : ℕ)
      ∧ Real.log (1047 : ℕ) ≤ ((347684211/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1048 :
    ((347731943/50000000 : ℚ) : ℝ) ≤ Real.log (1048 : ℕ)
      ∧ Real.log (1048 : ℕ) ≤ ((695463887/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1049 :
    ((34777963/5000000 : ℚ) : ℝ) ≤ Real.log (1049 : ℕ)
      ∧ Real.log (1049 : ℕ) ≤ ((695559261/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1050 :
    ((43478409/6250000 : ℚ) : ℝ) ≤ Real.log (1050 : ℕ)
      ∧ Real.log (1050 : ℕ) ≤ ((139130909/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1051 :
    ((695749737/100000000 : ℚ) : ℝ) ≤ Real.log (1051 : ℕ)
      ∧ Real.log (1051 : ℕ) ≤ ((347874869/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1052 :
    ((695844839/100000000 : ℚ) : ℝ) ≤ Real.log (1052 : ℕ)
      ∧ Real.log (1052 : ℕ) ≤ ((17396121/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1053 :
    ((695939851/100000000 : ℚ) : ℝ) ≤ Real.log (1053 : ℕ)
      ∧ Real.log (1053 : ℕ) ≤ ((173984963/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1054 :
    ((174008693/25000000 : ℚ) : ℝ) ≤ Real.log (1054 : ℕ)
      ∧ Real.log (1054 : ℕ) ≤ ((696034773/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1055 :
    ((174032401/25000000 : ℚ) : ℝ) ≤ Real.log (1055 : ℕ)
      ∧ Real.log (1055 : ℕ) ≤ ((139225921/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1056 :
    ((348112173/50000000 : ℚ) : ℝ) ≤ Real.log (1056 : ℕ)
      ∧ Real.log (1056 : ℕ) ≤ ((696224347/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1057 :
    ((348159499/50000000 : ℚ) : ℝ) ≤ Real.log (1057 : ℕ)
      ∧ Real.log (1057 : ℕ) ≤ ((696318999/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1058 :
    ((696413561/100000000 : ℚ) : ℝ) ≤ Real.log (1058 : ℕ)
      ∧ Real.log (1058 : ℕ) ≤ ((348206781/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1059 :
    ((348254017/50000000 : ℚ) : ℝ) ≤ Real.log (1059 : ℕ)
      ∧ Real.log (1059 : ℕ) ≤ ((139301607/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1060 :
    ((348301209/50000000 : ℚ) : ℝ) ≤ Real.log (1060 : ℕ)
      ∧ Real.log (1060 : ℕ) ≤ ((696602419/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1061 :
    ((696696713/100000000 : ℚ) : ℝ) ≤ Real.log (1061 : ℕ)
      ∧ Real.log (1061 : ℕ) ≤ ((348348357/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1062 :
    ((17419773/2500000 : ℚ) : ℝ) ≤ Real.log (1062 : ℕ)
      ∧ Real.log (1062 : ℕ) ≤ ((696790921/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1063 :
    ((696885037/100000000 : ℚ) : ℝ) ≤ Real.log (1063 : ℕ)
      ∧ Real.log (1063 : ℕ) ≤ ((348442519/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1064 :
    ((348489533/50000000 : ℚ) : ℝ) ≤ Real.log (1064 : ℕ)
      ∧ Real.log (1064 : ℕ) ≤ ((174244767/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1065 :
    ((697073007/100000000 : ℚ) : ℝ) ≤ Real.log (1065 : ℕ)
      ∧ Real.log (1065 : ℕ) ≤ ((43567063/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1066 :
    ((34858343/5000000 : ℚ) : ℝ) ≤ Real.log (1066 : ℕ)
      ∧ Real.log (1066 : ℕ) ≤ ((697166861/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1067 :
    ((1115617/160000 : ℚ) : ℝ) ≤ Real.log (1067 : ℕ)
      ∧ Real.log (1067 : ℕ) ≤ ((348630313/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1068 :
    ((697354301/100000000 : ℚ) : ℝ) ≤ Real.log (1068 : ℕ)
      ∧ Real.log (1068 : ℕ) ≤ ((348677151/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1069 :
    ((697447891/100000000 : ℚ) : ℝ) ≤ Real.log (1069 : ℕ)
      ∧ Real.log (1069 : ℕ) ≤ ((174361973/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1070 :
    ((43596337/6250000 : ℚ) : ℝ) ≤ Real.log (1070 : ℕ)
      ∧ Real.log (1070 : ℕ) ≤ ((697541393/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1071 :
    ((697634807/100000000 : ℚ) : ℝ) ≤ Real.log (1071 : ℕ)
      ∧ Real.log (1071 : ℕ) ≤ ((87204351/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1072 :
    ((348864067/50000000 : ℚ) : ℝ) ≤ Real.log (1072 : ℕ)
      ∧ Real.log (1072 : ℕ) ≤ ((139545627/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1073 :
    ((348910687/50000000 : ℚ) : ℝ) ≤ Real.log (1073 : ℕ)
      ∧ Real.log (1073 : ℕ) ≤ ((5582571/800000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1074 :
    ((697914527/100000000 : ℚ) : ℝ) ≤ Real.log (1074 : ℕ)
      ∧ Real.log (1074 : ℕ) ≤ ((21809829/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1075 :
    ((349003797/50000000 : ℚ) : ℝ) ≤ Real.log (1075 : ℕ)
      ∧ Real.log (1075 : ℕ) ≤ ((139601519/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1076 :
    ((349050287/50000000 : ℚ) : ℝ) ≤ Real.log (1076 : ℕ)
      ∧ Real.log (1076 : ℕ) ≤ ((27924023/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1077 :
    ((698193467/100000000 : ℚ) : ℝ) ≤ Real.log (1077 : ℕ)
      ∧ Real.log (1077 : ℕ) ≤ ((174548367/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1078 :
    ((27931451/4000000 : ℚ) : ℝ) ≤ Real.log (1078 : ℕ)
      ∧ Real.log (1078 : ℕ) ≤ ((174571569/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1079 :
    ((174594749/25000000 : ℚ) : ℝ) ≤ Real.log (1079 : ℕ)
      ∧ Real.log (1079 : ℕ) ≤ ((698378997/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1080 :
    ((698471631/100000000 : ℚ) : ℝ) ≤ Real.log (1080 : ℕ)
      ∧ Real.log (1080 : ℕ) ≤ ((698471633/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1081 :
    ((698564181/100000000 : ℚ) : ℝ) ≤ Real.log (1081 : ℕ)
      ∧ Real.log (1081 : ℕ) ≤ ((349282091/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1082 :
    ((139731329/20000000 : ℚ) : ℝ) ≤ Real.log (1082 : ℕ)
      ∧ Real.log (1082 : ℕ) ≤ ((349328323/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1083 :
    ((21835907/3125000 : ℚ) : ℝ) ≤ Real.log (1083 : ℕ)
      ∧ Real.log (1083 : ℕ) ≤ ((27949961/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1084 :
    ((349420659/50000000 : ℚ) : ℝ) ≤ Real.log (1084 : ℕ)
      ∧ Real.log (1084 : ℕ) ≤ ((698841319/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1085 :
    ((349466763/50000000 : ℚ) : ℝ) ≤ Real.log (1085 : ℕ)
      ∧ Real.log (1085 : ℕ) ≤ ((698933527/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1086 :
    ((13980513/2000000 : ℚ) : ℝ) ≤ Real.log (1086 : ℕ)
      ∧ Real.log (1086 : ℕ) ≤ ((699025651/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1087 :
    ((87389711/12500000 : ℚ) : ℝ) ≤ Real.log (1087 : ℕ)
      ∧ Real.log (1087 : ℕ) ≤ ((699117689/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1088 :
    ((349604821/50000000 : ℚ) : ℝ) ≤ Real.log (1088 : ℕ)
      ∧ Real.log (1088 : ℕ) ≤ ((699209643/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1089 :
    ((87412689/12500000 : ℚ) : ℝ) ≤ Real.log (1089 : ℕ)
      ∧ Real.log (1089 : ℕ) ≤ ((699301513/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1090 :
    ((699393297/100000000 : ℚ) : ℝ) ≤ Real.log (1090 : ℕ)
      ∧ Real.log (1090 : ℕ) ≤ ((349696649/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1091 :
    ((349742499/50000000 : ℚ) : ℝ) ≤ Real.log (1091 : ℕ)
      ∧ Real.log (1091 : ℕ) ≤ ((699484999/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1092 :
    ((139915323/20000000 : ℚ) : ℝ) ≤ Real.log (1092 : ℕ)
      ∧ Real.log (1092 : ℕ) ≤ ((87447077/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1093 :
    ((174917037/25000000 : ℚ) : ℝ) ≤ Real.log (1093 : ℕ)
      ∧ Real.log (1093 : ℕ) ≤ ((699668149/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1094 :
    ((349879799/50000000 : ℚ) : ℝ) ≤ Real.log (1094 : ℕ)
      ∧ Real.log (1094 : ℕ) ≤ ((699759599/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1095 :
    ((174962741/25000000 : ℚ) : ℝ) ≤ Real.log (1095 : ℕ)
      ∧ Real.log (1095 : ℕ) ≤ ((139970193/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1096 :
    ((349971123/50000000 : ℚ) : ℝ) ≤ Real.log (1096 : ℕ)
      ∧ Real.log (1096 : ℕ) ≤ ((699942247/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1097 :
    ((140006689/20000000 : ℚ) : ℝ) ≤ Real.log (1097 : ℕ)
      ∧ Real.log (1097 : ℕ) ≤ ((700033447/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1098 :
    ((350062281/50000000 : ℚ) : ℝ) ≤ Real.log (1098 : ℕ)
      ∧ Real.log (1098 : ℕ) ≤ ((700124563/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1099 :
    ((140043119/20000000 : ℚ) : ℝ) ≤ Real.log (1099 : ℕ)
      ∧ Real.log (1099 : ℕ) ≤ ((175053899/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1100 :
    ((140061309/20000000 : ℚ) : ℝ) ≤ Real.log (1100 : ℕ)
      ∧ Real.log (1100 : ℕ) ≤ ((350153273/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1101 :
    ((700397413/100000000 : ℚ) : ℝ) ≤ Real.log (1101 : ℕ)
      ∧ Real.log (1101 : ℕ) ≤ ((350198707/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1102 :
    ((350244099/50000000 : ℚ) : ℝ) ≤ Real.log (1102 : ℕ)
      ∧ Real.log (1102 : ℕ) ≤ ((3502441/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1103 :
    ((700578901/100000000 : ℚ) : ℝ) ≤ Real.log (1103 : ℕ)
      ∧ Real.log (1103 : ℕ) ≤ ((350289451/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1104 :
    ((350334761/50000000 : ℚ) : ℝ) ≤ Real.log (1104 : ℕ)
      ∧ Real.log (1104 : ℕ) ≤ ((700669523/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1105 :
    ((700760061/100000000 : ℚ) : ℝ) ≤ Real.log (1105 : ℕ)
      ∧ Real.log (1105 : ℕ) ≤ ((350380031/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1106 :
    ((350425259/50000000 : ℚ) : ℝ) ≤ Real.log (1106 : ℕ)
      ∧ Real.log (1106 : ℕ) ≤ ((700850519/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1107 :
    ((700940893/100000000 : ℚ) : ℝ) ≤ Real.log (1107 : ℕ)
      ∧ Real.log (1107 : ℕ) ≤ ((350470447/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1108 :
    ((350515593/50000000 : ℚ) : ℝ) ≤ Real.log (1108 : ℕ)
      ∧ Real.log (1108 : ℕ) ≤ ((701031187/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1109 :
    ((350560699/50000000 : ℚ) : ℝ) ≤ Real.log (1109 : ℕ)
      ∧ Real.log (1109 : ℕ) ≤ ((701121399/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1110 :
    ((701211529/100000000 : ℚ) : ℝ) ≤ Real.log (1110 : ℕ)
      ∧ Real.log (1110 : ℕ) ≤ ((70121153/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1111 :
    ((350650789/50000000 : ℚ) : ℝ) ≤ Real.log (1111 : ℕ)
      ∧ Real.log (1111 : ℕ) ≤ ((35065079/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1112 :
    ((701391547/100000000 : ℚ) : ℝ) ≤ Real.log (1112 : ℕ)
      ∧ Real.log (1112 : ℕ) ≤ ((175347887/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1113 :
    ((140296287/20000000 : ℚ) : ℝ) ≤ Real.log (1113 : ℕ)
      ∧ Real.log (1113 : ℕ) ≤ ((175370359/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1114 :
    ((350785621/50000000 : ℚ) : ℝ) ≤ Real.log (1114 : ℕ)
      ∧ Real.log (1114 : ℕ) ≤ ((701571243/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1115 :
    ((87707621/12500000 : ℚ) : ℝ) ≤ Real.log (1115 : ℕ)
      ∧ Real.log (1115 : ℕ) ≤ ((701660969/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1116 :
    ((350875307/50000000 : ℚ) : ℝ) ≤ Real.log (1116 : ℕ)
      ∧ Real.log (1116 : ℕ) ≤ ((140350123/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1117 :
    ((701840179/100000000 : ℚ) : ℝ) ≤ Real.log (1117 : ℕ)
      ∧ Real.log (1117 : ℕ) ≤ ((35092009/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1118 :
    ((140385933/20000000 : ℚ) : ℝ) ≤ Real.log (1118 : ℕ)
      ∧ Real.log (1118 : ℕ) ≤ ((350964833/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1119 :
    ((70201907/10000000 : ℚ) : ℝ) ≤ Real.log (1119 : ℕ)
      ∧ Real.log (1119 : ℕ) ≤ ((702019071/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1120 :
    ((175527099/25000000 : ℚ) : ℝ) ≤ Real.log (1120 : ℕ)
      ∧ Real.log (1120 : ℕ) ≤ ((702108397/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1121 :
    ((351098821/50000000 : ℚ) : ℝ) ≤ Real.log (1121 : ℕ)
      ∧ Real.log (1121 : ℕ) ≤ ((702197643/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1122 :
    ((87785851/12500000 : ℚ) : ℝ) ≤ Real.log (1122 : ℕ)
      ∧ Real.log (1122 : ℕ) ≤ ((702286809/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1123 :
    ((140475179/20000000 : ℚ) : ℝ) ≤ Real.log (1123 : ℕ)
      ∧ Real.log (1123 : ℕ) ≤ ((87796987/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1124 :
    ((702464903/100000000 : ℚ) : ℝ) ≤ Real.log (1124 : ℕ)
      ∧ Real.log (1124 : ℕ) ≤ ((87808113/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1125 :
    ((702553831/100000000 : ℚ) : ℝ) ≤ Real.log (1125 : ℕ)
      ∧ Real.log (1125 : ℕ) ≤ ((87819229/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1126 :
    ((17566067/2500000 : ℚ) : ℝ) ≤ Real.log (1126 : ℕ)
      ∧ Real.log (1126 : ℕ) ≤ ((702642681/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1127 :
    ((702731451/100000000 : ℚ) : ℝ) ≤ Real.log (1127 : ℕ)
      ∧ Real.log (1127 : ℕ) ≤ ((175682863/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1128 :
    ((702820143/100000000 : ℚ) : ℝ) ≤ Real.log (1128 : ℕ)
      ∧ Real.log (1128 : ℕ) ≤ ((43926259/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1129 :
    ((175727189/25000000 : ℚ) : ℝ) ≤ Real.log (1129 : ℕ)
      ∧ Real.log (1129 : ℕ) ≤ ((702908757/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1130 :
    ((702997291/100000000 : ℚ) : ℝ) ≤ Real.log (1130 : ℕ)
      ∧ Real.log (1130 : ℕ) ≤ ((175749323/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1131 :
    ((703085747/100000000 : ℚ) : ℝ) ≤ Real.log (1131 : ℕ)
      ∧ Real.log (1131 : ℕ) ≤ ((175771437/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1132 :
    ((5625393/800000 : ℚ) : ℝ) ≤ Real.log (1132 : ℕ)
      ∧ Real.log (1132 : ℕ) ≤ ((351587063/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1133 :
    ((351631213/50000000 : ℚ) : ℝ) ≤ Real.log (1133 : ℕ)
      ∧ Real.log (1133 : ℕ) ≤ ((703262427/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1134 :
    ((87918831/12500000 : ℚ) : ℝ) ≤ Real.log (1134 : ℕ)
      ∧ Real.log (1134 : ℕ) ≤ ((703350649/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1135 :
    ((87929849/12500000 : ℚ) : ℝ) ≤ Real.log (1135 : ℕ)
      ∧ Real.log (1135 : ℕ) ≤ ((351719397/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1136 :
    ((703526859/100000000 : ℚ) : ℝ) ≤ Real.log (1136 : ℕ)
      ∧ Real.log (1136 : ℕ) ≤ ((35176343/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1137 :
    ((703614849/100000000 : ℚ) : ℝ) ≤ Real.log (1137 : ℕ)
      ∧ Real.log (1137 : ℕ) ≤ ((14072297/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1138 :
    ((703702761/100000000 : ℚ) : ℝ) ≤ Real.log (1138 : ℕ)
      ∧ Real.log (1138 : ℕ) ≤ ((351851381/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1139 :
    ((175947649/25000000 : ℚ) : ℝ) ≤ Real.log (1139 : ℕ)
      ∧ Real.log (1139 : ℕ) ≤ ((703790597/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1140 :
    ((351939177/50000000 : ℚ) : ℝ) ≤ Real.log (1140 : ℕ)
      ∧ Real.log (1140 : ℕ) ≤ ((140775671/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1141 :
    ((351983017/50000000 : ℚ) : ℝ) ≤ Real.log (1141 : ℕ)
      ∧ Real.log (1141 : ℕ) ≤ ((175991509/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1142 :
    ((352026819/50000000 : ℚ) : ℝ) ≤ Real.log (1142 : ℕ)
      ∧ Real.log (1142 : ℕ) ≤ ((17601341/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1143 :
    ((352070583/50000000 : ℚ) : ℝ) ≤ Real.log (1143 : ℕ)
      ∧ Real.log (1143 : ℕ) ≤ ((704141167/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1144 :
    ((704228617/100000000 : ℚ) : ℝ) ≤ Real.log (1144 : ℕ)
      ∧ Real.log (1144 : ℕ) ≤ ((352114309/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1145 :
    ((704315991/100000000 : ℚ) : ℝ) ≤ Real.log (1145 : ℕ)
      ∧ Real.log (1145 : ℕ) ≤ ((88039499/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1146 :
    ((704403289/100000000 : ℚ) : ℝ) ≤ Real.log (1146 : ℕ)
      ∧ Real.log (1146 : ℕ) ≤ ((70440329/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1147 :
    ((704490511/100000000 : ℚ) : ℝ) ≤ Real.log (1147 : ℕ)
      ∧ Real.log (1147 : ℕ) ≤ ((44030657/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1148 :
    ((704577657/100000000 : ℚ) : ℝ) ≤ Real.log (1148 : ℕ)
      ∧ Real.log (1148 : ℕ) ≤ ((352288829/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1149 :
    ((704664727/100000000 : ℚ) : ℝ) ≤ Real.log (1149 : ℕ)
      ∧ Real.log (1149 : ℕ) ≤ ((88083091/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1150 :
    ((352375861/50000000 : ℚ) : ℝ) ≤ Real.log (1150 : ℕ)
      ∧ Real.log (1150 : ℕ) ≤ ((704751723/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1151 :
    ((8810483/1250000 : ℚ) : ℝ) ≤ Real.log (1151 : ℕ)
      ∧ Real.log (1151 : ℕ) ≤ ((704838641/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1152 :
    ((176231371/25000000 : ℚ) : ℝ) ≤ Real.log (1152 : ℕ)
      ∧ Real.log (1152 : ℕ) ≤ ((140985097/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1153 :
    ((705012251/100000000 : ℚ) : ℝ) ≤ Real.log (1153 : ℕ)
      ∧ Real.log (1153 : ℕ) ≤ ((705012253/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1154 :
    ((11017171/1562500 : ℚ) : ℝ) ≤ Real.log (1154 : ℕ)
      ∧ Real.log (1154 : ℕ) ≤ ((141019789/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1155 :
    ((352592781/50000000 : ℚ) : ℝ) ≤ Real.log (1155 : ℕ)
      ∧ Real.log (1155 : ℕ) ≤ ((705185563/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1156 :
    ((88159013/12500000 : ℚ) : ℝ) ≤ Real.log (1156 : ℕ)
      ∧ Real.log (1156 : ℕ) ≤ ((141054421/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1157 :
    ((176339643/25000000 : ℚ) : ℝ) ≤ Real.log (1157 : ℕ)
      ∧ Real.log (1157 : ℕ) ≤ ((705358573/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1158 :
    ((141088993/20000000 : ℚ) : ℝ) ≤ Real.log (1158 : ℕ)
      ∧ Real.log (1158 : ℕ) ≤ ((352722483/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1159 :
    ((176382821/25000000 : ℚ) : ℝ) ≤ Real.log (1159 : ℕ)
      ∧ Real.log (1159 : ℕ) ≤ ((141106257/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1160 :
    ((88202191/12500000 : ℚ) : ℝ) ≤ Real.log (1160 : ℕ)
      ∧ Real.log (1160 : ℕ) ≤ ((705617529/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1161 :
    ((352851849/50000000 : ℚ) : ℝ) ≤ Real.log (1161 : ℕ)
      ∧ Real.log (1161 : ℕ) ≤ ((705703699/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1162 :
    ((705789793/100000000 : ℚ) : ℝ) ≤ Real.log (1162 : ℕ)
      ∧ Real.log (1162 : ℕ) ≤ ((352894897/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1163 :
    ((141175163/20000000 : ℚ) : ℝ) ≤ Real.log (1163 : ℕ)
      ∧ Real.log (1163 : ℕ) ≤ ((88234477/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1164 :
    ((352980881/50000000 : ℚ) : ℝ) ≤ Real.log (1164 : ℕ)
      ∧ Real.log (1164 : ℕ) ≤ ((705961763/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1165 :
    ((176511909/25000000 : ℚ) : ℝ) ≤ Real.log (1165 : ℕ)
      ∧ Real.log (1165 : ℕ) ≤ ((706047637/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1166 :
    ((176533359/25000000 : ℚ) : ℝ) ≤ Real.log (1166 : ℕ)
      ∧ Real.log (1166 : ℕ) ≤ ((706133437/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1167 :
    ((706219163/100000000 : ℚ) : ℝ) ≤ Real.log (1167 : ℕ)
      ∧ Real.log (1167 : ℕ) ≤ ((176554791/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1168 :
    ((44144051/6250000 : ℚ) : ℝ) ≤ Real.log (1168 : ℕ)
      ∧ Real.log (1168 : ℕ) ≤ ((706304817/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1169 :
    ((176597599/25000000 : ℚ) : ℝ) ≤ Real.log (1169 : ℕ)
      ∧ Real.log (1169 : ℕ) ≤ ((706390397/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1170 :
    ((353237951/50000000 : ℚ) : ℝ) ≤ Real.log (1170 : ℕ)
      ∧ Real.log (1170 : ℕ) ≤ ((706475903/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1171 :
    ((88320167/12500000 : ℚ) : ℝ) ≤ Real.log (1171 : ℕ)
      ∧ Real.log (1171 : ℕ) ≤ ((706561337/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1172 :
    ((88330837/12500000 : ℚ) : ℝ) ≤ Real.log (1172 : ℕ)
      ∧ Real.log (1172 : ℕ) ≤ ((353323349/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1173 :
    ((44170749/6250000 : ℚ) : ℝ) ≤ Real.log (1173 : ℕ)
      ∧ Real.log (1173 : ℕ) ≤ ((141346397/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1174 :
    ((1767043/250000 : ℚ) : ℝ) ≤ Real.log (1174 : ℕ)
      ∧ Real.log (1174 : ℕ) ≤ ((706817201/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1175 :
    ((353451171/50000000 : ℚ) : ℝ) ≤ Real.log (1175 : ℕ)
      ∧ Real.log (1175 : ℕ) ≤ ((706902343/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1176 :
    ((176746853/25000000 : ℚ) : ℝ) ≤ Real.log (1176 : ℕ)
      ∧ Real.log (1176 : ℕ) ≤ ((706987413/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1177 :
    ((70707241/10000000 : ℚ) : ℝ) ≤ Real.log (1177 : ℕ)
      ∧ Real.log (1177 : ℕ) ≤ ((707072411/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1178 :
    ((88394667/12500000 : ℚ) : ℝ) ≤ Real.log (1178 : ℕ)
      ∧ Real.log (1178 : ℕ) ≤ ((707157337/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1179 :
    ((70724219/10000000 : ℚ) : ℝ) ≤ Real.log (1179 : ℕ)
      ∧ Real.log (1179 : ℕ) ≤ ((707242191/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1180 :
    ((707326971/100000000 : ℚ) : ℝ) ≤ Real.log (1180 : ℕ)
      ∧ Real.log (1180 : ℕ) ≤ ((176831743/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1181 :
    ((707411681/100000000 : ℚ) : ℝ) ≤ Real.log (1181 : ℕ)
      ∧ Real.log (1181 : ℕ) ≤ ((353705841/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1182 :
    ((707496319/100000000 : ℚ) : ℝ) ≤ Real.log (1182 : ℕ)
      ∧ Real.log (1182 : ℕ) ≤ ((1105463/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1183 :
    ((353790443/50000000 : ℚ) : ℝ) ≤ Real.log (1183 : ℕ)
      ∧ Real.log (1183 : ℕ) ≤ ((707580887/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1184 :
    ((707665381/100000000 : ℚ) : ℝ) ≤ Real.log (1184 : ℕ)
      ∧ Real.log (1184 : ℕ) ≤ ((353832691/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1185 :
    ((141549961/20000000 : ℚ) : ℝ) ≤ Real.log (1185 : ℕ)
      ∧ Real.log (1185 : ℕ) ≤ ((353874903/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1186 :
    ((707834157/100000000 : ℚ) : ℝ) ≤ Real.log (1186 : ℕ)
      ∧ Real.log (1186 : ℕ) ≤ ((353917079/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1187 :
    ((707918439/100000000 : ℚ) : ℝ) ≤ Real.log (1187 : ℕ)
      ∧ Real.log (1187 : ℕ) ≤ ((17697961/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1188 :
    ((708002649/100000000 : ℚ) : ℝ) ≤ Real.log (1188 : ℕ)
      ∧ Real.log (1188 : ℕ) ≤ ((708002651/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1189 :
    ((708086789/100000000 : ℚ) : ℝ) ≤ Real.log (1189 : ℕ)
      ∧ Real.log (1189 : ℕ) ≤ ((70808679/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1190 :
    ((354085429/50000000 : ℚ) : ℝ) ≤ Real.log (1190 : ℕ)
      ∧ Real.log (1190 : ℕ) ≤ ((708170859/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1191 :
    ((88531857/12500000 : ℚ) : ℝ) ≤ Real.log (1191 : ℕ)
      ∧ Real.log (1191 : ℕ) ≤ ((708254857/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1192 :
    ((22135587/3125000 : ℚ) : ℝ) ≤ Real.log (1192 : ℕ)
      ∧ Real.log (1192 : ℕ) ≤ ((141667757/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1193 :
    ((354211321/50000000 : ℚ) : ℝ) ≤ Real.log (1193 : ℕ)
      ∧ Real.log (1193 : ℕ) ≤ ((708422643/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1194 :
    ((708506429/100000000 : ℚ) : ℝ) ≤ Real.log (1194 : ℕ)
      ∧ Real.log (1194 : ℕ) ≤ ((70850643/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1195 :
    ((354295073/50000000 : ℚ) : ℝ) ≤ Real.log (1195 : ℕ)
      ∧ Real.log (1195 : ℕ) ≤ ((708590147/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1196 :
    ((708673793/100000000 : ℚ) : ℝ) ≤ Real.log (1196 : ℕ)
      ∧ Real.log (1196 : ℕ) ≤ ((354336897/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1197 :
    ((70875737/10000000 : ℚ) : ℝ) ≤ Real.log (1197 : ℕ)
      ∧ Real.log (1197 : ℕ) ≤ ((708757371/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1198 :
    ((708840877/100000000 : ℚ) : ℝ) ≤ Real.log (1198 : ℕ)
      ∧ Real.log (1198 : ℕ) ≤ ((354420439/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1199 :
    ((141784863/20000000 : ℚ) : ℝ) ≤ Real.log (1199 : ℕ)
      ∧ Real.log (1199 : ℕ) ≤ ((177231079/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1200 :
    ((709007683/100000000 : ℚ) : ℝ) ≤ Real.log (1200 : ℕ)
      ∧ Real.log (1200 : ℕ) ≤ ((177251921/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1201 :
    ((354545491/50000000 : ℚ) : ℝ) ≤ Real.log (1201 : ℕ)
      ∧ Real.log (1201 : ℕ) ≤ ((709090983/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1202 :
    ((709174211/100000000 : ℚ) : ℝ) ≤ Real.log (1202 : ℕ)
      ∧ Real.log (1202 : ℕ) ≤ ((177293553/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1203 :
    ((709257371/100000000 : ℚ) : ℝ) ≤ Real.log (1203 : ℕ)
      ∧ Real.log (1203 : ℕ) ≤ ((177314343/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1204 :
    ((354670231/50000000 : ℚ) : ℝ) ≤ Real.log (1204 : ℕ)
      ∧ Real.log (1204 : ℕ) ≤ ((709340463/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1205 :
    ((177355871/25000000 : ℚ) : ℝ) ≤ Real.log (1205 : ℕ)
      ∧ Real.log (1205 : ℕ) ≤ ((141884697/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1206 :
    ((709506437/100000000 : ℚ) : ℝ) ≤ Real.log (1206 : ℕ)
      ∧ Real.log (1206 : ℕ) ≤ ((354753219/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1207 :
    ((354794661/50000000 : ℚ) : ℝ) ≤ Real.log (1207 : ℕ)
      ∧ Real.log (1207 : ℕ) ≤ ((709589323/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1208 :
    ((709672137/100000000 : ℚ) : ℝ) ≤ Real.log (1208 : ℕ)
      ∧ Real.log (1208 : ℕ) ≤ ((354836069/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1209 :
    ((141950977/20000000 : ℚ) : ℝ) ≤ Real.log (1209 : ℕ)
      ∧ Real.log (1209 : ℕ) ≤ ((354877443/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1210 :
    ((709837563/100000000 : ℚ) : ℝ) ≤ Real.log (1210 : ℕ)
      ∧ Real.log (1210 : ℕ) ≤ ((177459391/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1211 :
    ((354960087/50000000 : ℚ) : ℝ) ≤ Real.log (1211 : ℕ)
      ∧ Real.log (1211 : ℕ) ≤ ((28396807/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1212 :
    ((177500679/25000000 : ℚ) : ℝ) ≤ Real.log (1212 : ℕ)
      ∧ Real.log (1212 : ℕ) ≤ ((710002717/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1213 :
    ((71008519/10000000 : ℚ) : ℝ) ≤ Real.log (1213 : ℕ)
      ∧ Real.log (1213 : ℕ) ≤ ((710085191/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1214 :
    ((710167597/100000000 : ℚ) : ℝ) ≤ Real.log (1214 : ℕ)
      ∧ Real.log (1214 : ℕ) ≤ ((355083799/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1215 :
    ((142049987/20000000 : ℚ) : ℝ) ≤ Real.log (1215 : ℕ)
      ∧ Real.log (1215 : ℕ) ≤ ((44390621/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1216 :
    ((355166103/50000000 : ℚ) : ℝ) ≤ Real.log (1216 : ℕ)
      ∧ Real.log (1216 : ℕ) ≤ ((710332207/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1217 :
    ((710414409/100000000 : ℚ) : ℝ) ≤ Real.log (1217 : ℕ)
      ∧ Real.log (1217 : ℕ) ≤ ((71041441/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1218 :
    ((22203017/3125000 : ℚ) : ℝ) ≤ Real.log (1218 : ℕ)
      ∧ Real.log (1218 : ℕ) ≤ ((142099309/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1219 :
    ((177644653/25000000 : ℚ) : ℝ) ≤ Real.log (1219 : ℕ)
      ∧ Real.log (1219 : ℕ) ≤ ((710578613/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1220 :
    ((710660613/100000000 : ℚ) : ℝ) ≤ Real.log (1220 : ℕ)
      ∧ Real.log (1220 : ℕ) ≤ ((355330307/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1221 :
    ((710742547/100000000 : ℚ) : ℝ) ≤ Real.log (1221 : ℕ)
      ∧ Real.log (1221 : ℕ) ≤ ((177685637/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1222 :
    ((710824413/100000000 : ℚ) : ℝ) ≤ Real.log (1222 : ℕ)
      ∧ Real.log (1222 : ℕ) ≤ ((142164883/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1223 :
    ((710906213/100000000 : ℚ) : ℝ) ≤ Real.log (1223 : ℕ)
      ∧ Real.log (1223 : ℕ) ≤ ((355453107/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1224 :
    ((355493973/50000000 : ℚ) : ℝ) ≤ Real.log (1224 : ℕ)
      ∧ Real.log (1224 : ℕ) ≤ ((710987947/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1225 :
    ((177767403/25000000 : ℚ) : ℝ) ≤ Real.log (1225 : ℕ)
      ∧ Real.log (1225 : ℕ) ≤ ((711069613/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1226 :
    ((711151211/100000000 : ℚ) : ℝ) ≤ Real.log (1226 : ℕ)
      ∧ Real.log (1226 : ℕ) ≤ ((177787803/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1227 :
    ((88904093/12500000 : ℚ) : ℝ) ≤ Real.log (1227 : ℕ)
      ∧ Real.log (1227 : ℕ) ≤ ((142246549/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1228 :
    ((71131421/10000000 : ℚ) : ℝ) ≤ Real.log (1228 : ℕ)
      ∧ Real.log (1228 : ℕ) ≤ ((711314211/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1229 :
    ((71139561/10000000 : ℚ) : ℝ) ≤ Real.log (1229 : ℕ)
      ∧ Real.log (1229 : ℕ) ≤ ((711395611/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1230 :
    ((44467309/6250000 : ℚ) : ℝ) ≤ Real.log (1230 : ℕ)
      ∧ Real.log (1230 : ℕ) ≤ ((142295389/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1231 :
    ((177889553/25000000 : ℚ) : ℝ) ≤ Real.log (1231 : ℕ)
      ∧ Real.log (1231 : ℕ) ≤ ((711558213/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1232 :
    ((355819707/50000000 : ℚ) : ℝ) ≤ Real.log (1232 : ℕ)
      ∧ Real.log (1232 : ℕ) ≤ ((142327883/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1233 :
    ((14234411/2000000 : ℚ) : ℝ) ≤ Real.log (1233 : ℕ)
      ∧ Real.log (1233 : ℕ) ≤ ((711720551/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1234 :
    ((35590081/5000000 : ℚ) : ℝ) ≤ Real.log (1234 : ℕ)
      ∧ Real.log (1234 : ℕ) ≤ ((711801621/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1235 :
    ((5561583/781250 : ℚ) : ℝ) ≤ Real.log (1235 : ℕ)
      ∧ Real.log (1235 : ℕ) ≤ ((5695061/800000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1236 :
    ((711963563/100000000 : ℚ) : ℝ) ≤ Real.log (1236 : ℕ)
      ∧ Real.log (1236 : ℕ) ≤ ((177990891/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1237 :
    ((712044437/100000000 : ℚ) : ℝ) ≤ Real.log (1237 : ℕ)
      ∧ Real.log (1237 : ℕ) ≤ ((356022219/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1238 :
    ((142425049/20000000 : ℚ) : ℝ) ≤ Real.log (1238 : ℕ)
      ∧ Real.log (1238 : ℕ) ≤ ((356062623/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1239 :
    ((178051497/25000000 : ℚ) : ℝ) ≤ Real.log (1239 : ℕ)
      ∧ Real.log (1239 : ℕ) ≤ ((712205989/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1240 :
    ((142457333/20000000 : ℚ) : ℝ) ≤ Real.log (1240 : ℕ)
      ∧ Real.log (1240 : ℕ) ≤ ((356143333/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1241 :
    ((356183639/50000000 : ℚ) : ℝ) ≤ Real.log (1241 : ℕ)
      ∧ Real.log (1241 : ℕ) ≤ ((712367279/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1242 :
    ((356223913/50000000 : ℚ) : ℝ) ≤ Real.log (1242 : ℕ)
      ∧ Real.log (1242 : ℕ) ≤ ((712447827/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1243 :
    ((712528309/100000000 : ℚ) : ℝ) ≤ Real.log (1243 : ℕ)
      ∧ Real.log (1243 : ℕ) ≤ ((71252831/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1244 :
    ((712608727/100000000 : ℚ) : ℝ) ≤ Real.log (1244 : ℕ)
      ∧ Real.log (1244 : ℕ) ≤ ((89076091/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1245 :
    ((17817227/2500000 : ℚ) : ℝ) ≤ Real.log (1245 : ℕ)
      ∧ Real.log (1245 : ℕ) ≤ ((712689081/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1246 :
    ((712769369/100000000 : ℚ) : ℝ) ≤ Real.log (1246 : ℕ)
      ∧ Real.log (1246 : ℕ) ≤ ((71276937/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1247 :
    ((356424797/50000000 : ℚ) : ℝ) ≤ Real.log (1247 : ℕ)
      ∧ Real.log (1247 : ℕ) ≤ ((142569919/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1248 :
    ((356464877/50000000 : ℚ) : ℝ) ≤ Real.log (1248 : ℕ)
      ∧ Real.log (1248 : ℕ) ≤ ((142585951/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1249 :
    ((14260197/2000000 : ℚ) : ℝ) ≤ Real.log (1249 : ℕ)
      ∧ Real.log (1249 : ℕ) ≤ ((178252463/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1250 :
    ((356544941/50000000 : ℚ) : ℝ) ≤ Real.log (1250 : ℕ)
      ∧ Real.log (1250 : ℕ) ≤ ((178272471/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1251 :
    ((713169851/100000000 : ℚ) : ℝ) ≤ Real.log (1251 : ℕ)
      ∧ Real.log (1251 : ℕ) ≤ ((178292463/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1252 :
    ((142649951/20000000 : ℚ) : ℝ) ≤ Real.log (1252 : ℕ)
      ∧ Real.log (1252 : ℕ) ≤ ((178312439/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1253 :
    ((142665919/20000000 : ℚ) : ℝ) ≤ Real.log (1253 : ℕ)
      ∧ Real.log (1253 : ℕ) ≤ ((178332399/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1254 :
    ((178352343/25000000 : ℚ) : ℝ) ≤ Real.log (1254 : ℕ)
      ∧ Real.log (1254 : ℕ) ≤ ((713409373/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1255 :
    ((142697817/20000000 : ℚ) : ℝ) ≤ Real.log (1255 : ℕ)
      ∧ Real.log (1255 : ℕ) ≤ ((356744543/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1256 :
    ((356784367/50000000 : ℚ) : ℝ) ≤ Real.log (1256 : ℕ)
      ∧ Real.log (1256 : ℕ) ≤ ((142713747/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1257 :
    ((2230151/312500 : ℚ) : ℝ) ≤ Real.log (1257 : ℕ)
      ∧ Real.log (1257 : ℕ) ≤ ((713648321/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1258 :
    ((713727843/100000000 : ℚ) : ℝ) ≤ Real.log (1258 : ℕ)
      ∧ Real.log (1258 : ℕ) ≤ ((178431961/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1259 :
    ((713807303/100000000 : ℚ) : ℝ) ≤ Real.log (1259 : ℕ)
      ∧ Real.log (1259 : ℕ) ≤ ((89225913/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1260 :
    ((713886699/100000000 : ℚ) : ℝ) ≤ Real.log (1260 : ℕ)
      ∧ Real.log (1260 : ℕ) ≤ ((713886701/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1261 :
    ((713966033/100000000 : ℚ) : ℝ) ≤ Real.log (1261 : ℕ)
      ∧ Real.log (1261 : ℕ) ≤ ((356983017/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1262 :
    ((89255663/12500000 : ℚ) : ℝ) ≤ Real.log (1262 : ℕ)
      ∧ Real.log (1262 : ℕ) ≤ ((142809061/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1263 :
    ((22316391/3125000 : ℚ) : ℝ) ≤ Real.log (1263 : ℕ)
      ∧ Real.log (1263 : ℕ) ≤ ((714124513/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1264 :
    ((714203657/100000000 : ℚ) : ℝ) ≤ Real.log (1264 : ℕ)
      ∧ Real.log (1264 : ℕ) ≤ ((357101829/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1265 :
    ((35714137/5000000 : ℚ) : ℝ) ≤ Real.log (1265 : ℕ)
      ∧ Real.log (1265 : ℕ) ≤ ((714282741/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1266 :
    ((4464761/625000 : ℚ) : ℝ) ≤ Real.log (1266 : ℕ)
      ∧ Real.log (1266 : ℕ) ≤ ((714361761/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1267 :
    ((714440717/100000000 : ℚ) : ℝ) ≤ Real.log (1267 : ℕ)
      ∧ Real.log (1267 : ℕ) ≤ ((714440719/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1268 :
    ((714519613/100000000 : ℚ) : ℝ) ≤ Real.log (1268 : ℕ)
      ∧ Real.log (1268 : ℕ) ≤ ((357259807/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1269 :
    ((357299223/50000000 : ℚ) : ℝ) ≤ Real.log (1269 : ℕ)
      ∧ Real.log (1269 : ℕ) ≤ ((714598447/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1270 :
    ((714677217/100000000 : ℚ) : ℝ) ≤ Real.log (1270 : ℕ)
      ∧ Real.log (1270 : ℕ) ≤ ((357338609/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1271 :
    ((714755927/100000000 : ℚ) : ℝ) ≤ Real.log (1271 : ℕ)
      ∧ Real.log (1271 : ℕ) ≤ ((89344491/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1272 :
    ((357417287/50000000 : ℚ) : ℝ) ≤ Real.log (1272 : ℕ)
      ∧ Real.log (1272 : ℕ) ≤ ((28593383/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1273 :
    ((714913159/100000000 : ℚ) : ℝ) ≤ Real.log (1273 : ℕ)
      ∧ Real.log (1273 : ℕ) ≤ ((17872829/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1274 :
    ((714991683/100000000 : ℚ) : ℝ) ≤ Real.log (1274 : ℕ)
      ∧ Real.log (1274 : ℕ) ≤ ((178747921/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1275 :
    ((143014029/20000000 : ℚ) : ℝ) ≤ Real.log (1275 : ℕ)
      ∧ Real.log (1275 : ℕ) ≤ ((357535073/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1276 :
    ((357574273/50000000 : ℚ) : ℝ) ≤ Real.log (1276 : ℕ)
      ∧ Real.log (1276 : ℕ) ≤ ((715148547/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1277 :
    ((143045377/20000000 : ℚ) : ℝ) ≤ Real.log (1277 : ℕ)
      ∧ Real.log (1277 : ℕ) ≤ ((357613443/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1278 :
    ((715305163/100000000 : ℚ) : ℝ) ≤ Real.log (1278 : ℕ)
      ∧ Real.log (1278 : ℕ) ≤ ((178826291/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1279 :
    ((35769169/5000000 : ℚ) : ℝ) ≤ Real.log (1279 : ℕ)
      ∧ Real.log (1279 : ℕ) ≤ ((715383381/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1280 :
    ((143092307/20000000 : ℚ) : ℝ) ≤ Real.log (1280 : ℕ)
      ∧ Real.log (1280 : ℕ) ≤ ((22358173/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1281 :
    ((71553963/10000000 : ℚ) : ℝ) ≤ Real.log (1281 : ℕ)
      ∧ Real.log (1281 : ℕ) ≤ ((715539631/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1282 :
    ((715617663/100000000 : ℚ) : ℝ) ≤ Real.log (1282 : ℕ)
      ∧ Real.log (1282 : ℕ) ≤ ((5590763/781250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1283 :
    ((178923909/25000000 : ℚ) : ℝ) ≤ Real.log (1283 : ℕ)
      ∧ Real.log (1283 : ℕ) ≤ ((715695637/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1284 :
    ((178943387/25000000 : ℚ) : ℝ) ≤ Real.log (1284 : ℕ)
      ∧ Real.log (1284 : ℕ) ≤ ((715773549/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1285 :
    ((715851399/100000000 : ℚ) : ℝ) ≤ Real.log (1285 : ℕ)
      ∧ Real.log (1285 : ℕ) ≤ ((3579257/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1286 :
    ((71592919/10000000 : ℚ) : ℝ) ≤ Real.log (1286 : ℕ)
      ∧ Real.log (1286 : ℕ) ≤ ((715929191/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1287 :
    ((17900173/2500000 : ℚ) : ℝ) ≤ Real.log (1287 : ℕ)
      ∧ Real.log (1287 : ℕ) ≤ ((716006921/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1288 :
    ((71608459/10000000 : ℚ) : ℝ) ≤ Real.log (1288 : ℕ)
      ∧ Real.log (1288 : ℕ) ≤ ((716084591/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1289 :
    ((3580811/500000 : ℚ) : ℝ) ≤ Real.log (1289 : ℕ)
      ∧ Real.log (1289 : ℕ) ≤ ((716162201/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1290 :
    ((716239749/100000000 : ℚ) : ℝ) ≤ Real.log (1290 : ℕ)
      ∧ Real.log (1290 : ℕ) ≤ ((2864959/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1291 :
    ((716317239/100000000 : ℚ) : ℝ) ≤ Real.log (1291 : ℕ)
      ∧ Real.log (1291 : ℕ) ≤ ((17907931/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1292 :
    ((179098667/25000000 : ℚ) : ℝ) ≤ Real.log (1292 : ℕ)
      ∧ Real.log (1292 : ℕ) ≤ ((716394669/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1293 :
    ((716472037/100000000 : ℚ) : ℝ) ≤ Real.log (1293 : ℕ)
      ∧ Real.log (1293 : ℕ) ≤ ((358236019/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1294 :
    ((716549347/100000000 : ℚ) : ℝ) ≤ Real.log (1294 : ℕ)
      ∧ Real.log (1294 : ℕ) ≤ ((179137337/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1295 :
    ((716626597/100000000 : ℚ) : ℝ) ≤ Real.log (1295 : ℕ)
      ∧ Real.log (1295 : ℕ) ≤ ((358313299/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1296 :
    ((716703787/100000000 : ℚ) : ℝ) ≤ Real.log (1296 : ℕ)
      ∧ Real.log (1296 : ℕ) ≤ ((179175947/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1297 :
    ((358390459/50000000 : ℚ) : ℝ) ≤ Real.log (1297 : ℕ)
      ∧ Real.log (1297 : ℕ) ≤ ((716780919/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1298 :
    ((716857989/100000000 : ℚ) : ℝ) ≤ Real.log (1298 : ℕ)
      ∧ Real.log (1298 : ℕ) ≤ ((71685799/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1299 :
    ((716935001/100000000 : ℚ) : ℝ) ≤ Real.log (1299 : ℕ)
      ∧ Real.log (1299 : ℕ) ≤ ((358467501/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1300 :
    ((358505977/50000000 : ℚ) : ℝ) ≤ Real.log (1300 : ℕ)
      ∧ Real.log (1300 : ℕ) ≤ ((143402391/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1301 :
    ((717088847/100000000 : ℚ) : ℝ) ≤ Real.log (1301 : ℕ)
      ∧ Real.log (1301 : ℕ) ≤ ((44818053/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1302 :
    ((358582841/50000000 : ℚ) : ℝ) ≤ Real.log (1302 : ℕ)
      ∧ Real.log (1302 : ℕ) ≤ ((717165683/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1303 :
    ((717242457/100000000 : ℚ) : ℝ) ≤ Real.log (1303 : ℕ)
      ∧ Real.log (1303 : ℕ) ≤ ((358621229/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1304 :
    ((358659587/50000000 : ℚ) : ℝ) ≤ Real.log (1304 : ℕ)
      ∧ Real.log (1304 : ℕ) ≤ ((28692767/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1305 :
    ((717395831/100000000 : ℚ) : ℝ) ≤ Real.log (1305 : ℕ)
      ∧ Real.log (1305 : ℕ) ≤ ((717395833/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1306 :
    ((71747243/10000000 : ℚ) : ℝ) ≤ Real.log (1306 : ℕ)
      ∧ Real.log (1306 : ℕ) ≤ ((44842027/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1307 :
    ((717548971/100000000 : ℚ) : ℝ) ≤ Real.log (1307 : ℕ)
      ∧ Real.log (1307 : ℕ) ≤ ((179387243/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1308 :
    ((717625453/100000000 : ℚ) : ℝ) ≤ Real.log (1308 : ℕ)
      ∧ Real.log (1308 : ℕ) ≤ ((358812727/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1309 :
    ((179425469/25000000 : ℚ) : ℝ) ≤ Real.log (1309 : ℕ)
      ∧ Real.log (1309 : ℕ) ≤ ((717701877/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1310 :
    ((717778241/100000000 : ℚ) : ℝ) ≤ Real.log (1310 : ℕ)
      ∧ Real.log (1310 : ℕ) ≤ ((358889121/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1311 :
    ((179463637/25000000 : ℚ) : ℝ) ≤ Real.log (1311 : ℕ)
      ∧ Real.log (1311 : ℕ) ≤ ((717854549/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1312 :
    ((179482699/25000000 : ℚ) : ℝ) ≤ Real.log (1312 : ℕ)
      ∧ Real.log (1312 : ℕ) ≤ ((717930797/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1313 :
    ((718006987/100000000 : ℚ) : ℝ) ≤ Real.log (1313 : ℕ)
      ∧ Real.log (1313 : ℕ) ≤ ((179501747/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1314 :
    ((718083119/100000000 : ℚ) : ℝ) ≤ Real.log (1314 : ℕ)
      ∧ Real.log (1314 : ℕ) ≤ ((8976039/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1315 :
    ((359079597/50000000 : ℚ) : ℝ) ≤ Real.log (1315 : ℕ)
      ∧ Real.log (1315 : ℕ) ≤ ((143631839/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1316 :
    ((718235211/100000000 : ℚ) : ℝ) ≤ Real.log (1316 : ℕ)
      ∧ Real.log (1316 : ℕ) ≤ ((179558803/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1317 :
    ((71831117/10000000 : ℚ) : ℝ) ≤ Real.log (1317 : ℕ)
      ∧ Real.log (1317 : ℕ) ≤ ((718311171/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1318 :
    ((718387071/100000000 : ℚ) : ℝ) ≤ Real.log (1318 : ℕ)
      ∧ Real.log (1318 : ℕ) ≤ ((5612399/781250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1319 :
    ((143692583/20000000 : ℚ) : ℝ) ≤ Real.log (1319 : ℕ)
      ∧ Real.log (1319 : ℕ) ≤ ((179615729/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1320 :
    ((718538701/100000000 : ℚ) : ℝ) ≤ Real.log (1320 : ℕ)
      ∧ Real.log (1320 : ℕ) ≤ ((359269351/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1321 :
    ((71861443/10000000 : ℚ) : ℝ) ≤ Real.log (1321 : ℕ)
      ∧ Real.log (1321 : ℕ) ≤ ((718614431/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1322 :
    ((359345051/50000000 : ℚ) : ℝ) ≤ Real.log (1322 : ℕ)
      ∧ Real.log (1322 : ℕ) ≤ ((718690103/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1323 :
    ((179691429/25000000 : ℚ) : ℝ) ≤ Real.log (1323 : ℕ)
      ∧ Real.log (1323 : ℕ) ≤ ((718765717/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1324 :
    ((718841273/100000000 : ℚ) : ℝ) ≤ Real.log (1324 : ℕ)
      ∧ Real.log (1324 : ℕ) ≤ ((359420637/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1325 :
    ((718916773/100000000 : ℚ) : ℝ) ≤ Real.log (1325 : ℕ)
      ∧ Real.log (1325 : ℕ) ≤ ((359458387/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1326 :
    ((718992217/100000000 : ℚ) : ℝ) ≤ Real.log (1326 : ℕ)
      ∧ Real.log (1326 : ℕ) ≤ ((359496109/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1327 :
    ((719067603/100000000 : ℚ) : ℝ) ≤ Real.log (1327 : ℕ)
      ∧ Real.log (1327 : ℕ) ≤ ((179766901/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1328 :
    ((179785733/25000000 : ℚ) : ℝ) ≤ Real.log (1328 : ℕ)
      ∧ Real.log (1328 : ℕ) ≤ ((359571467/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1329 :
    ((143843641/20000000 : ℚ) : ℝ) ≤ Real.log (1329 : ℕ)
      ∧ Real.log (1329 : ℕ) ≤ ((359609103/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1330 :
    ((359646711/50000000 : ℚ) : ℝ) ≤ Real.log (1330 : ℕ)
      ∧ Real.log (1330 : ℕ) ≤ ((719293423/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1331 :
    ((719368581/100000000 : ℚ) : ℝ) ≤ Real.log (1331 : ℕ)
      ∧ Real.log (1331 : ℕ) ≤ ((359684291/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1332 :
    ((143888737/20000000 : ℚ) : ℝ) ≤ Real.log (1332 : ℕ)
      ∧ Real.log (1332 : ℕ) ≤ ((359721843/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1333 :
    ((719518731/100000000 : ℚ) : ℝ) ≤ Real.log (1333 : ℕ)
      ∧ Real.log (1333 : ℕ) ≤ ((719518733/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1334 :
    ((359796861/50000000 : ℚ) : ℝ) ≤ Real.log (1334 : ℕ)
      ∧ Real.log (1334 : ℕ) ≤ ((719593723/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1335 :
    ((719668657/100000000 : ℚ) : ℝ) ≤ Real.log (1335 : ℕ)
      ∧ Real.log (1335 : ℕ) ≤ ((359834329/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1336 :
    ((143948707/20000000 : ℚ) : ℝ) ≤ Real.log (1336 : ℕ)
      ∧ Real.log (1336 : ℕ) ≤ ((44983971/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1337 :
    ((719818357/100000000 : ℚ) : ℝ) ≤ Real.log (1337 : ℕ)
      ∧ Real.log (1337 : ℕ) ≤ ((359909179/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1338 :
    ((179973281/25000000 : ℚ) : ℝ) ≤ Real.log (1338 : ℕ)
      ∧ Real.log (1338 : ℕ) ≤ ((1151829/160000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1339 :
    ((359983917/50000000 : ℚ) : ℝ) ≤ Real.log (1339 : ℕ)
      ∧ Real.log (1339 : ℕ) ≤ ((143993567/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1340 :
    ((720042489/100000000 : ℚ) : ℝ) ≤ Real.log (1340 : ℕ)
      ∧ Real.log (1340 : ℕ) ≤ ((72004249/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1341 :
    ((22503659/3125000 : ℚ) : ℝ) ≤ Real.log (1341 : ℕ)
      ∧ Real.log (1341 : ℕ) ≤ ((720117089/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1342 :
    ((720191631/100000000 : ℚ) : ℝ) ≤ Real.log (1342 : ℕ)
      ∧ Real.log (1342 : ℕ) ≤ ((45011977/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1343 :
    ((720266119/100000000 : ℚ) : ℝ) ≤ Real.log (1343 : ℕ)
      ∧ Real.log (1343 : ℕ) ≤ ((18006653/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1344 :
    ((90042569/12500000 : ℚ) : ℝ) ≤ Real.log (1344 : ℕ)
      ∧ Real.log (1344 : ℕ) ≤ ((720340553/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1345 :
    ((720414929/100000000 : ℚ) : ℝ) ≤ Real.log (1345 : ℕ)
      ∧ Real.log (1345 : ℕ) ≤ ((72041493/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1346 :
    ((2881957/400000 : ℚ) : ℝ) ≤ Real.log (1346 : ℕ)
      ∧ Real.log (1346 : ℕ) ≤ ((180122313/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1347 :
    ((720563517/100000000 : ℚ) : ℝ) ≤ Real.log (1347 : ℕ)
      ∧ Real.log (1347 : ℕ) ≤ ((360281759/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1348 :
    ((720637729/100000000 : ℚ) : ℝ) ≤ Real.log (1348 : ℕ)
      ∧ Real.log (1348 : ℕ) ≤ ((72063773/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1349 :
    ((144142377/20000000 : ℚ) : ℝ) ≤ Real.log (1349 : ℕ)
      ∧ Real.log (1349 : ℕ) ≤ ((360355943/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1350 :
    ((720785987/100000000 : ℚ) : ℝ) ≤ Real.log (1350 : ℕ)
      ∧ Real.log (1350 : ℕ) ≤ ((180196497/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1351 :
    ((720860033/100000000 : ℚ) : ℝ) ≤ Real.log (1351 : ℕ)
      ∧ Real.log (1351 : ℕ) ≤ ((360430017/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1352 :
    ((28837361/4000000 : ℚ) : ℝ) ≤ Real.log (1352 : ℕ)
      ∧ Real.log (1352 : ℕ) ≤ ((360467013/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1353 :
    ((360503981/50000000 : ℚ) : ℝ) ≤ Real.log (1353 : ℕ)
      ∧ Real.log (1353 : ℕ) ≤ ((721007963/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1354 :
    ((144216369/20000000 : ℚ) : ℝ) ≤ Real.log (1354 : ℕ)
      ∧ Real.log (1354 : ℕ) ≤ ((360540923/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1355 :
    ((721155673/100000000 : ℚ) : ℝ) ≤ Real.log (1355 : ℕ)
      ∧ Real.log (1355 : ℕ) ≤ ((360577837/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1356 :
    ((360614723/50000000 : ℚ) : ℝ) ≤ Real.log (1356 : ℕ)
      ∧ Real.log (1356 : ℕ) ≤ ((721229447/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1357 :
    ((144260633/20000000 : ℚ) : ℝ) ≤ Real.log (1357 : ℕ)
      ∧ Real.log (1357 : ℕ) ≤ ((721303167/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1358 :
    ((72137683/10000000 : ℚ) : ℝ) ≤ Real.log (1358 : ℕ)
      ∧ Real.log (1358 : ℕ) ≤ ((721376831/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1359 :
    ((721450441/100000000 : ℚ) : ℝ) ≤ Real.log (1359 : ℕ)
      ∧ Real.log (1359 : ℕ) ≤ ((360725221/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1360 :
    ((721523997/100000000 : ℚ) : ℝ) ≤ Real.log (1360 : ℕ)
      ∧ Real.log (1360 : ℕ) ≤ ((360761999/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1361 :
    ((288639/40000 : ℚ) : ℝ) ≤ Real.log (1361 : ℕ)
      ∧ Real.log (1361 : ℕ) ≤ ((721597501/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1362 :
    ((180417737/25000000 : ℚ) : ℝ) ≤ Real.log (1362 : ℕ)
      ∧ Real.log (1362 : ℕ) ≤ ((721670949/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1363 :
    ((721744343/100000000 : ℚ) : ℝ) ≤ Real.log (1363 : ℕ)
      ∧ Real.log (1363 : ℕ) ≤ ((90218043/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1364 :
    ((721817683/100000000 : ℚ) : ℝ) ≤ Real.log (1364 : ℕ)
      ∧ Real.log (1364 : ℕ) ≤ ((180454421/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1365 :
    ((72189097/10000000 : ℚ) : ℝ) ≤ Real.log (1365 : ℕ)
      ∧ Real.log (1365 : ℕ) ≤ ((721890971/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1366 :
    ((721964203/100000000 : ℚ) : ℝ) ≤ Real.log (1366 : ℕ)
      ∧ Real.log (1366 : ℕ) ≤ ((144392841/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1367 :
    ((722037383/100000000 : ℚ) : ℝ) ≤ Real.log (1367 : ℕ)
      ∧ Real.log (1367 : ℕ) ≤ ((90254673/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1368 :
    ((722110509/100000000 : ℚ) : ℝ) ≤ Real.log (1368 : ℕ)
      ∧ Real.log (1368 : ℕ) ≤ ((72211051/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1369 :
    ((361091791/50000000 : ℚ) : ℝ) ≤ Real.log (1369 : ℕ)
      ∧ Real.log (1369 : ℕ) ≤ ((722183583/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1370 :
    ((722256601/100000000 : ℚ) : ℝ) ≤ Real.log (1370 : ℕ)
      ∧ Real.log (1370 : ℕ) ≤ ((361128301/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1371 :
    ((722329567/100000000 : ℚ) : ℝ) ≤ Real.log (1371 : ℕ)
      ∧ Real.log (1371 : ℕ) ≤ ((22572799/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1372 :
    ((9030031/1250000 : ℚ) : ℝ) ≤ Real.log (1372 : ℕ)
      ∧ Real.log (1372 : ℕ) ≤ ((722402481/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1373 :
    ((36123767/5000000 : ℚ) : ℝ) ≤ Real.log (1373 : ℕ)
      ∧ Real.log (1373 : ℕ) ≤ ((722475341/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1374 :
    ((722548147/100000000 : ℚ) : ℝ) ≤ Real.log (1374 : ℕ)
      ∧ Real.log (1374 : ℕ) ≤ ((180637037/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1375 :
    ((7226209/1000000 : ℚ) : ℝ) ≤ Real.log (1375 : ℕ)
      ∧ Real.log (1375 : ℕ) ≤ ((361310451/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1376 :
    ((722693601/100000000 : ℚ) : ℝ) ≤ Real.log (1376 : ℕ)
      ∧ Real.log (1376 : ℕ) ≤ ((361346801/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1377 :
    ((722766249/100000000 : ℚ) : ℝ) ≤ Real.log (1377 : ℕ)
      ∧ Real.log (1377 : ℕ) ≤ ((578213/80000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1378 :
    ((144567769/20000000 : ℚ) : ℝ) ≤ Real.log (1378 : ℕ)
      ∧ Real.log (1378 : ℕ) ≤ ((361419423/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1379 :
    ((722911387/100000000 : ℚ) : ℝ) ≤ Real.log (1379 : ℕ)
      ∧ Real.log (1379 : ℕ) ≤ ((180727847/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1380 :
    ((722983877/100000000 : ℚ) : ℝ) ≤ Real.log (1380 : ℕ)
      ∧ Real.log (1380 : ℕ) ≤ ((361491939/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1381 :
    ((144611263/20000000 : ℚ) : ℝ) ≤ Real.log (1381 : ℕ)
      ∧ Real.log (1381 : ℕ) ≤ ((180764079/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1382 :
    ((7231287/1000000 : ℚ) : ℝ) ≤ Real.log (1382 : ℕ)
      ∧ Real.log (1382 : ℕ) ≤ ((723128701/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1383 :
    ((723201033/100000000 : ℚ) : ℝ) ≤ Real.log (1383 : ℕ)
      ∧ Real.log (1383 : ℕ) ≤ ((361600517/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1384 :
    ((723273313/100000000 : ℚ) : ℝ) ≤ Real.log (1384 : ℕ)
      ∧ Real.log (1384 : ℕ) ≤ ((361636657/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1385 :
    ((723345541/100000000 : ℚ) : ℝ) ≤ Real.log (1385 : ℕ)
      ∧ Real.log (1385 : ℕ) ≤ ((361672771/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1386 :
    ((723417717/100000000 : ℚ) : ℝ) ≤ Real.log (1386 : ℕ)
      ∧ Real.log (1386 : ℕ) ≤ ((723417719/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1387 :
    ((723489841/100000000 : ℚ) : ℝ) ≤ Real.log (1387 : ℕ)
      ∧ Real.log (1387 : ℕ) ≤ ((723489843/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1388 :
    ((361780957/50000000 : ℚ) : ℝ) ≤ Real.log (1388 : ℕ)
      ∧ Real.log (1388 : ℕ) ≤ ((144712383/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1389 :
    ((361816967/50000000 : ℚ) : ℝ) ≤ Real.log (1389 : ℕ)
      ∧ Real.log (1389 : ℕ) ≤ ((144726787/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1390 :
    ((361852951/50000000 : ℚ) : ℝ) ≤ Real.log (1390 : ℕ)
      ∧ Real.log (1390 : ℕ) ≤ ((723705903/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1391 :
    ((723777819/100000000 : ℚ) : ℝ) ≤ Real.log (1391 : ℕ)
      ∧ Real.log (1391 : ℕ) ≤ ((36188891/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1392 :
    ((180962421/25000000 : ℚ) : ℝ) ≤ Real.log (1392 : ℕ)
      ∧ Real.log (1392 : ℕ) ≤ ((144769937/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1393 :
    ((723921497/100000000 : ℚ) : ℝ) ≤ Real.log (1393 : ℕ)
      ∧ Real.log (1393 : ℕ) ≤ ((361960749/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1394 :
    ((723993259/100000000 : ℚ) : ℝ) ≤ Real.log (1394 : ℕ)
      ∧ Real.log (1394 : ℕ) ≤ ((36199663/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1395 :
    ((724064969/100000000 : ℚ) : ℝ) ≤ Real.log (1395 : ℕ)
      ∧ Real.log (1395 : ℕ) ≤ ((72406497/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1396 :
    ((181034157/25000000 : ℚ) : ℝ) ≤ Real.log (1396 : ℕ)
      ∧ Real.log (1396 : ℕ) ≤ ((724136629/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1397 :
    ((144841647/20000000 : ℚ) : ℝ) ≤ Real.log (1397 : ℕ)
      ∧ Real.log (1397 : ℕ) ≤ ((181052059/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1398 :
    ((45267487/6250000 : ℚ) : ℝ) ≤ Real.log (1398 : ℕ)
      ∧ Real.log (1398 : ℕ) ≤ ((724279793/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1399 :
    ((724351297/100000000 : ℚ) : ℝ) ≤ Real.log (1399 : ℕ)
      ∧ Real.log (1399 : ℕ) ≤ ((362175649/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1400 :
    ((724422751/100000000 : ℚ) : ℝ) ≤ Real.log (1400 : ℕ)
      ∧ Real.log (1400 : ℕ) ≤ ((22638211/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1401 :
    ((362247077/50000000 : ℚ) : ℝ) ≤ Real.log (1401 : ℕ)
      ∧ Real.log (1401 : ℕ) ≤ ((144898831/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1402 :
    ((362282753/50000000 : ℚ) : ℝ) ≤ Real.log (1402 : ℕ)
      ∧ Real.log (1402 : ℕ) ≤ ((724565507/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1403 :
    ((724636807/100000000 : ℚ) : ℝ) ≤ Real.log (1403 : ℕ)
      ∧ Real.log (1403 : ℕ) ≤ ((724636809/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1404 :
    ((362354029/50000000 : ℚ) : ℝ) ≤ Real.log (1404 : ℕ)
      ∧ Real.log (1404 : ℕ) ≤ ((724708059/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1405 :
    ((362389629/50000000 : ℚ) : ℝ) ≤ Real.log (1405 : ℕ)
      ∧ Real.log (1405 : ℕ) ≤ ((724779259/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1406 :
    ((724850407/100000000 : ℚ) : ℝ) ≤ Real.log (1406 : ℕ)
      ∧ Real.log (1406 : ℕ) ≤ ((90606301/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1407 :
    ((144984301/20000000 : ℚ) : ℝ) ≤ Real.log (1407 : ℕ)
      ∧ Real.log (1407 : ℕ) ≤ ((362460753/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1408 :
    ((724992553/100000000 : ℚ) : ℝ) ≤ Real.log (1408 : ℕ)
      ∧ Real.log (1408 : ℕ) ≤ ((362496277/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1409 :
    ((725063551/100000000 : ℚ) : ℝ) ≤ Real.log (1409 : ℕ)
      ∧ Real.log (1409 : ℕ) ≤ ((5664559/781250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1410 :
    ((362567249/50000000 : ℚ) : ℝ) ≤ Real.log (1410 : ℕ)
      ∧ Real.log (1410 : ℕ) ≤ ((725134499/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1411 :
    ((145041079/20000000 : ℚ) : ℝ) ≤ Real.log (1411 : ℕ)
      ∧ Real.log (1411 : ℕ) ≤ ((181301349/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1412 :
    ((725276241/100000000 : ℚ) : ℝ) ≤ Real.log (1412 : ℕ)
      ∧ Real.log (1412 : ℕ) ≤ ((362638121/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1413 :
    ((362673519/50000000 : ℚ) : ℝ) ≤ Real.log (1413 : ℕ)
      ∧ Real.log (1413 : ℕ) ≤ ((725347039/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1414 :
    ((90677223/12500000 : ℚ) : ℝ) ≤ Real.log (1414 : ℕ)
      ∧ Real.log (1414 : ℕ) ≤ ((145083557/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1415 :
    ((4534303/625000 : ℚ) : ℝ) ≤ Real.log (1415 : ℕ)
      ∧ Real.log (1415 : ℕ) ≤ ((362744241/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1416 :
    ((725559127/100000000 : ℚ) : ℝ) ≤ Real.log (1416 : ℕ)
      ∧ Real.log (1416 : ℕ) ≤ ((90694891/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1417 :
    ((725629723/100000000 : ℚ) : ℝ) ≤ Real.log (1417 : ℕ)
      ∧ Real.log (1417 : ℕ) ≤ ((29025189/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1418 :
    ((72570027/10000000 : ℚ) : ℝ) ≤ Real.log (1418 : ℕ)
      ∧ Real.log (1418 : ℕ) ≤ ((725700271/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1419 :
    ((725770767/100000000 : ℚ) : ℝ) ≤ Real.log (1419 : ℕ)
      ∧ Real.log (1419 : ℕ) ≤ ((45360673/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1420 :
    ((145168243/20000000 : ℚ) : ℝ) ≤ Real.log (1420 : ℕ)
      ∧ Real.log (1420 : ℕ) ≤ ((11341269/1562500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1421 :
    ((181477903/25000000 : ℚ) : ℝ) ≤ Real.log (1421 : ℕ)
      ∧ Real.log (1421 : ℕ) ≤ ((725911613/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1422 :
    ((18149549/2500000 : ℚ) : ℝ) ≤ Real.log (1422 : ℕ)
      ∧ Real.log (1422 : ℕ) ≤ ((362990981/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1423 :
    ((726052259/100000000 : ℚ) : ℝ) ≤ Real.log (1423 : ℕ)
      ∧ Real.log (1423 : ℕ) ≤ ((36302613/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1424 :
    ((726122509/100000000 : ℚ) : ℝ) ≤ Real.log (1424 : ℕ)
      ∧ Real.log (1424 : ℕ) ≤ ((72612251/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1425 :
    ((726192709/100000000 : ℚ) : ℝ) ≤ Real.log (1425 : ℕ)
      ∧ Real.log (1425 : ℕ) ≤ ((72619271/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1426 :
    ((36313143/5000000 : ℚ) : ℝ) ≤ Real.log (1426 : ℕ)
      ∧ Real.log (1426 : ℕ) ≤ ((726262861/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1427 :
    ((726332961/100000000 : ℚ) : ℝ) ≤ Real.log (1427 : ℕ)
      ∧ Real.log (1427 : ℕ) ≤ ((363166481/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1428 :
    ((363201507/50000000 : ℚ) : ℝ) ≤ Real.log (1428 : ℕ)
      ∧ Real.log (1428 : ℕ) ≤ ((145280603/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1429 :
    ((726473017/100000000 : ℚ) : ℝ) ≤ Real.log (1429 : ℕ)
      ∧ Real.log (1429 : ℕ) ≤ ((363236509/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1430 :
    ((181635743/25000000 : ℚ) : ℝ) ≤ Real.log (1430 : ℕ)
      ∧ Real.log (1430 : ℕ) ≤ ((726542973/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1431 :
    ((726612877/100000000 : ℚ) : ℝ) ≤ Real.log (1431 : ℕ)
      ∧ Real.log (1431 : ℕ) ≤ ((363306439/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1432 :
    ((363341367/50000000 : ℚ) : ℝ) ≤ Real.log (1432 : ℕ)
      ∧ Real.log (1432 : ℕ) ≤ ((145336547/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1433 :
    ((363376271/50000000 : ℚ) : ℝ) ≤ Real.log (1433 : ℕ)
      ∧ Real.log (1433 : ℕ) ≤ ((726752543/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1434 :
    ((363411151/50000000 : ℚ) : ℝ) ≤ Real.log (1434 : ℕ)
      ∧ Real.log (1434 : ℕ) ≤ ((726822303/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1435 :
    ((181723003/25000000 : ℚ) : ℝ) ≤ Real.log (1435 : ℕ)
      ∧ Real.log (1435 : ℕ) ≤ ((726892013/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1436 :
    ((363480837/50000000 : ℚ) : ℝ) ≤ Real.log (1436 : ℕ)
      ∧ Real.log (1436 : ℕ) ≤ ((181740419/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1437 :
    ((90878911/12500000 : ℚ) : ℝ) ≤ Real.log (1437 : ℕ)
      ∧ Real.log (1437 : ℕ) ≤ ((727031289/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1438 :
    ((727100853/100000000 : ℚ) : ℝ) ≤ Real.log (1438 : ℕ)
      ∧ Real.log (1438 : ℕ) ≤ ((363550427/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1439 :
    ((72717037/10000000 : ℚ) : ℝ) ≤ Real.log (1439 : ℕ)
      ∧ Real.log (1439 : ℕ) ≤ ((727170371/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1440 :
    ((727239839/100000000 : ℚ) : ℝ) ≤ Real.log (1440 : ℕ)
      ∧ Real.log (1440 : ℕ) ≤ ((4545249/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1441 :
    ((727309259/100000000 : ℚ) : ℝ) ≤ Real.log (1441 : ℕ)
      ∧ Real.log (1441 : ℕ) ≤ ((36365463/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1442 :
    ((727378631/100000000 : ℚ) : ℝ) ≤ Real.log (1442 : ℕ)
      ∧ Real.log (1442 : ℕ) ≤ ((90922329/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1443 :
    ((145489591/20000000 : ℚ) : ℝ) ≤ Real.log (1443 : ℕ)
      ∧ Real.log (1443 : ℕ) ≤ ((181861989/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1444 :
    ((727517231/100000000 : ℚ) : ℝ) ≤ Real.log (1444 : ℕ)
      ∧ Real.log (1444 : ℕ) ≤ ((45469827/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1445 :
    ((36379323/5000000 : ℚ) : ℝ) ≤ Real.log (1445 : ℕ)
      ∧ Real.log (1445 : ℕ) ≤ ((727586461/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1446 :
    ((18191391/2500000 : ℚ) : ℝ) ≤ Real.log (1446 : ℕ)
      ∧ Real.log (1446 : ℕ) ≤ ((727655641/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1447 :
    ((181931193/25000000 : ℚ) : ℝ) ≤ Real.log (1447 : ℕ)
      ∧ Real.log (1447 : ℕ) ≤ ((727724773/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1448 :
    ((727793857/100000000 : ℚ) : ℝ) ≤ Real.log (1448 : ℕ)
      ∧ Real.log (1448 : ℕ) ≤ ((363896929/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1449 :
    ((363931447/50000000 : ℚ) : ℝ) ≤ Real.log (1449 : ℕ)
      ∧ Real.log (1449 : ℕ) ≤ ((145572579/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1450 :
    ((727931883/100000000 : ℚ) : ℝ) ≤ Real.log (1450 : ℕ)
      ∧ Real.log (1450 : ℕ) ≤ ((181982971/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1451 :
    ((29120033/4000000 : ℚ) : ℝ) ≤ Real.log (1451 : ℕ)
      ∧ Real.log (1451 : ℕ) ≤ ((364000413/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1452 :
    ((728069719/100000000 : ℚ) : ℝ) ≤ Real.log (1452 : ℕ)
      ∧ Real.log (1452 : ℕ) ≤ ((18201743/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1453 :
    ((364069283/50000000 : ℚ) : ℝ) ≤ Real.log (1453 : ℕ)
      ∧ Real.log (1453 : ℕ) ≤ ((728138567/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1454 :
    ((145641473/20000000 : ℚ) : ℝ) ≤ Real.log (1454 : ℕ)
      ∧ Real.log (1454 : ℕ) ≤ ((364103683/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1455 :
    ((728276117/100000000 : ℚ) : ℝ) ≤ Real.log (1455 : ℕ)
      ∧ Real.log (1455 : ℕ) ≤ ((728276119/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1456 :
    ((364172411/50000000 : ℚ) : ℝ) ≤ Real.log (1456 : ℕ)
      ∧ Real.log (1456 : ℕ) ≤ ((728344823/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1457 :
    ((18210337/2500000 : ℚ) : ℝ) ≤ Real.log (1457 : ℕ)
      ∧ Real.log (1457 : ℕ) ≤ ((728413481/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1458 :
    ((728482091/100000000 : ℚ) : ℝ) ≤ Real.log (1458 : ℕ)
      ∧ Real.log (1458 : ℕ) ≤ ((182120523/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1459 :
    ((364275327/50000000 : ℚ) : ℝ) ≤ Real.log (1459 : ℕ)
      ∧ Real.log (1459 : ℕ) ≤ ((145710131/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1460 :
    ((728619171/100000000 : ℚ) : ℝ) ≤ Real.log (1460 : ℕ)
      ∧ Real.log (1460 : ℕ) ≤ ((182154793/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1461 :
    ((728687641/100000000 : ℚ) : ℝ) ≤ Real.log (1461 : ℕ)
      ∧ Real.log (1461 : ℕ) ≤ ((364343821/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1462 :
    ((728756063/100000000 : ℚ) : ℝ) ≤ Real.log (1462 : ℕ)
      ∧ Real.log (1462 : ℕ) ≤ ((145751213/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1463 :
    ((18220611/2500000 : ℚ) : ℝ) ≤ Real.log (1463 : ℕ)
      ∧ Real.log (1463 : ℕ) ≤ ((728824441/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1464 :
    ((728892769/100000000 : ℚ) : ℝ) ≤ Real.log (1464 : ℕ)
      ∧ Real.log (1464 : ℕ) ≤ ((72889277/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1465 :
    ((182240263/25000000 : ℚ) : ℝ) ≤ Real.log (1465 : ℕ)
      ∧ Real.log (1465 : ℕ) ≤ ((728961053/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1466 :
    ((91128661/12500000 : ℚ) : ℝ) ≤ Real.log (1466 : ℕ)
      ∧ Real.log (1466 : ℕ) ≤ ((729029289/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1467 :
    ((729097477/100000000 : ℚ) : ℝ) ≤ Real.log (1467 : ℕ)
      ∧ Real.log (1467 : ℕ) ≤ ((364548739/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1468 :
    ((36458281/5000000 : ℚ) : ℝ) ≤ Real.log (1468 : ℕ)
      ∧ Real.log (1468 : ℕ) ≤ ((729165621/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1469 :
    ((729233717/100000000 : ℚ) : ℝ) ≤ Real.log (1469 : ℕ)
      ∧ Real.log (1469 : ℕ) ≤ ((364616859/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1470 :
    ((729301767/100000000 : ℚ) : ℝ) ≤ Real.log (1470 : ℕ)
      ∧ Real.log (1470 : ℕ) ≤ ((729301769/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1471 :
    ((182342443/25000000 : ℚ) : ℝ) ≤ Real.log (1471 : ℕ)
      ∧ Real.log (1471 : ℕ) ≤ ((729369773/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1472 :
    ((729437729/100000000 : ℚ) : ℝ) ≤ Real.log (1472 : ℕ)
      ∧ Real.log (1472 : ℕ) ≤ ((72943773/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1473 :
    ((729505641/100000000 : ℚ) : ℝ) ≤ Real.log (1473 : ℕ)
      ∧ Real.log (1473 : ℕ) ≤ ((364752821/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1474 :
    ((729573507/100000000 : ℚ) : ℝ) ≤ Real.log (1474 : ℕ)
      ∧ Real.log (1474 : ℕ) ≤ ((182393377/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1475 :
    ((364820663/50000000 : ℚ) : ℝ) ≤ Real.log (1475 : ℕ)
      ∧ Real.log (1475 : ℕ) ≤ ((729641327/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1476 :
    ((7297091/1000000 : ℚ) : ℝ) ≤ Real.log (1476 : ℕ)
      ∧ Real.log (1476 : ℕ) ≤ ((729709101/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1477 :
    ((182444207/25000000 : ℚ) : ℝ) ≤ Real.log (1477 : ℕ)
      ∧ Real.log (1477 : ℕ) ≤ ((729776829/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1478 :
    ((72984451/10000000 : ℚ) : ℝ) ≤ Real.log (1478 : ℕ)
      ∧ Real.log (1478 : ℕ) ≤ ((729844511/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1479 :
    ((364956073/50000000 : ℚ) : ℝ) ≤ Real.log (1479 : ℕ)
      ∧ Real.log (1479 : ℕ) ≤ ((729912147/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1480 :
    ((91247467/12500000 : ℚ) : ℝ) ≤ Real.log (1480 : ℕ)
      ∧ Real.log (1480 : ℕ) ≤ ((729979737/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1481 :
    ((730047281/100000000 : ℚ) : ℝ) ≤ Real.log (1481 : ℕ)
      ∧ Real.log (1481 : ℕ) ≤ ((365023641/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1482 :
    ((36505739/5000000 : ℚ) : ℝ) ≤ Real.log (1482 : ℕ)
      ∧ Real.log (1482 : ℕ) ≤ ((730114781/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1483 :
    ((365091117/50000000 : ℚ) : ℝ) ≤ Real.log (1483 : ℕ)
      ∧ Real.log (1483 : ℕ) ≤ ((146036447/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1484 :
    ((365124821/50000000 : ℚ) : ℝ) ≤ Real.log (1484 : ℕ)
      ∧ Real.log (1484 : ℕ) ≤ ((730249643/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1485 :
    ((146063401/20000000 : ℚ) : ℝ) ≤ Real.log (1485 : ℕ)
      ∧ Real.log (1485 : ℕ) ≤ ((365158503/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1486 :
    ((365192161/50000000 : ℚ) : ℝ) ≤ Real.log (1486 : ℕ)
      ∧ Real.log (1486 : ℕ) ≤ ((730384323/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1487 :
    ((365225797/50000000 : ℚ) : ℝ) ≤ Real.log (1487 : ℕ)
      ∧ Real.log (1487 : ℕ) ≤ ((146090319/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1488 :
    ((730518821/100000000 : ℚ) : ℝ) ≤ Real.log (1488 : ℕ)
      ∧ Real.log (1488 : ℕ) ≤ ((365259411/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1489 :
    ((730586003/100000000 : ℚ) : ℝ) ≤ Real.log (1489 : ℕ)
      ∧ Real.log (1489 : ℕ) ≤ ((182646501/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1490 :
    ((730653139/100000000 : ℚ) : ℝ) ≤ Real.log (1490 : ℕ)
      ∧ Real.log (1490 : ℕ) ≤ ((36532657/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1491 :
    ((730720231/100000000 : ℚ) : ℝ) ≤ Real.log (1491 : ℕ)
      ∧ Real.log (1491 : ℕ) ≤ ((91340029/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1492 :
    ((365393639/50000000 : ℚ) : ℝ) ≤ Real.log (1492 : ℕ)
      ∧ Real.log (1492 : ℕ) ≤ ((730787279/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1493 :
    ((730854279/100000000 : ℚ) : ℝ) ≤ Real.log (1493 : ℕ)
      ∧ Real.log (1493 : ℕ) ≤ ((18271357/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1494 :
    ((182730309/25000000 : ℚ) : ℝ) ≤ Real.log (1494 : ℕ)
      ∧ Real.log (1494 : ℕ) ≤ ((730921237/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1495 :
    ((182747037/25000000 : ℚ) : ℝ) ≤ Real.log (1495 : ℕ)
      ∧ Real.log (1495 : ℕ) ≤ ((730988149/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1496 :
    ((146211003/20000000 : ℚ) : ℝ) ≤ Real.log (1496 : ℕ)
      ∧ Real.log (1496 : ℕ) ≤ ((91381877/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1497 :
    ((365560919/50000000 : ℚ) : ℝ) ≤ Real.log (1497 : ℕ)
      ∧ Real.log (1497 : ℕ) ≤ ((731121839/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1498 :
    ((91398577/12500000 : ℚ) : ℝ) ≤ Real.log (1498 : ℕ)
      ∧ Real.log (1498 : ℕ) ≤ ((731188617/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1499 :
    ((731255349/100000000 : ℚ) : ℝ) ≤ Real.log (1499 : ℕ)
      ∧ Real.log (1499 : ℕ) ≤ ((14625107/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1500 :
    ((365661019/50000000 : ℚ) : ℝ) ≤ Real.log (1500 : ℕ)
      ∧ Real.log (1500 : ℕ) ≤ ((731322039/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1501 :
    ((731388683/100000000 : ℚ) : ℝ) ≤ Real.log (1501 : ℕ)
      ∧ Real.log (1501 : ℕ) ≤ ((182847171/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1502 :
    ((731455283/100000000 : ℚ) : ℝ) ≤ Real.log (1502 : ℕ)
      ∧ Real.log (1502 : ℕ) ≤ ((182863821/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1503 :
    ((365760919/50000000 : ℚ) : ℝ) ≤ Real.log (1503 : ℕ)
      ∧ Real.log (1503 : ℕ) ≤ ((9144023/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1504 :
    ((14631767/2000000 : ℚ) : ℝ) ≤ Real.log (1504 : ℕ)
      ∧ Real.log (1504 : ℕ) ≤ ((731588351/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1505 :
    ((731654817/100000000 : ℚ) : ℝ) ≤ Real.log (1505 : ℕ)
      ∧ Real.log (1505 : ℕ) ≤ ((365827409/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1506 :
    ((18293031/2500000 : ℚ) : ℝ) ≤ Real.log (1506 : ℕ)
      ∧ Real.log (1506 : ℕ) ≤ ((731721241/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1507 :
    ((731787619/100000000 : ℚ) : ℝ) ≤ Real.log (1507 : ℕ)
      ∧ Real.log (1507 : ℕ) ≤ ((36589381/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1508 :
    ((365926977/50000000 : ℚ) : ℝ) ≤ Real.log (1508 : ℕ)
      ∧ Real.log (1508 : ℕ) ≤ ((146370791/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1509 :
    ((146384049/20000000 : ℚ) : ℝ) ≤ Real.log (1509 : ℕ)
      ∧ Real.log (1509 : ℕ) ≤ ((365960123/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1510 :
    ((182996623/25000000 : ℚ) : ℝ) ≤ Real.log (1510 : ℕ)
      ∧ Real.log (1510 : ℕ) ≤ ((365993247/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1511 :
    ((91506587/12500000 : ℚ) : ℝ) ≤ Real.log (1511 : ℕ)
      ∧ Real.log (1511 : ℕ) ≤ ((732052697/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1512 :
    ((146423771/20000000 : ℚ) : ℝ) ≤ Real.log (1512 : ℕ)
      ∧ Real.log (1512 : ℕ) ≤ ((91514857/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1513 :
    ((732184971/100000000 : ℚ) : ℝ) ≤ Real.log (1513 : ℕ)
      ∧ Real.log (1513 : ℕ) ≤ ((183046243/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1514 :
    ((732251043/100000000 : ℚ) : ℝ) ≤ Real.log (1514 : ℕ)
      ∧ Real.log (1514 : ℕ) ≤ ((183062761/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1515 :
    ((732317071/100000000 : ℚ) : ℝ) ≤ Real.log (1515 : ℕ)
      ∧ Real.log (1515 : ℕ) ≤ ((45769817/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1516 :
    ((45773941/6250000 : ℚ) : ℝ) ≤ Real.log (1516 : ℕ)
      ∧ Real.log (1516 : ℕ) ≤ ((732383057/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1517 :
    ((732448997/100000000 : ℚ) : ℝ) ≤ Real.log (1517 : ℕ)
      ∧ Real.log (1517 : ℕ) ≤ ((366224499/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1518 :
    ((146502979/20000000 : ℚ) : ℝ) ≤ Real.log (1518 : ℕ)
      ∧ Real.log (1518 : ℕ) ≤ ((45782181/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1519 :
    ((2930323/400000 : ℚ) : ℝ) ≤ Real.log (1519 : ℕ)
      ∧ Real.log (1519 : ℕ) ≤ ((732580751/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1520 :
    ((732646561/100000000 : ℚ) : ℝ) ≤ Real.log (1520 : ℕ)
      ∧ Real.log (1520 : ℕ) ≤ ((366323281/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1521 :
    ((732712329/100000000 : ℚ) : ℝ) ≤ Real.log (1521 : ℕ)
      ∧ Real.log (1521 : ℕ) ≤ ((73271233/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1522 :
    ((732778053/100000000 : ℚ) : ℝ) ≤ Real.log (1522 : ℕ)
      ∧ Real.log (1522 : ℕ) ≤ ((366389027/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1523 :
    ((146568747/20000000 : ℚ) : ℝ) ≤ Real.log (1523 : ℕ)
      ∧ Real.log (1523 : ℕ) ≤ ((91605467/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1524 :
    ((732909373/100000000 : ℚ) : ℝ) ≤ Real.log (1524 : ℕ)
      ∧ Real.log (1524 : ℕ) ≤ ((366454687/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1525 :
    ((91621871/12500000 : ℚ) : ℝ) ≤ Real.log (1525 : ℕ)
      ∧ Real.log (1525 : ℕ) ≤ ((732974969/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1526 :
    ((733040521/100000000 : ℚ) : ℝ) ≤ Real.log (1526 : ℕ)
      ∧ Real.log (1526 : ℕ) ≤ ((366520261/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1527 :
    ((73310603/10000000 : ℚ) : ℝ) ≤ Real.log (1527 : ℕ)
      ∧ Real.log (1527 : ℕ) ≤ ((733106031/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1528 :
    ((91646437/12500000 : ℚ) : ℝ) ≤ Real.log (1528 : ℕ)
      ∧ Real.log (1528 : ℕ) ≤ ((366585749/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1529 :
    ((18330923/2500000 : ℚ) : ℝ) ≤ Real.log (1529 : ℕ)
      ∧ Real.log (1529 : ℕ) ≤ ((733236921/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1530 :
    ((733302301/100000000 : ℚ) : ℝ) ≤ Real.log (1530 : ℕ)
      ∧ Real.log (1530 : ℕ) ≤ ((366651151/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1531 :
    ((733367639/100000000 : ℚ) : ℝ) ≤ Real.log (1531 : ℕ)
      ∧ Real.log (1531 : ℕ) ≤ ((18334191/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1532 :
    ((366716467/50000000 : ℚ) : ℝ) ≤ Real.log (1532 : ℕ)
      ∧ Real.log (1532 : ℕ) ≤ ((91679117/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1533 :
    ((733498187/100000000 : ℚ) : ℝ) ≤ Real.log (1533 : ℕ)
      ∧ Real.log (1533 : ℕ) ≤ ((183374547/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1534 :
    ((366781699/50000000 : ℚ) : ℝ) ≤ Real.log (1534 : ℕ)
      ∧ Real.log (1534 : ℕ) ≤ ((733563399/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1535 :
    ((146725713/20000000 : ℚ) : ℝ) ≤ Real.log (1535 : ℕ)
      ∧ Real.log (1535 : ℕ) ≤ ((733628567/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1536 :
    ((733693691/100000000 : ℚ) : ℝ) ≤ Real.log (1536 : ℕ)
      ∧ Real.log (1536 : ℕ) ≤ ((183423423/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1537 :
    ((366879387/50000000 : ℚ) : ℝ) ≤ Real.log (1537 : ℕ)
      ∧ Real.log (1537 : ℕ) ≤ ((29350351/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1538 :
    ((366911907/50000000 : ℚ) : ℝ) ≤ Real.log (1538 : ℕ)
      ∧ Real.log (1538 : ℕ) ≤ ((91727977/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1539 :
    ((733888813/100000000 : ℚ) : ℝ) ≤ Real.log (1539 : ℕ)
      ∧ Real.log (1539 : ℕ) ≤ ((366944407/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1540 :
    ((733953769/100000000 : ℚ) : ℝ) ≤ Real.log (1540 : ℕ)
      ∧ Real.log (1540 : ℕ) ≤ ((73395377/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1541 :
    ((734018683/100000000 : ℚ) : ℝ) ≤ Real.log (1541 : ℕ)
      ∧ Real.log (1541 : ℕ) ≤ ((183504671/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1542 :
    ((146816711/20000000 : ℚ) : ℝ) ≤ Real.log (1542 : ℕ)
      ∧ Real.log (1542 : ℕ) ≤ ((183520889/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1543 :
    ((146829677/20000000 : ℚ) : ℝ) ≤ Real.log (1543 : ℕ)
      ∧ Real.log (1543 : ℕ) ≤ ((367074193/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1544 :
    ((734213173/100000000 : ℚ) : ℝ) ≤ Real.log (1544 : ℕ)
      ∧ Real.log (1544 : ℕ) ≤ ((367106587/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1545 :
    ((367138959/50000000 : ℚ) : ℝ) ≤ Real.log (1545 : ℕ)
      ∧ Real.log (1545 : ℕ) ≤ ((4589237/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1546 :
    ((367171311/50000000 : ℚ) : ℝ) ≤ Real.log (1546 : ℕ)
      ∧ Real.log (1546 : ℕ) ≤ ((734342623/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1547 :
    ((146881457/20000000 : ℚ) : ℝ) ≤ Real.log (1547 : ℕ)
      ∧ Real.log (1547 : ℕ) ≤ ((367203643/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1548 :
    ((146894381/20000000 : ℚ) : ℝ) ≤ Real.log (1548 : ℕ)
      ∧ Real.log (1548 : ℕ) ≤ ((367235953/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1549 :
    ((183634121/25000000 : ℚ) : ℝ) ≤ Real.log (1549 : ℕ)
      ∧ Real.log (1549 : ℕ) ≤ ((146907297/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1550 :
    ((36730051/5000000 : ℚ) : ℝ) ≤ Real.log (1550 : ℕ)
      ∧ Real.log (1550 : ℕ) ≤ ((367300511/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1551 :
    ((183666379/25000000 : ℚ) : ℝ) ≤ Real.log (1551 : ℕ)
      ∧ Real.log (1551 : ℕ) ≤ ((734665517/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1552 :
    ((73472997/10000000 : ℚ) : ℝ) ≤ Real.log (1552 : ℕ)
      ∧ Real.log (1552 : ℕ) ≤ ((734729971/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1553 :
    ((367397191/50000000 : ℚ) : ℝ) ≤ Real.log (1553 : ℕ)
      ∧ Real.log (1553 : ℕ) ≤ ((734794383/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1554 :
    ((734858753/100000000 : ℚ) : ℝ) ≤ Real.log (1554 : ℕ)
      ∧ Real.log (1554 : ℕ) ≤ ((367429377/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1555 :
    ((367461541/50000000 : ℚ) : ℝ) ≤ Real.log (1555 : ℕ)
      ∧ Real.log (1555 : ℕ) ≤ ((734923083/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1556 :
    ((73498737/10000000 : ℚ) : ℝ) ≤ Real.log (1556 : ℕ)
      ∧ Real.log (1556 : ℕ) ≤ ((734987371/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1557 :
    ((735051617/100000000 : ℚ) : ℝ) ≤ Real.log (1557 : ℕ)
      ∧ Real.log (1557 : ℕ) ≤ ((367525809/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1558 :
    ((367557911/50000000 : ℚ) : ℝ) ≤ Real.log (1558 : ℕ)
      ∧ Real.log (1558 : ℕ) ≤ ((735115823/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1559 :
    ((367589993/50000000 : ℚ) : ℝ) ≤ Real.log (1559 : ℕ)
      ∧ Real.log (1559 : ℕ) ≤ ((735179987/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1560 :
    ((735244109/100000000 : ℚ) : ℝ) ≤ Real.log (1560 : ℕ)
      ∧ Real.log (1560 : ℕ) ≤ ((735244111/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1561 :
    ((22978381/3125000 : ℚ) : ℝ) ≤ Real.log (1561 : ℕ)
      ∧ Real.log (1561 : ℕ) ≤ ((735308193/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1562 :
    ((735372233/100000000 : ℚ) : ℝ) ≤ Real.log (1562 : ℕ)
      ∧ Real.log (1562 : ℕ) ≤ ((367686117/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1563 :
    ((735436233/100000000 : ℚ) : ℝ) ≤ Real.log (1563 : ℕ)
      ∧ Real.log (1563 : ℕ) ≤ ((367718117/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1564 :
    ((22984381/3125000 : ℚ) : ℝ) ≤ Real.log (1564 : ℕ)
      ∧ Real.log (1564 : ℕ) ≤ ((735500193/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1565 :
    ((73556411/10000000 : ℚ) : ℝ) ≤ Real.log (1565 : ℕ)
      ∧ Real.log (1565 : ℕ) ≤ ((735564111/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1566 :
    ((735627987/100000000 : ℚ) : ℝ) ≤ Real.log (1566 : ℕ)
      ∧ Real.log (1566 : ℕ) ≤ ((183906997/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1567 :
    ((45980739/6250000 : ℚ) : ℝ) ≤ Real.log (1567 : ℕ)
      ∧ Real.log (1567 : ℕ) ≤ ((29427673/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1568 :
    ((36787781/5000000 : ℚ) : ℝ) ≤ Real.log (1568 : ℕ)
      ∧ Real.log (1568 : ℕ) ≤ ((735755621/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1569 :
    ((1177311/160000 : ℚ) : ℝ) ≤ Real.log (1569 : ℕ)
      ∧ Real.log (1569 : ℕ) ≤ ((45988711/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1570 :
    ((735883089/100000000 : ℚ) : ℝ) ≤ Real.log (1570 : ℕ)
      ∧ Real.log (1570 : ℕ) ≤ ((73588309/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1571 :
    ((735946763/100000000 : ℚ) : ℝ) ≤ Real.log (1571 : ℕ)
      ∧ Real.log (1571 : ℕ) ≤ ((183986691/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1572 :
    ((736010397/100000000 : ℚ) : ℝ) ≤ Real.log (1572 : ℕ)
      ∧ Real.log (1572 : ℕ) ≤ ((368005199/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1573 :
    ((73607399/10000000 : ℚ) : ℝ) ≤ Real.log (1573 : ℕ)
      ∧ Real.log (1573 : ℕ) ≤ ((736073991/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1574 :
    ((368068771/50000000 : ℚ) : ℝ) ≤ Real.log (1574 : ℕ)
      ∧ Real.log (1574 : ℕ) ≤ ((736137543/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1575 :
    ((147240211/20000000 : ℚ) : ℝ) ≤ Real.log (1575 : ℕ)
      ∧ Real.log (1575 : ℕ) ≤ ((23006283/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1576 :
    ((736264527/100000000 : ℚ) : ℝ) ≤ Real.log (1576 : ℕ)
      ∧ Real.log (1576 : ℕ) ≤ ((46016533/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1577 :
    ((368163979/50000000 : ℚ) : ℝ) ≤ Real.log (1577 : ℕ)
      ∧ Real.log (1577 : ℕ) ≤ ((736327959/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1578 :
    ((14727827/2000000 : ℚ) : ℝ) ≤ Real.log (1578 : ℕ)
      ∧ Real.log (1578 : ℕ) ≤ ((736391351/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1579 :
    ((736454701/100000000 : ℚ) : ℝ) ≤ Real.log (1579 : ℕ)
      ∧ Real.log (1579 : ℕ) ≤ ((368227351/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1580 :
    ((184129503/25000000 : ℚ) : ℝ) ≤ Real.log (1580 : ℕ)
      ∧ Real.log (1580 : ℕ) ≤ ((736518013/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1581 :
    ((736581283/100000000 : ℚ) : ℝ) ≤ Real.log (1581 : ℕ)
      ∧ Real.log (1581 : ℕ) ≤ ((184145321/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1582 :
    ((368322257/50000000 : ℚ) : ℝ) ≤ Real.log (1582 : ℕ)
      ∧ Real.log (1582 : ℕ) ≤ ((147328903/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1583 :
    ((147341541/20000000 : ℚ) : ℝ) ≤ Real.log (1583 : ℕ)
      ∧ Real.log (1583 : ℕ) ≤ ((736707707/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1584 :
    ((736770857/100000000 : ℚ) : ℝ) ≤ Real.log (1584 : ℕ)
      ∧ Real.log (1584 : ℕ) ≤ ((368385429/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1585 :
    ((46052123/6250000 : ℚ) : ℝ) ≤ Real.log (1585 : ℕ)
      ∧ Real.log (1585 : ℕ) ≤ ((736833969/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1586 :
    ((9211213/1250000 : ℚ) : ℝ) ≤ Real.log (1586 : ℕ)
      ∧ Real.log (1586 : ℕ) ≤ ((736897041/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1587 :
    ((92120009/12500000 : ℚ) : ℝ) ≤ Real.log (1587 : ℕ)
      ∧ Real.log (1587 : ℕ) ≤ ((736960073/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1588 :
    ((92127883/12500000 : ℚ) : ℝ) ≤ Real.log (1588 : ℕ)
      ∧ Real.log (1588 : ℕ) ≤ ((147404613/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1589 :
    ((11516969/1562500 : ℚ) : ℝ) ≤ Real.log (1589 : ℕ)
      ∧ Real.log (1589 : ℕ) ≤ ((737086017/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1590 :
    ((737148929/100000000 : ℚ) : ℝ) ≤ Real.log (1590 : ℕ)
      ∧ Real.log (1590 : ℕ) ≤ ((73714893/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1591 :
    ((368605901/50000000 : ℚ) : ℝ) ≤ Real.log (1591 : ℕ)
      ∧ Real.log (1591 : ℕ) ≤ ((737211803/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1592 :
    ((184318659/25000000 : ℚ) : ℝ) ≤ Real.log (1592 : ℕ)
      ∧ Real.log (1592 : ℕ) ≤ ((737274637/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1593 :
    ((73733743/10000000 : ℚ) : ℝ) ≤ Real.log (1593 : ℕ)
      ∧ Real.log (1593 : ℕ) ≤ ((92167179/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1594 :
    ((147480037/20000000 : ℚ) : ℝ) ≤ Real.log (1594 : ℕ)
      ∧ Real.log (1594 : ℕ) ≤ ((737400187/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1595 :
    ((737462901/100000000 : ℚ) : ℝ) ≤ Real.log (1595 : ℕ)
      ∧ Real.log (1595 : ℕ) ≤ ((368731451/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1596 :
    ((737525577/100000000 : ℚ) : ℝ) ≤ Real.log (1596 : ℕ)
      ∧ Real.log (1596 : ℕ) ≤ ((368762789/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1597 :
    ((368794107/50000000 : ℚ) : ℝ) ≤ Real.log (1597 : ℕ)
      ∧ Real.log (1597 : ℕ) ≤ ((147517643/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1598 :
    ((184412703/25000000 : ℚ) : ℝ) ≤ Real.log (1598 : ℕ)
      ∧ Real.log (1598 : ℕ) ≤ ((737650813/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1599 :
    ((737713371/100000000 : ℚ) : ℝ) ≤ Real.log (1599 : ℕ)
      ∧ Real.log (1599 : ℕ) ≤ ((184428343/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1600 :
    ((73777589/10000000 : ℚ) : ℝ) ≤ Real.log (1600 : ℕ)
      ∧ Real.log (1600 : ℕ) ≤ ((737775891/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1601 :
    ((737838371/100000000 : ℚ) : ℝ) ≤ Real.log (1601 : ℕ)
      ∧ Real.log (1601 : ℕ) ≤ ((184459593/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1602 :
    ((184475203/25000000 : ℚ) : ℝ) ≤ Real.log (1602 : ℕ)
      ∧ Real.log (1602 : ℕ) ≤ ((737900813/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1603 :
    ((147592643/20000000 : ℚ) : ℝ) ≤ Real.log (1603 : ℕ)
      ∧ Real.log (1603 : ℕ) ≤ ((46122701/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1604 :
    ((369012789/50000000 : ℚ) : ℝ) ≤ Real.log (1604 : ℕ)
      ∧ Real.log (1604 : ℕ) ≤ ((738025579/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1605 :
    ((738087903/100000000 : ℚ) : ℝ) ≤ Real.log (1605 : ℕ)
      ∧ Real.log (1605 : ℕ) ≤ ((23065247/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1606 :
    ((738150189/100000000 : ℚ) : ℝ) ≤ Real.log (1606 : ℕ)
      ∧ Real.log (1606 : ℕ) ≤ ((73815019/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1607 :
    ((184553109/25000000 : ℚ) : ℝ) ≤ Real.log (1607 : ℕ)
      ∧ Real.log (1607 : ℕ) ≤ ((738212437/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1608 :
    ((184568661/25000000 : ℚ) : ℝ) ≤ Real.log (1608 : ℕ)
      ∧ Real.log (1608 : ℕ) ≤ ((369137323/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1609 :
    ((369168407/50000000 : ℚ) : ℝ) ≤ Real.log (1609 : ℕ)
      ∧ Real.log (1609 : ℕ) ≤ ((147667363/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1610 :
    ((147679789/20000000 : ℚ) : ℝ) ≤ Real.log (1610 : ℕ)
      ∧ Real.log (1610 : ℕ) ≤ ((369199473/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1611 :
    ((369230519/50000000 : ℚ) : ℝ) ≤ Real.log (1611 : ℕ)
      ∧ Real.log (1611 : ℕ) ≤ ((738461039/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1612 :
    ((184630773/25000000 : ℚ) : ℝ) ≤ Real.log (1612 : ℕ)
      ∧ Real.log (1612 : ℕ) ≤ ((738523093/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1613 :
    ((738585107/100000000 : ℚ) : ℝ) ≤ Real.log (1613 : ℕ)
      ∧ Real.log (1613 : ℕ) ≤ ((184646277/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1614 :
    ((184661771/25000000 : ℚ) : ℝ) ≤ Real.log (1614 : ℕ)
      ∧ Real.log (1614 : ℕ) ≤ ((369323543/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1615 :
    ((738709023/100000000 : ℚ) : ℝ) ≤ Real.log (1615 : ℕ)
      ∧ Real.log (1615 : ℕ) ≤ ((23084657/3125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1616 :
    ((738770923/100000000 : ℚ) : ℝ) ≤ Real.log (1616 : ℕ)
      ∧ Real.log (1616 : ℕ) ≤ ((29550837/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1617 :
    ((147766557/20000000 : ℚ) : ℝ) ≤ Real.log (1617 : ℕ)
      ∧ Real.log (1617 : ℕ) ≤ ((738832787/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1618 :
    ((738894609/100000000 : ℚ) : ℝ) ≤ Real.log (1618 : ℕ)
      ∧ Real.log (1618 : ℕ) ≤ ((73889461/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1619 :
    ((147791279/20000000 : ℚ) : ℝ) ≤ Real.log (1619 : ℕ)
      ∧ Real.log (1619 : ℕ) ≤ ((184739099/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1620 :
    ((369509071/50000000 : ℚ) : ℝ) ≤ Real.log (1620 : ℕ)
      ∧ Real.log (1620 : ℕ) ≤ ((739018143/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1621 :
    ((184769963/25000000 : ℚ) : ℝ) ≤ Real.log (1621 : ℕ)
      ∧ Real.log (1621 : ℕ) ≤ ((739079853/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1622 :
    ((739141523/100000000 : ℚ) : ℝ) ≤ Real.log (1622 : ℕ)
      ∧ Real.log (1622 : ℕ) ≤ ((184785381/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1623 :
    ((184800789/25000000 : ℚ) : ℝ) ≤ Real.log (1623 : ℕ)
      ∧ Real.log (1623 : ℕ) ≤ ((739203157/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1624 :
    ((46204047/6250000 : ℚ) : ℝ) ≤ Real.log (1624 : ℕ)
      ∧ Real.log (1624 : ℕ) ≤ ((739264753/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1625 :
    ((739326309/100000000 : ℚ) : ℝ) ≤ Real.log (1625 : ℕ)
      ∧ Real.log (1625 : ℕ) ≤ ((73932631/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1626 :
    ((184846957/25000000 : ℚ) : ℝ) ≤ Real.log (1626 : ℕ)
      ∧ Real.log (1626 : ℕ) ≤ ((73938783/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1627 :
    ((73944931/10000000 : ℚ) : ℝ) ≤ Real.log (1627 : ℕ)
      ∧ Real.log (1627 : ℕ) ≤ ((739449311/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1628 :
    ((369755377/50000000 : ℚ) : ℝ) ≤ Real.log (1628 : ℕ)
      ∧ Real.log (1628 : ℕ) ≤ ((147902151/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1629 :
    ((2311163/312500 : ℚ) : ℝ) ≤ Real.log (1629 : ℕ)
      ∧ Real.log (1629 : ℕ) ≤ ((739572161/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1630 :
    ((739633529/100000000 : ℚ) : ℝ) ≤ Real.log (1630 : ℕ)
      ∧ Real.log (1630 : ℕ) ≤ ((73963353/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1631 :
    ((36984743/5000000 : ℚ) : ℝ) ≤ Real.log (1631 : ℕ)
      ∧ Real.log (1631 : ℕ) ≤ ((739694861/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1632 :
    ((739756153/100000000 : ℚ) : ℝ) ≤ Real.log (1632 : ℕ)
      ∧ Real.log (1632 : ℕ) ≤ ((369878077/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1633 :
    ((739817409/100000000 : ℚ) : ℝ) ≤ Real.log (1633 : ℕ)
      ∧ Real.log (1633 : ℕ) ≤ ((73981741/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1634 :
    ((739878627/100000000 : ℚ) : ℝ) ≤ Real.log (1634 : ℕ)
      ∧ Real.log (1634 : ℕ) ≤ ((184969657/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1635 :
    ((23123119/3125000 : ℚ) : ℝ) ≤ Real.log (1635 : ℕ)
      ∧ Real.log (1635 : ℕ) ≤ ((739939809/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1636 :
    ((740000951/100000000 : ℚ) : ℝ) ≤ Real.log (1636 : ℕ)
      ∧ Real.log (1636 : ℕ) ≤ ((92500119/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1637 :
    ((740062057/100000000 : ℚ) : ℝ) ≤ Real.log (1637 : ℕ)
      ∧ Real.log (1637 : ℕ) ≤ ((370031029/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1638 :
    ((370061563/50000000 : ℚ) : ℝ) ≤ Real.log (1638 : ℕ)
      ∧ Real.log (1638 : ℕ) ≤ ((740123127/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1639 :
    ((740184157/100000000 : ℚ) : ℝ) ≤ Real.log (1639 : ℕ)
      ∧ Real.log (1639 : ℕ) ≤ ((740184159/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1640 :
    ((23132661/3125000 : ℚ) : ℝ) ≤ Real.log (1640 : ℕ)
      ∧ Real.log (1640 : ℕ) ≤ ((740245153/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1641 :
    ((740306109/100000000 : ℚ) : ℝ) ≤ Real.log (1641 : ℕ)
      ∧ Real.log (1641 : ℕ) ≤ ((74030611/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1642 :
    ((185091757/25000000 : ℚ) : ℝ) ≤ Real.log (1642 : ℕ)
      ∧ Real.log (1642 : ℕ) ≤ ((74036703/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1643 :
    ((740427911/100000000 : ℚ) : ℝ) ≤ Real.log (1643 : ℕ)
      ∧ Real.log (1643 : ℕ) ≤ ((92553489/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1644 :
    ((740488757/100000000 : ℚ) : ℝ) ≤ Real.log (1644 : ℕ)
      ∧ Real.log (1644 : ℕ) ≤ ((370244379/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1645 :
    ((370274783/50000000 : ℚ) : ℝ) ≤ Real.log (1645 : ℕ)
      ∧ Real.log (1645 : ℕ) ≤ ((740549567/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1646 :
    ((370305169/50000000 : ℚ) : ℝ) ≤ Real.log (1646 : ℕ)
      ∧ Real.log (1646 : ℕ) ≤ ((740610339/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1647 :
    ((23145971/3125000 : ℚ) : ℝ) ≤ Real.log (1647 : ℕ)
      ∧ Real.log (1647 : ℕ) ≤ ((370335537/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1648 :
    ((740731771/100000000 : ℚ) : ℝ) ≤ Real.log (1648 : ℕ)
      ∧ Real.log (1648 : ℕ) ≤ ((185182943/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1649 :
    ((46299527/6250000 : ℚ) : ℝ) ≤ Real.log (1649 : ℕ)
      ∧ Real.log (1649 : ℕ) ≤ ((740792433/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1650 :
    ((11575829/1562500 : ℚ) : ℝ) ≤ Real.log (1650 : ℕ)
      ∧ Real.log (1650 : ℕ) ≤ ((740853057/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1651 :
    ((185228411/25000000 : ℚ) : ℝ) ≤ Real.log (1651 : ℕ)
      ∧ Real.log (1651 : ℕ) ≤ ((148182729/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1652 :
    ((148194839/20000000 : ℚ) : ℝ) ≤ Real.log (1652 : ℕ)
      ∧ Real.log (1652 : ℕ) ≤ ((185243549/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1653 :
    ((741034709/100000000 : ℚ) : ℝ) ≤ Real.log (1653 : ℕ)
      ∧ Real.log (1653 : ℕ) ≤ ((74103471/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1654 :
    ((741095187/100000000 : ℚ) : ℝ) ≤ Real.log (1654 : ℕ)
      ∧ Real.log (1654 : ℕ) ≤ ((185273797/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1655 :
    ((185288907/25000000 : ℚ) : ℝ) ≤ Real.log (1655 : ℕ)
      ∧ Real.log (1655 : ℕ) ≤ ((741155629/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1656 :
    ((741216033/100000000 : ℚ) : ℝ) ≤ Real.log (1656 : ℕ)
      ∧ Real.log (1656 : ℕ) ≤ ((370608017/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1657 :
    ((741276401/100000000 : ℚ) : ℝ) ≤ Real.log (1657 : ℕ)
      ∧ Real.log (1657 : ℕ) ≤ ((370638201/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1658 :
    ((741336733/100000000 : ℚ) : ℝ) ≤ Real.log (1658 : ℕ)
      ∧ Real.log (1658 : ℕ) ≤ ((370668367/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1659 :
    ((185349257/25000000 : ℚ) : ℝ) ≤ Real.log (1659 : ℕ)
      ∧ Real.log (1659 : ℕ) ≤ ((74139703/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1660 :
    ((92682161/12500000 : ℚ) : ℝ) ≤ Real.log (1660 : ℕ)
      ∧ Real.log (1660 : ℕ) ≤ ((741457289/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1661 :
    ((74151751/10000000 : ℚ) : ℝ) ≤ Real.log (1661 : ℕ)
      ∧ Real.log (1661 : ℕ) ≤ ((92689689/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1662 :
    ((741577697/100000000 : ℚ) : ℝ) ≤ Real.log (1662 : ℕ)
      ∧ Real.log (1662 : ℕ) ≤ ((370788849/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1663 :
    ((741637847/100000000 : ℚ) : ℝ) ≤ Real.log (1663 : ℕ)
      ∧ Real.log (1663 : ℕ) ≤ ((741637849/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1664 :
    ((370848981/50000000 : ℚ) : ℝ) ≤ Real.log (1664 : ℕ)
      ∧ Real.log (1664 : ℕ) ≤ ((741697963/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1665 :
    ((18543951/2500000 : ℚ) : ℝ) ≤ Real.log (1665 : ℕ)
      ∧ Real.log (1665 : ℕ) ≤ ((741758041/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1666 :
    ((370909041/50000000 : ℚ) : ℝ) ≤ Real.log (1666 : ℕ)
      ∧ Real.log (1666 : ℕ) ≤ ((741818083/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1667 :
    ((92734761/12500000 : ℚ) : ℝ) ≤ Real.log (1667 : ℕ)
      ∧ Real.log (1667 : ℕ) ≤ ((741878089/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1668 :
    ((370969029/50000000 : ℚ) : ℝ) ≤ Real.log (1668 : ℕ)
      ∧ Real.log (1668 : ℕ) ≤ ((741938059/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1669 :
    ((92749749/12500000 : ℚ) : ℝ) ≤ Real.log (1669 : ℕ)
      ∧ Real.log (1669 : ℕ) ≤ ((741997993/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1670 :
    ((74205789/10000000 : ℚ) : ℝ) ≤ Real.log (1670 : ℕ)
      ∧ Real.log (1670 : ℕ) ≤ ((742057891/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1671 :
    ((92764719/12500000 : ℚ) : ℝ) ≤ Real.log (1671 : ℕ)
      ∧ Real.log (1671 : ℕ) ≤ ((371058877/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1672 :
    ((742177579/100000000 : ℚ) : ℝ) ≤ Real.log (1672 : ℕ)
      ∧ Real.log (1672 : ℕ) ≤ ((37108879/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1673 :
    ((74223737/10000000 : ℚ) : ℝ) ≤ Real.log (1673 : ℕ)
      ∧ Real.log (1673 : ℕ) ≤ ((742237371/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1674 :
    ((5938377/800000 : ℚ) : ℝ) ≤ Real.log (1674 : ℕ)
      ∧ Real.log (1674 : ℕ) ≤ ((371148563/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1675 :
    ((185589211/25000000 : ℚ) : ℝ) ≤ Real.log (1675 : ℕ)
      ∧ Real.log (1675 : ℕ) ≤ ((148471369/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1676 :
    ((46401033/6250000 : ℚ) : ℝ) ≤ Real.log (1676 : ℕ)
      ∧ Real.log (1676 : ℕ) ≤ ((742416529/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1677 :
    ((46404761/6250000 : ℚ) : ℝ) ≤ Real.log (1677 : ℕ)
      ∧ Real.log (1677 : ℕ) ≤ ((742476177/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1678 :
    ((185633947/25000000 : ℚ) : ℝ) ≤ Real.log (1678 : ℕ)
      ∧ Real.log (1678 : ℕ) ≤ ((742535789/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1679 :
    ((148519073/20000000 : ℚ) : ℝ) ≤ Real.log (1679 : ℕ)
      ∧ Real.log (1679 : ℕ) ≤ ((371297683/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1680 :
    ((742654907/100000000 : ℚ) : ℝ) ≤ Real.log (1680 : ℕ)
      ∧ Real.log (1680 : ℕ) ≤ ((185663727/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1681 :
    ((742714413/100000000 : ℚ) : ℝ) ≤ Real.log (1681 : ℕ)
      ∧ Real.log (1681 : ℕ) ≤ ((371357207/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1682 :
    ((185693471/25000000 : ℚ) : ℝ) ≤ Real.log (1682 : ℕ)
      ∧ Real.log (1682 : ℕ) ≤ ((148554777/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1683 :
    ((742833319/100000000 : ℚ) : ℝ) ≤ Real.log (1683 : ℕ)
      ∧ Real.log (1683 : ℕ) ≤ ((18570833/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1684 :
    ((742892719/100000000 : ℚ) : ℝ) ≤ Real.log (1684 : ℕ)
      ∧ Real.log (1684 : ℕ) ≤ ((9286159/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1685 :
    ((185738021/25000000 : ℚ) : ℝ) ≤ Real.log (1685 : ℕ)
      ∧ Real.log (1685 : ℕ) ≤ ((148590417/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1686 :
    ((743011413/100000000 : ℚ) : ℝ) ≤ Real.log (1686 : ℕ)
      ∧ Real.log (1686 : ℕ) ≤ ((148602283/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1687 :
    ((185767677/25000000 : ℚ) : ℝ) ≤ Real.log (1687 : ℕ)
      ∧ Real.log (1687 : ℕ) ≤ ((743070709/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1688 :
    ((743129967/100000000 : ℚ) : ℝ) ≤ Real.log (1688 : ℕ)
      ∧ Real.log (1688 : ℕ) ≤ ((46445623/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1689 :
    ((743189191/100000000 : ℚ) : ℝ) ≤ Real.log (1689 : ℕ)
      ∧ Real.log (1689 : ℕ) ≤ ((92898649/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1690 :
    ((37162419/5000000 : ℚ) : ℝ) ≤ Real.log (1690 : ℕ)
      ∧ Real.log (1690 : ℕ) ≤ ((371624191/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1691 :
    ((371653767/50000000 : ℚ) : ℝ) ≤ Real.log (1691 : ℕ)
      ∧ Real.log (1691 : ℕ) ≤ ((46456721/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1692 :
    ((743366653/100000000 : ℚ) : ℝ) ≤ Real.log (1692 : ℕ)
      ∧ Real.log (1692 : ℕ) ≤ ((148673331/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1693 :
    ((371712869/50000000 : ℚ) : ℝ) ≤ Real.log (1693 : ℕ)
      ∧ Real.log (1693 : ℕ) ≤ ((743425739/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1694 :
    ((743484787/100000000 : ℚ) : ℝ) ≤ Real.log (1694 : ℕ)
      ∧ Real.log (1694 : ℕ) ≤ ((185871197/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1695 :
    ((743543801/100000000 : ℚ) : ℝ) ≤ Real.log (1695 : ℕ)
      ∧ Real.log (1695 : ℕ) ≤ ((743543803/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1696 :
    ((743602781/100000000 : ℚ) : ℝ) ≤ Real.log (1696 : ℕ)
      ∧ Real.log (1696 : ℕ) ≤ ((371801391/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1697 :
    ((371830863/50000000 : ℚ) : ℝ) ≤ Real.log (1697 : ℕ)
      ∧ Real.log (1697 : ℕ) ≤ ((743661727/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1698 :
    ((185930159/25000000 : ℚ) : ℝ) ≤ Real.log (1698 : ℕ)
      ∧ Real.log (1698 : ℕ) ≤ ((743720637/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1699 :
    ((92972439/12500000 : ℚ) : ℝ) ≤ Real.log (1699 : ℕ)
      ∧ Real.log (1699 : ℕ) ≤ ((743779513/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1700 :
    ((46489897/6250000 : ℚ) : ℝ) ≤ Real.log (1700 : ℕ)
      ∧ Real.log (1700 : ℕ) ≤ ((371919177/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1701 :
    ((743897159/100000000 : ℚ) : ℝ) ≤ Real.log (1701 : ℕ)
      ∧ Real.log (1701 : ℕ) ≤ ((18597429/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1702 :
    ((74395593/10000000 : ℚ) : ℝ) ≤ Real.log (1702 : ℕ)
      ∧ Real.log (1702 : ℕ) ≤ ((185988983/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1703 :
    ((186003667/25000000 : ℚ) : ℝ) ≤ Real.log (1703 : ℕ)
      ∧ Real.log (1703 : ℕ) ≤ ((744014669/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1704 :
    ((74407337/10000000 : ℚ) : ℝ) ≤ Real.log (1704 : ℕ)
      ∧ Real.log (1704 : ℕ) ≤ ((186018343/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1705 :
    ((372066019/50000000 : ℚ) : ℝ) ≤ Real.log (1705 : ℕ)
      ∧ Real.log (1705 : ℕ) ≤ ((18603301/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1706 :
    ((46511917/6250000 : ℚ) : ℝ) ≤ Real.log (1706 : ℕ)
      ∧ Real.log (1706 : ℕ) ≤ ((372095337/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1707 :
    ((93031159/12500000 : ℚ) : ℝ) ≤ Real.log (1707 : ℕ)
      ∧ Real.log (1707 : ℕ) ≤ ((744249273/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1708 :
    ((744307837/100000000 : ℚ) : ℝ) ≤ Real.log (1708 : ℕ)
      ∧ Real.log (1708 : ℕ) ≤ ((372153919/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1709 :
    ((23261449/3125000 : ℚ) : ℝ) ≤ Real.log (1709 : ℕ)
      ∧ Real.log (1709 : ℕ) ≤ ((744366369/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1710 :
    ((23263277/3125000 : ℚ) : ℝ) ≤ Real.log (1710 : ℕ)
      ∧ Real.log (1710 : ℕ) ≤ ((372212433/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1711 :
    ((744483327/100000000 : ℚ) : ℝ) ≤ Real.log (1711 : ℕ)
      ∧ Real.log (1711 : ℕ) ≤ ((2908138/390625 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1712 :
    ((148908351/20000000 : ℚ) : ℝ) ≤ Real.log (1712 : ℕ)
      ∧ Real.log (1712 : ℕ) ≤ ((186135439/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1713 :
    ((744600149/100000000 : ℚ) : ℝ) ≤ Real.log (1713 : ℕ)
      ∧ Real.log (1713 : ℕ) ≤ ((744600151/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1714 :
    ((744658509/100000000 : ℚ) : ℝ) ≤ Real.log (1714 : ℕ)
      ∧ Real.log (1714 : ℕ) ≤ ((744658511/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1715 :
    ((148943367/20000000 : ℚ) : ℝ) ≤ Real.log (1715 : ℕ)
      ∧ Real.log (1715 : ℕ) ≤ ((744716837/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1716 :
    ((744775127/100000000 : ℚ) : ℝ) ≤ Real.log (1716 : ℕ)
      ∧ Real.log (1716 : ℕ) ≤ ((744775129/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1717 :
    ((372416693/50000000 : ℚ) : ℝ) ≤ Real.log (1717 : ℕ)
      ∧ Real.log (1717 : ℕ) ≤ ((744833387/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1718 :
    ((74489161/10000000 : ℚ) : ℝ) ≤ Real.log (1718 : ℕ)
      ∧ Real.log (1718 : ℕ) ≤ ((744891611/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1719 :
    ((3724749/500000 : ℚ) : ℝ) ≤ Real.log (1719 : ℕ)
      ∧ Real.log (1719 : ℕ) ≤ ((744949801/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1720 :
    ((186251989/25000000 : ℚ) : ℝ) ≤ Real.log (1720 : ℕ)
      ∧ Real.log (1720 : ℕ) ≤ ((372503979/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1721 :
    ((745066079/100000000 : ℚ) : ℝ) ≤ Real.log (1721 : ℕ)
      ∧ Real.log (1721 : ℕ) ≤ ((4656663/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1722 :
    ((93140521/12500000 : ℚ) : ℝ) ≤ Real.log (1722 : ℕ)
      ∧ Real.log (1722 : ℕ) ≤ ((745124169/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1723 :
    ((745182223/100000000 : ℚ) : ℝ) ≤ Real.log (1723 : ℕ)
      ∧ Real.log (1723 : ℕ) ≤ ((46573889/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1724 :
    ((149048049/20000000 : ℚ) : ℝ) ≤ Real.log (1724 : ℕ)
      ∧ Real.log (1724 : ℕ) ≤ ((372620123/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1725 :
    ((93162279/12500000 : ℚ) : ℝ) ≤ Real.log (1725 : ℕ)
      ∧ Real.log (1725 : ℕ) ≤ ((372649117/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1726 :
    ((745356187/100000000 : ℚ) : ℝ) ≤ Real.log (1726 : ℕ)
      ∧ Real.log (1726 : ℕ) ≤ ((186339047/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1727 :
    ((745414107/100000000 : ℚ) : ℝ) ≤ Real.log (1727 : ℕ)
      ∧ Real.log (1727 : ℕ) ≤ ((745414109/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1728 :
    ((372735997/50000000 : ℚ) : ℝ) ≤ Real.log (1728 : ℕ)
      ∧ Real.log (1728 : ℕ) ≤ ((186367999/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1729 :
    ((93191231/12500000 : ℚ) : ℝ) ≤ Real.log (1729 : ℕ)
      ∧ Real.log (1729 : ℕ) ≤ ((745529849/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1730 :
    ((186396917/25000000 : ℚ) : ℝ) ≤ Real.log (1730 : ℕ)
      ∧ Real.log (1730 : ℕ) ≤ ((74558767/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1731 :
    ((149129091/20000000 : ℚ) : ℝ) ≤ Real.log (1731 : ℕ)
      ∧ Real.log (1731 : ℕ) ≤ ((46602841/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1732 :
    ((93212901/12500000 : ℚ) : ℝ) ≤ Real.log (1732 : ℕ)
      ∧ Real.log (1732 : ℕ) ≤ ((74570321/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1733 :
    ((23305029/3125000 : ℚ) : ℝ) ≤ Real.log (1733 : ℕ)
      ∧ Real.log (1733 : ℕ) ≤ ((74576093/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1734 :
    ((149163723/20000000 : ℚ) : ℝ) ≤ Real.log (1734 : ℕ)
      ∧ Real.log (1734 : ℕ) ≤ ((745818617/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1735 :
    ((745876269/100000000 : ℚ) : ℝ) ≤ Real.log (1735 : ℕ)
      ∧ Real.log (1735 : ℕ) ≤ ((74587627/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1736 :
    ((745933889/100000000 : ℚ) : ℝ) ≤ Real.log (1736 : ℕ)
      ∧ Real.log (1736 : ℕ) ≤ ((74593389/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1737 :
    ((186497869/25000000 : ℚ) : ℝ) ≤ Real.log (1737 : ℕ)
      ∧ Real.log (1737 : ℕ) ≤ ((372995739/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1738 :
    ((74604903/10000000 : ℚ) : ℝ) ≤ Real.log (1738 : ℕ)
      ∧ Real.log (1738 : ℕ) ≤ ((746049031/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1739 :
    ((746106551/100000000 : ℚ) : ℝ) ≤ Real.log (1739 : ℕ)
      ∧ Real.log (1739 : ℕ) ≤ ((93263319/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1740 :
    ((746164039/100000000 : ℚ) : ℝ) ≤ Real.log (1740 : ℕ)
      ∧ Real.log (1740 : ℕ) ≤ ((18654101/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1741 :
    ((746221493/100000000 : ℚ) : ℝ) ≤ Real.log (1741 : ℕ)
      ∧ Real.log (1741 : ℕ) ≤ ((149244299/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1742 :
    ((149255783/20000000 : ℚ) : ℝ) ≤ Real.log (1742 : ℕ)
      ∧ Real.log (1742 : ℕ) ≤ ((746278917/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1743 :
    ((46646019/6250000 : ℚ) : ℝ) ≤ Real.log (1743 : ℕ)
      ∧ Real.log (1743 : ℕ) ≤ ((149267261/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1744 :
    ((37319683/5000000 : ℚ) : ℝ) ≤ Real.log (1744 : ℕ)
      ∧ Real.log (1744 : ℕ) ≤ ((746393661/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1745 :
    ((746450983/100000000 : ℚ) : ℝ) ≤ Real.log (1745 : ℕ)
      ∧ Real.log (1745 : ℕ) ≤ ((93306373/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1746 :
    ((746508273/100000000 : ℚ) : ℝ) ≤ Real.log (1746 : ℕ)
      ∧ Real.log (1746 : ℕ) ≤ ((29860331/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1747 :
    ((74656553/10000000 : ℚ) : ℝ) ≤ Real.log (1747 : ℕ)
      ∧ Real.log (1747 : ℕ) ≤ ((186641383/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1748 :
    ((149324551/20000000 : ℚ) : ℝ) ≤ Real.log (1748 : ℕ)
      ∧ Real.log (1748 : ℕ) ≤ ((746622757/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1749 :
    ((746679947/100000000 : ℚ) : ℝ) ≤ Real.log (1749 : ℕ)
      ∧ Real.log (1749 : ℕ) ≤ ((186669987/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1750 :
    ((373368553/50000000 : ℚ) : ℝ) ≤ Real.log (1750 : ℕ)
      ∧ Real.log (1750 : ℕ) ≤ ((186684277/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1751 :
    ((746794233/100000000 : ℚ) : ℝ) ≤ Real.log (1751 : ℕ)
      ∧ Real.log (1751 : ℕ) ≤ ((373397117/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1752 :
    ((746851327/100000000 : ℚ) : ℝ) ≤ Real.log (1752 : ℕ)
      ∧ Real.log (1752 : ℕ) ≤ ((2917388/390625 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1753 :
    ((186727097/25000000 : ℚ) : ℝ) ≤ Real.log (1753 : ℕ)
      ∧ Real.log (1753 : ℕ) ≤ ((746908389/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1754 :
    ((746965417/100000000 : ℚ) : ℝ) ≤ Real.log (1754 : ℕ)
      ∧ Real.log (1754 : ℕ) ≤ ((373482709/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1755 :
    ((747022413/100000000 : ℚ) : ℝ) ≤ Real.log (1755 : ℕ)
      ∧ Real.log (1755 : ℕ) ≤ ((149404483/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1756 :
    ((747079377/100000000 : ℚ) : ℝ) ≤ Real.log (1756 : ℕ)
      ∧ Real.log (1756 : ℕ) ≤ ((373539689/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1757 :
    ((186784077/25000000 : ℚ) : ℝ) ≤ Real.log (1757 : ℕ)
      ∧ Real.log (1757 : ℕ) ≤ ((74713631/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1758 :
    ((747193207/100000000 : ℚ) : ℝ) ≤ Real.log (1758 : ℕ)
      ∧ Real.log (1758 : ℕ) ≤ ((747193209/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1759 :
    ((373625037/50000000 : ℚ) : ℝ) ≤ Real.log (1759 : ℕ)
      ∧ Real.log (1759 : ℕ) ≤ ((29890003/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1760 :
    ((186826727/25000000 : ℚ) : ℝ) ≤ Real.log (1760 : ℕ)
      ∧ Real.log (1760 : ℕ) ≤ ((74730691/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1761 :
    ((74736371/10000000 : ℚ) : ℝ) ≤ Real.log (1761 : ℕ)
      ∧ Real.log (1761 : ℕ) ≤ ((5838779/781250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1762 :
    ((2335689/312500 : ℚ) : ℝ) ≤ Real.log (1762 : ℕ)
      ∧ Real.log (1762 : ℕ) ≤ ((373710241/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1763 :
    ((373738609/50000000 : ℚ) : ℝ) ≤ Real.log (1763 : ℕ)
      ∧ Real.log (1763 : ℕ) ≤ ((747477219/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1764 :
    ((747533923/100000000 : ℚ) : ℝ) ≤ Real.log (1764 : ℕ)
      ∧ Real.log (1764 : ℕ) ≤ ((29901357/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1765 :
    ((186897649/25000000 : ℚ) : ℝ) ≤ Real.log (1765 : ℕ)
      ∧ Real.log (1765 : ℕ) ≤ ((373795299/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1766 :
    ((373823619/50000000 : ℚ) : ℝ) ≤ Real.log (1766 : ℕ)
      ∧ Real.log (1766 : ℕ) ≤ ((747647239/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1767 :
    ((747703847/100000000 : ℚ) : ℝ) ≤ Real.log (1767 : ℕ)
      ∧ Real.log (1767 : ℕ) ≤ ((93462981/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1768 :
    ((93470053/12500000 : ℚ) : ℝ) ≤ Real.log (1768 : ℕ)
      ∧ Real.log (1768 : ℕ) ≤ ((29910417/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1769 :
    ((747816969/100000000 : ℚ) : ℝ) ≤ Real.log (1769 : ℕ)
      ∧ Real.log (1769 : ℕ) ≤ ((74781697/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1770 :
    ((373936741/50000000 : ℚ) : ℝ) ≤ Real.log (1770 : ℕ)
      ∧ Real.log (1770 : ℕ) ≤ ((186968371/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1771 :
    ((747929963/100000000 : ℚ) : ℝ) ≤ Real.log (1771 : ℕ)
      ∧ Real.log (1771 : ℕ) ≤ ((149585993/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1772 :
    ((747986413/100000000 : ℚ) : ℝ) ≤ Real.log (1772 : ℕ)
      ∧ Real.log (1772 : ℕ) ≤ ((373993207/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1773 :
    ((74804283/10000000 : ℚ) : ℝ) ≤ Real.log (1773 : ℕ)
      ∧ Real.log (1773 : ℕ) ≤ ((46752677/6250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1774 :
    ((46756201/6250000 : ℚ) : ℝ) ≤ Real.log (1774 : ℕ)
      ∧ Real.log (1774 : ℕ) ≤ ((748099217/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1775 :
    ((74815557/10000000 : ℚ) : ℝ) ≤ Real.log (1775 : ℕ)
      ∧ Real.log (1775 : ℕ) ≤ ((748155571/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1776 :
    ((187052973/25000000 : ℚ) : ℝ) ≤ Real.log (1776 : ℕ)
      ∧ Real.log (1776 : ℕ) ≤ ((748211893/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1777 :
    ((374134091/50000000 : ℚ) : ℝ) ≤ Real.log (1777 : ℕ)
      ∧ Real.log (1777 : ℕ) ≤ ((93533523/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1778 :
    ((748324441/100000000 : ℚ) : ℝ) ≤ Real.log (1778 : ℕ)
      ∧ Real.log (1778 : ℕ) ≤ ((748324443/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1779 :
    ((187095167/25000000 : ℚ) : ℝ) ≤ Real.log (1779 : ℕ)
      ∧ Real.log (1779 : ℕ) ≤ ((74838067/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1780 :
    ((5847163/781250 : ℚ) : ℝ) ≤ Real.log (1780 : ℕ)
      ∧ Real.log (1780 : ℕ) ≤ ((149687373/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1781 :
    ((187123257/25000000 : ℚ) : ℝ) ≤ Real.log (1781 : ℕ)
      ∧ Real.log (1781 : ℕ) ≤ ((748493029/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1782 :
    ((18713729/2500000 : ℚ) : ℝ) ≤ Real.log (1782 : ℕ)
      ∧ Real.log (1782 : ℕ) ≤ ((374274581/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1783 :
    ((748605261/100000000 : ℚ) : ℝ) ≤ Real.log (1783 : ℕ)
      ∧ Real.log (1783 : ℕ) ≤ ((748605263/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1784 :
    ((748661331/100000000 : ℚ) : ℝ) ≤ Real.log (1784 : ℕ)
      ∧ Real.log (1784 : ℕ) ≤ ((187165333/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1785 :
    ((748717369/100000000 : ℚ) : ℝ) ≤ Real.log (1785 : ℕ)
      ∧ Real.log (1785 : ℕ) ≤ ((748717371/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1786 :
    ((2924896/390625 : ℚ) : ℝ) ≤ Real.log (1786 : ℕ)
      ∧ Real.log (1786 : ℕ) ≤ ((748773377/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1787 :
    ((748829351/100000000 : ℚ) : ℝ) ≤ Real.log (1787 : ℕ)
      ∧ Real.log (1787 : ℕ) ≤ ((748829353/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1788 :
    ((149777059/20000000 : ℚ) : ℝ) ≤ Real.log (1788 : ℕ)
      ∧ Real.log (1788 : ℕ) ≤ ((748885297/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1789 :
    ((93617651/12500000 : ℚ) : ℝ) ≤ Real.log (1789 : ℕ)
      ∧ Real.log (1789 : ℕ) ≤ ((748941209/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1790 :
    ((748997089/100000000 : ℚ) : ℝ) ≤ Real.log (1790 : ℕ)
      ∧ Real.log (1790 : ℕ) ≤ ((748997091/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1791 :
    ((37452647/5000000 : ℚ) : ℝ) ≤ Real.log (1791 : ℕ)
      ∧ Real.log (1791 : ℕ) ≤ ((749052941/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1792 :
    ((749108759/100000000 : ℚ) : ℝ) ≤ Real.log (1792 : ℕ)
      ∧ Real.log (1792 : ℕ) ≤ ((749108761/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1793 :
    ((749164547/100000000 : ℚ) : ℝ) ≤ Real.log (1793 : ℕ)
      ∧ Real.log (1793 : ℕ) ≤ ((749164549/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1794 :
    ((46826269/6250000 : ℚ) : ℝ) ≤ Real.log (1794 : ℕ)
      ∧ Real.log (1794 : ℕ) ≤ ((149844061/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1795 :
    ((74927603/10000000 : ℚ) : ℝ) ≤ Real.log (1795 : ℕ)
      ∧ Real.log (1795 : ℕ) ≤ ((749276031/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1796 :
    ((187332931/25000000 : ℚ) : ℝ) ≤ Real.log (1796 : ℕ)
      ∧ Real.log (1796 : ℕ) ≤ ((374665863/50000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1797 :
    ((187346847/25000000 : ℚ) : ℝ) ≤ Real.log (1797 : ℕ)
      ∧ Real.log (1797 : ℕ) ≤ ((74938739/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1798 :
    ((749443021/100000000 : ℚ) : ℝ) ≤ Real.log (1798 : ℕ)
      ∧ Real.log (1798 : ℕ) ≤ ((749443023/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1799 :
    ((749498623/100000000 : ℚ) : ℝ) ≤ Real.log (1799 : ℕ)
      ∧ Real.log (1799 : ℕ) ≤ ((5995989/800000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1800 :
    ((374777097/50000000 : ℚ) : ℝ) ≤ Real.log (1800 : ℕ)
      ∧ Real.log (1800 : ℕ) ≤ ((187388549/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1801 :
    ((374804867/50000000 : ℚ) : ℝ) ≤ Real.log (1801 : ℕ)
      ∧ Real.log (1801 : ℕ) ≤ ((93701217/12500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1802 :
    ((749665243/100000000 : ℚ) : ℝ) ≤ Real.log (1802 : ℕ)
      ∧ Real.log (1802 : ℕ) ≤ ((149933049/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1803 :
    ((374860361/50000000 : ℚ) : ℝ) ≤ Real.log (1803 : ℕ)
      ∧ Real.log (1803 : ℕ) ≤ ((187430181/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1804 :
    ((74977617/10000000 : ℚ) : ℝ) ≤ Real.log (1804 : ℕ)
      ∧ Real.log (1804 : ℕ) ≤ ((749776171/100000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1805 :
    ((749831587/100000000 : ℚ) : ℝ) ≤ Real.log (1805 : ℕ)
      ∧ Real.log (1805 : ℕ) ≤ ((187457897/25000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1806 :
    ((749886973/100000000 : ℚ) : ℝ) ≤ Real.log (1806 : ℕ)
      ∧ Real.log (1806 : ℕ) ≤ ((29995479/4000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1807 :
    ((749942329/100000000 : ℚ) : ℝ) ≤ Real.log (1807 : ℕ)
      ∧ Real.log (1807 : ℕ) ≤ ((74994233/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1808 :
    ((374998827/50000000 : ℚ) : ℝ) ≤ Real.log (1808 : ℕ)
      ∧ Real.log (1808 : ℕ) ≤ ((149999531/20000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1809 :
    ((375026473/50000000 : ℚ) : ℝ) ≤ Real.log (1809 : ℕ)
      ∧ Real.log (1809 : ℕ) ≤ ((750052949/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1810 :
    ((75010821/10000000 : ℚ) : ℝ) ≤ Real.log (1810 : ℕ)
      ∧ Real.log (1810 : ℕ) ≤ ((750108213/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1811 :
    ((750163443/100000000 : ℚ) : ℝ) ≤ Real.log (1811 : ℕ)
      ∧ Real.log (1811 : ℕ) ≤ ((375081723/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1812 :
    ((375109323/50000000 : ℚ) : ℝ) ≤ Real.log (1812 : ℕ)
      ∧ Real.log (1812 : ℕ) ≤ ((750218649/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1813 :
    ((750273819/100000000 : ℚ) : ℝ) ≤ Real.log (1813 : ℕ)
      ∧ Real.log (1813 : ℕ) ≤ ((375136911/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1814 :
    ((750328961/100000000 : ℚ) : ℝ) ≤ Real.log (1814 : ℕ)
      ∧ Real.log (1814 : ℕ) ≤ ((187582241/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1815 :
    ((93798009/12500000 : ℚ) : ℝ) ≤ Real.log (1815 : ℕ)
      ∧ Real.log (1815 : ℕ) ≤ ((30015363/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1816 :
    ((375219577/50000000 : ℚ) : ℝ) ≤ Real.log (1816 : ℕ)
      ∧ Real.log (1816 : ℕ) ≤ ((750439157/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1817 :
    ((150098841/20000000 : ℚ) : ℝ) ≤ Real.log (1817 : ℕ)
      ∧ Real.log (1817 : ℕ) ≤ ((2931618/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1818 :
    ((30021969/4000000 : ℚ) : ℝ) ≤ Real.log (1818 : ℕ)
      ∧ Real.log (1818 : ℕ) ≤ ((187637307/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1819 :
    ((93825527/12500000 : ℚ) : ℝ) ≤ Real.log (1819 : ℕ)
      ∧ Real.log (1819 : ℕ) ≤ ((750604219/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1820 :
    ((93832397/12500000 : ℚ) : ℝ) ≤ Real.log (1820 : ℕ)
      ∧ Real.log (1820 : ℕ) ≤ ((750659179/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1821 :
    ((375357053/50000000 : ℚ) : ℝ) ≤ Real.log (1821 : ℕ)
      ∧ Real.log (1821 : ℕ) ≤ ((750714109/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1822 :
    ((375384503/50000000 : ℚ) : ℝ) ≤ Real.log (1822 : ℕ)
      ∧ Real.log (1822 : ℕ) ≤ ((46923063/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1823 :
    ((6006591/800000 : ℚ) : ℝ) ≤ Real.log (1823 : ℕ)
      ∧ Real.log (1823 : ℕ) ≤ ((375411939/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1824 :
    ((150175743/20000000 : ℚ) : ℝ) ≤ Real.log (1824 : ℕ)
      ∧ Real.log (1824 : ℕ) ≤ ((375439359/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1825 :
    ((30037341/4000000 : ℚ) : ℝ) ≤ Real.log (1825 : ℕ)
      ∧ Real.log (1825 : ℕ) ≤ ((750933527/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1826 :
    ((46936769/6250000 : ℚ) : ℝ) ≤ Real.log (1826 : ℕ)
      ∧ Real.log (1826 : ℕ) ≤ ((750988307/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1827 :
    ((375521527/50000000 : ℚ) : ℝ) ≤ Real.log (1827 : ℕ)
      ∧ Real.log (1827 : ℕ) ≤ ((46940191/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1828 :
    ((751097773/100000000 : ℚ) : ℝ) ≤ Real.log (1828 : ℕ)
      ∧ Real.log (1828 : ℕ) ≤ ((46943611/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1829 :
    ((751152463/100000000 : ℚ) : ℝ) ≤ Real.log (1829 : ℕ)
      ∧ Real.log (1829 : ℕ) ≤ ((150230493/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1830 :
    ((751207123/100000000 : ℚ) : ℝ) ≤ Real.log (1830 : ℕ)
      ∧ Real.log (1830 : ℕ) ≤ ((6009657/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1831 :
    ((93907719/12500000 : ℚ) : ℝ) ≤ Real.log (1831 : ℕ)
      ∧ Real.log (1831 : ℕ) ≤ ((150252351/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1832 :
    ((751316353/100000000 : ℚ) : ℝ) ≤ Real.log (1832 : ℕ)
      ∧ Real.log (1832 : ℕ) ≤ ((150263271/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1833 :
    ((751370923/100000000 : ℚ) : ℝ) ≤ Real.log (1833 : ℕ)
      ∧ Real.log (1833 : ℕ) ≤ ((30054837/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1834 :
    ((751425463/100000000 : ℚ) : ℝ) ≤ Real.log (1834 : ℕ)
      ∧ Real.log (1834 : ℕ) ≤ ((375712733/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1835 :
    ((375739987/50000000 : ℚ) : ℝ) ≤ Real.log (1835 : ℕ)
      ∧ Real.log (1835 : ℕ) ≤ ((751479977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1836 :
    ((150306891/20000000 : ℚ) : ℝ) ≤ Real.log (1836 : ℕ)
      ∧ Real.log (1836 : ℕ) ≤ ((375767229/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1837 :
    ((751588907/100000000 : ℚ) : ℝ) ≤ Real.log (1837 : ℕ)
      ∧ Real.log (1837 : ℕ) ≤ ((751588909/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1838 :
    ((11744427/1562500 : ℚ) : ℝ) ≤ Real.log (1838 : ℕ)
      ∧ Real.log (1838 : ℕ) ≤ ((751643331/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1839 :
    ((751697721/100000000 : ℚ) : ℝ) ≤ Real.log (1839 : ℕ)
      ∧ Real.log (1839 : ℕ) ≤ ((751697723/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1840 :
    ((751752083/100000000 : ℚ) : ℝ) ≤ Real.log (1840 : ℕ)
      ∧ Real.log (1840 : ℕ) ≤ ((375876043/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1841 :
    ((46987901/6250000 : ℚ) : ℝ) ≤ Real.log (1841 : ℕ)
      ∧ Real.log (1841 : ℕ) ≤ ((751806419/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1842 :
    ((9398259/1250000 : ℚ) : ℝ) ≤ Real.log (1842 : ℕ)
      ∧ Real.log (1842 : ℕ) ≤ ((375930361/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1843 :
    ((375957497/50000000 : ℚ) : ℝ) ≤ Real.log (1843 : ℕ)
      ∧ Real.log (1843 : ℕ) ≤ ((187978749/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1844 :
    ((751969239/100000000 : ℚ) : ℝ) ≤ Real.log (1844 : ℕ)
      ∧ Real.log (1844 : ℕ) ≤ ((751969241/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1845 :
    ((376011727/50000000 : ℚ) : ℝ) ≤ Real.log (1845 : ℕ)
      ∧ Real.log (1845 : ℕ) ≤ ((23500733/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1846 :
    ((18801941/2500000 : ℚ) : ℝ) ≤ Real.log (1846 : ℕ)
      ∧ Real.log (1846 : ℕ) ≤ ((376038821/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1847 :
    ((188032949/25000000 : ℚ) : ℝ) ≤ Real.log (1847 : ℕ)
      ∧ Real.log (1847 : ℕ) ≤ ((752131799/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1848 :
    ((752185923/100000000 : ℚ) : ℝ) ≤ Real.log (1848 : ℕ)
      ∧ Real.log (1848 : ℕ) ≤ ((376092963/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1849 :
    ((752240021/100000000 : ℚ) : ℝ) ≤ Real.log (1849 : ℕ)
      ∧ Real.log (1849 : ℕ) ≤ ((94030003/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1850 :
    ((75229409/10000000 : ℚ) : ℝ) ≤ Real.log (1850 : ℕ)
      ∧ Real.log (1850 : ℕ) ≤ ((188073523/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1851 :
    ((75234813/10000000 : ℚ) : ℝ) ≤ Real.log (1851 : ℕ)
      ∧ Real.log (1851 : ℕ) ≤ ((188087033/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1852 :
    ((37620107/5000000 : ℚ) : ℝ) ≤ Real.log (1852 : ℕ)
      ∧ Real.log (1852 : ℕ) ≤ ((376201071/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1853 :
    ((752456121/100000000 : ℚ) : ℝ) ≤ Real.log (1853 : ℕ)
      ∧ Real.log (1853 : ℕ) ≤ ((752456123/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1854 :
    ((752510073/100000000 : ℚ) : ℝ) ≤ Real.log (1854 : ℕ)
      ∧ Real.log (1854 : ℕ) ≤ ((30100403/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1855 :
    ((188140999/25000000 : ℚ) : ℝ) ≤ Real.log (1855 : ℕ)
      ∧ Real.log (1855 : ℕ) ≤ ((376281999/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1856 :
    ((75261789/10000000 : ℚ) : ℝ) ≤ Real.log (1856 : ℕ)
      ∧ Real.log (1856 : ℕ) ≤ ((188154473/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1857 :
    ((150534351/20000000 : ℚ) : ℝ) ≤ Real.log (1857 : ℕ)
      ∧ Real.log (1857 : ℕ) ≤ ((752671757/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1858 :
    ((75272559/10000000 : ℚ) : ℝ) ≤ Real.log (1858 : ℕ)
      ∧ Real.log (1858 : ℕ) ≤ ((752725593/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1859 :
    ((752779397/100000000 : ℚ) : ℝ) ≤ Real.log (1859 : ℕ)
      ∧ Real.log (1859 : ℕ) ≤ ((752779399/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1860 :
    ((30113327/4000000 : ℚ) : ℝ) ≤ Real.log (1860 : ℕ)
      ∧ Real.log (1860 : ℕ) ≤ ((752833177/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1861 :
    ((188221731/25000000 : ℚ) : ℝ) ≤ Real.log (1861 : ℕ)
      ∧ Real.log (1861 : ℕ) ≤ ((376443463/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1862 :
    ((188235161/25000000 : ℚ) : ℝ) ≤ Real.log (1862 : ℕ)
      ∧ Real.log (1862 : ℕ) ≤ ((376470323/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1863 :
    ((150598867/20000000 : ℚ) : ℝ) ≤ Real.log (1863 : ℕ)
      ∧ Real.log (1863 : ℕ) ≤ ((376497169/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1864 :
    ((376523999/50000000 : ℚ) : ℝ) ≤ Real.log (1864 : ℕ)
      ∧ Real.log (1864 : ℕ) ≤ ((94131/12500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1865 :
    ((11767213/1562500 : ℚ) : ℝ) ≤ Real.log (1865 : ℕ)
      ∧ Real.log (1865 : ℕ) ≤ ((376550817/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1866 :
    ((753155237/100000000 : ℚ) : ℝ) ≤ Real.log (1866 : ℕ)
      ∧ Real.log (1866 : ℕ) ≤ ((753155239/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1867 :
    ((753208813/100000000 : ℚ) : ℝ) ≤ Real.log (1867 : ℕ)
      ∧ Real.log (1867 : ℕ) ≤ ((150641763/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1868 :
    ((18831559/2500000 : ℚ) : ℝ) ≤ Real.log (1868 : ℕ)
      ∧ Real.log (1868 : ℕ) ≤ ((376631181/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1869 :
    ((753315879/100000000 : ℚ) : ℝ) ≤ Real.log (1869 : ℕ)
      ∧ Real.log (1869 : ℕ) ≤ ((753315881/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1870 :
    ((753369369/100000000 : ℚ) : ℝ) ≤ Real.log (1870 : ℕ)
      ∧ Real.log (1870 : ℕ) ≤ ((188342343/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1871 :
    ((753422831/100000000 : ℚ) : ℝ) ≤ Real.log (1871 : ℕ)
      ∧ Real.log (1871 : ℕ) ≤ ((753422833/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1872 :
    ((94184533/12500000 : ℚ) : ℝ) ≤ Real.log (1872 : ℕ)
      ∧ Real.log (1872 : ℕ) ≤ ((376738133/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1873 :
    ((753529669/100000000 : ℚ) : ℝ) ≤ Real.log (1873 : ℕ)
      ∧ Real.log (1873 : ℕ) ≤ ((753529671/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1874 :
    ((150716609/20000000 : ℚ) : ℝ) ≤ Real.log (1874 : ℕ)
      ∧ Real.log (1874 : ℕ) ≤ ((753583047/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1875 :
    ((94204549/12500000 : ℚ) : ℝ) ≤ Real.log (1875 : ℕ)
      ∧ Real.log (1875 : ℕ) ≤ ((376818197/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1876 :
    ((47105607/6250000 : ℚ) : ℝ) ≤ Real.log (1876 : ℕ)
      ∧ Real.log (1876 : ℕ) ≤ ((376844857/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1877 :
    ((376871501/50000000 : ℚ) : ℝ) ≤ Real.log (1877 : ℕ)
      ∧ Real.log (1877 : ℕ) ≤ ((188435751/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1878 :
    ((150759253/20000000 : ℚ) : ℝ) ≤ Real.log (1878 : ℕ)
      ∧ Real.log (1878 : ℕ) ≤ ((753796267/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1879 :
    ((753849499/100000000 : ℚ) : ℝ) ≤ Real.log (1879 : ℕ)
      ∧ Real.log (1879 : ℕ) ≤ ((753849501/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1880 :
    ((47118919/6250000 : ℚ) : ℝ) ≤ Real.log (1880 : ℕ)
      ∧ Real.log (1880 : ℕ) ≤ ((376951353/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1881 :
    ((376977941/50000000 : ℚ) : ℝ) ≤ Real.log (1881 : ℕ)
      ∧ Real.log (1881 : ℕ) ≤ ((188488971/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1882 :
    ((754009031/100000000 : ℚ) : ℝ) ≤ Real.log (1882 : ℕ)
      ∧ Real.log (1882 : ℕ) ≤ ((754009033/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1883 :
    ((94257769/12500000 : ℚ) : ℝ) ≤ Real.log (1883 : ℕ)
      ∧ Real.log (1883 : ℕ) ≤ ((754062153/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1884 :
    ((188528811/25000000 : ℚ) : ℝ) ≤ Real.log (1884 : ℕ)
      ∧ Real.log (1884 : ℕ) ≤ ((377057623/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1885 :
    ((754168309/100000000 : ℚ) : ℝ) ≤ Real.log (1885 : ℕ)
      ∧ Real.log (1885 : ℕ) ≤ ((754168311/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1886 :
    ((150844269/20000000 : ℚ) : ℝ) ≤ Real.log (1886 : ℕ)
      ∧ Real.log (1886 : ℕ) ≤ ((754221347/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1887 :
    ((754274353/100000000 : ℚ) : ℝ) ≤ Real.log (1887 : ℕ)
      ∧ Real.log (1887 : ℕ) ≤ ((150854871/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1888 :
    ((754327333/100000000 : ℚ) : ℝ) ≤ Real.log (1888 : ℕ)
      ∧ Real.log (1888 : ℕ) ≤ ((150865467/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1889 :
    ((150876057/20000000 : ℚ) : ℝ) ≤ Real.log (1889 : ℕ)
      ∧ Real.log (1889 : ℕ) ≤ ((754380287/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1890 :
    ((75443321/10000000 : ℚ) : ℝ) ≤ Real.log (1890 : ℕ)
      ∧ Real.log (1890 : ℕ) ≤ ((754433211/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1891 :
    ((377243053/50000000 : ℚ) : ℝ) ≤ Real.log (1891 : ℕ)
      ∧ Real.log (1891 : ℕ) ≤ ((754486107/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1892 :
    ((377269487/50000000 : ℚ) : ℝ) ≤ Real.log (1892 : ℕ)
      ∧ Real.log (1892 : ℕ) ≤ ((23579343/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1893 :
    ((377295907/50000000 : ℚ) : ℝ) ≤ Real.log (1893 : ℕ)
      ∧ Real.log (1893 : ℕ) ≤ ((94323977/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1894 :
    ((377322313/50000000 : ℚ) : ℝ) ≤ Real.log (1894 : ℕ)
      ∧ Real.log (1894 : ℕ) ≤ ((188661157/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1895 :
    ((75469741/10000000 : ℚ) : ℝ) ≤ Real.log (1895 : ℕ)
      ∧ Real.log (1895 : ℕ) ≤ ((188674353/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1896 :
    ((754750167/100000000 : ℚ) : ℝ) ≤ Real.log (1896 : ℕ)
      ∧ Real.log (1896 : ℕ) ≤ ((754750169/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1897 :
    ((47175181/6250000 : ℚ) : ℝ) ≤ Real.log (1897 : ℕ)
      ∧ Real.log (1897 : ℕ) ≤ ((377401449/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1898 :
    ((754855597/100000000 : ℚ) : ℝ) ≤ Real.log (1898 : ℕ)
      ∧ Real.log (1898 : ℕ) ≤ ((754855599/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1899 :
    ((75490827/10000000 : ℚ) : ℝ) ≤ Real.log (1899 : ℕ)
      ∧ Real.log (1899 : ℕ) ≤ ((47181767/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1900 :
    ((150992183/20000000 : ℚ) : ℝ) ≤ Real.log (1900 : ℕ)
      ∧ Real.log (1900 : ℕ) ≤ ((754960917/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1901 :
    ((755013533/100000000 : ℚ) : ℝ) ≤ Real.log (1901 : ℕ)
      ∧ Real.log (1901 : ℕ) ≤ ((151002707/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1902 :
    ((755066123/100000000 : ℚ) : ℝ) ≤ Real.log (1902 : ℕ)
      ∧ Real.log (1902 : ℕ) ≤ ((6040529/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1903 :
    ((377559343/50000000 : ℚ) : ℝ) ≤ Real.log (1903 : ℕ)
      ∧ Real.log (1903 : ℕ) ≤ ((755118687/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1904 :
    ((37758561/5000000 : ℚ) : ℝ) ≤ Real.log (1904 : ℕ)
      ∧ Real.log (1904 : ℕ) ≤ ((377585611/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1905 :
    ((47201483/6250000 : ℚ) : ℝ) ≤ Real.log (1905 : ℕ)
      ∧ Real.log (1905 : ℕ) ≤ ((755223729/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1906 :
    ((755276207/100000000 : ℚ) : ℝ) ≤ Real.log (1906 : ℕ)
      ∧ Real.log (1906 : ℕ) ≤ ((755276209/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1907 :
    ((755328659/100000000 : ℚ) : ℝ) ≤ Real.log (1907 : ℕ)
      ∧ Real.log (1907 : ℕ) ≤ ((755328661/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1908 :
    ((188845271/25000000 : ℚ) : ℝ) ≤ Real.log (1908 : ℕ)
      ∧ Real.log (1908 : ℕ) ≤ ((377690543/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1909 :
    ((755433481/100000000 : ℚ) : ℝ) ≤ Real.log (1909 : ℕ)
      ∧ Real.log (1909 : ℕ) ≤ ((755433483/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1910 :
    ((755485851/100000000 : ℚ) : ℝ) ≤ Real.log (1910 : ℕ)
      ∧ Real.log (1910 : ℕ) ≤ ((755485853/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1911 :
    ((755538193/100000000 : ℚ) : ℝ) ≤ Real.log (1911 : ℕ)
      ∧ Real.log (1911 : ℕ) ≤ ((151107639/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1912 :
    ((188897627/25000000 : ℚ) : ℝ) ≤ Real.log (1912 : ℕ)
      ∧ Real.log (1912 : ℕ) ≤ ((75559051/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1913 :
    ((188910699/25000000 : ℚ) : ℝ) ≤ Real.log (1913 : ℕ)
      ∧ Real.log (1913 : ℕ) ≤ ((377821399/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1914 :
    ((47230941/6250000 : ℚ) : ℝ) ≤ Real.log (1914 : ℕ)
      ∧ Real.log (1914 : ℕ) ≤ ((377847529/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1915 :
    ((755747289/100000000 : ℚ) : ℝ) ≤ Real.log (1915 : ℕ)
      ∧ Real.log (1915 : ℕ) ≤ ((755747291/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1916 :
    ((151159899/20000000 : ℚ) : ℝ) ≤ Real.log (1916 : ℕ)
      ∧ Real.log (1916 : ℕ) ≤ ((94474937/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1917 :
    ((755851673/100000000 : ℚ) : ℝ) ≤ Real.log (1917 : ℕ)
      ∧ Real.log (1917 : ℕ) ≤ ((30234067/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1918 :
    ((47243989/6250000 : ℚ) : ℝ) ≤ Real.log (1918 : ℕ)
      ∧ Real.log (1918 : ℕ) ≤ ((377951913/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1919 :
    ((755955949/100000000 : ℚ) : ℝ) ≤ Real.log (1919 : ℕ)
      ∧ Real.log (1919 : ℕ) ≤ ((15119119/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1920 :
    ((151201609/20000000 : ℚ) : ℝ) ≤ Real.log (1920 : ℕ)
      ∧ Real.log (1920 : ℕ) ≤ ((756008047/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1921 :
    ((151212023/20000000 : ℚ) : ℝ) ≤ Real.log (1921 : ℕ)
      ∧ Real.log (1921 : ℕ) ≤ ((756060117/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1922 :
    ((378056079/50000000 : ℚ) : ℝ) ≤ Real.log (1922 : ℕ)
      ∧ Real.log (1922 : ℕ) ≤ ((4725701/625000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1923 :
    ((756164173/100000000 : ℚ) : ℝ) ≤ Real.log (1923 : ℕ)
      ∧ Real.log (1923 : ℕ) ≤ ((30246567/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1924 :
    ((378108081/50000000 : ℚ) : ℝ) ≤ Real.log (1924 : ℕ)
      ∧ Real.log (1924 : ℕ) ≤ ((189054041/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1925 :
    ((189067031/25000000 : ℚ) : ℝ) ≤ Real.log (1925 : ℕ)
      ∧ Real.log (1925 : ℕ) ≤ ((1210029/160000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1926 :
    ((378160029/50000000 : ℚ) : ℝ) ≤ Real.log (1926 : ℕ)
      ∧ Real.log (1926 : ℕ) ≤ ((37816003/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1927 :
    ((378185983/50000000 : ℚ) : ℝ) ≤ Real.log (1927 : ℕ)
      ∧ Real.log (1927 : ℕ) ≤ ((756371967/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1928 :
    ((378211923/50000000 : ℚ) : ℝ) ≤ Real.log (1928 : ℕ)
      ∧ Real.log (1928 : ℕ) ≤ ((94552981/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1929 :
    ((7564757/1000000 : ℚ) : ℝ) ≤ Real.log (1929 : ℕ)
      ∧ Real.log (1929 : ℕ) ≤ ((378237851/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1930 :
    ((756527527/100000000 : ℚ) : ℝ) ≤ Real.log (1930 : ℕ)
      ∧ Real.log (1930 : ℕ) ≤ ((756527529/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1931 :
    ((756579327/100000000 : ℚ) : ℝ) ≤ Real.log (1931 : ℕ)
      ∧ Real.log (1931 : ℕ) ≤ ((756579329/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1932 :
    ((7566311/1000000 : ℚ) : ℝ) ≤ Real.log (1932 : ℕ)
      ∧ Real.log (1932 : ℕ) ≤ ((378315551/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1933 :
    ((756682847/100000000 : ℚ) : ℝ) ≤ Real.log (1933 : ℕ)
      ∧ Real.log (1933 : ℕ) ≤ ((756682849/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1934 :
    ((756734567/100000000 : ℚ) : ℝ) ≤ Real.log (1934 : ℕ)
      ∧ Real.log (1934 : ℕ) ≤ ((94591821/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1935 :
    ((37839313/5000000 : ℚ) : ℝ) ≤ Real.log (1935 : ℕ)
      ∧ Real.log (1935 : ℕ) ≤ ((756786261/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1936 :
    ((378418963/50000000 : ℚ) : ℝ) ≤ Real.log (1936 : ℕ)
      ∧ Real.log (1936 : ℕ) ≤ ((756837927/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1937 :
    ((151377913/20000000 : ℚ) : ℝ) ≤ Real.log (1937 : ℕ)
      ∧ Real.log (1937 : ℕ) ≤ ((756889567/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1938 :
    ((378470589/50000000 : ℚ) : ℝ) ≤ Real.log (1938 : ℕ)
      ∧ Real.log (1938 : ℕ) ≤ ((37847059/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1939 :
    ((151398553/20000000 : ℚ) : ℝ) ≤ Real.log (1939 : ℕ)
      ∧ Real.log (1939 : ℕ) ≤ ((378496383/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1940 :
    ((189261081/25000000 : ℚ) : ℝ) ≤ Real.log (1940 : ℕ)
      ∧ Real.log (1940 : ℕ) ≤ ((378522163/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1941 :
    ((757095857/100000000 : ℚ) : ℝ) ≤ Real.log (1941 : ℕ)
      ∧ Real.log (1941 : ℕ) ≤ ((757095859/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1942 :
    ((189286841/25000000 : ℚ) : ℝ) ≤ Real.log (1942 : ℕ)
      ∧ Real.log (1942 : ℕ) ≤ ((151429473/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1943 :
    ((189299711/25000000 : ℚ) : ℝ) ≤ Real.log (1943 : ℕ)
      ∧ Real.log (1943 : ℕ) ≤ ((378599423/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1944 :
    ((378625149/50000000 : ℚ) : ℝ) ≤ Real.log (1944 : ℕ)
      ∧ Real.log (1944 : ℕ) ≤ ((757250299/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1945 :
    ((30292069/4000000 : ℚ) : ℝ) ≤ Real.log (1945 : ℕ)
      ∧ Real.log (1945 : ℕ) ≤ ((378650863/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1946 :
    ((242353/32000 : ℚ) : ℝ) ≤ Real.log (1946 : ℕ)
      ∧ Real.log (1946 : ℕ) ≤ ((757353127/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1947 :
    ((1514809/200000 : ℚ) : ℝ) ≤ Real.log (1947 : ℕ)
      ∧ Real.log (1947 : ℕ) ≤ ((757404501/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1948 :
    ((757455847/100000000 : ℚ) : ℝ) ≤ Real.log (1948 : ℕ)
      ∧ Real.log (1948 : ℕ) ≤ ((757455849/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1949 :
    ((757507169/100000000 : ℚ) : ℝ) ≤ Real.log (1949 : ℕ)
      ∧ Real.log (1949 : ℕ) ≤ ((757507171/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1950 :
    ((11836851/1562500 : ℚ) : ℝ) ≤ Real.log (1950 : ℕ)
      ∧ Real.log (1950 : ℕ) ≤ ((378779233/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1951 :
    ((757609733/100000000 : ℚ) : ℝ) ≤ Real.log (1951 : ℕ)
      ∧ Real.log (1951 : ℕ) ≤ ((151521947/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1952 :
    ((47353811/6250000 : ℚ) : ℝ) ≤ Real.log (1952 : ℕ)
      ∧ Real.log (1952 : ℕ) ≤ ((757660977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1953 :
    ((11839253/1562500 : ℚ) : ℝ) ≤ Real.log (1953 : ℕ)
      ∧ Real.log (1953 : ℕ) ≤ ((378856097/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1954 :
    ((378881691/50000000 : ℚ) : ℝ) ≤ Real.log (1954 : ℕ)
      ∧ Real.log (1954 : ℕ) ≤ ((94720423/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1955 :
    ((378907273/50000000 : ℚ) : ℝ) ≤ Real.log (1955 : ℕ)
      ∧ Real.log (1955 : ℕ) ≤ ((189453637/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1956 :
    ((189466421/25000000 : ℚ) : ℝ) ≤ Real.log (1956 : ℕ)
      ∧ Real.log (1956 : ℕ) ≤ ((378932843/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1957 :
    ((189479199/25000000 : ℚ) : ℝ) ≤ Real.log (1957 : ℕ)
      ∧ Real.log (1957 : ℕ) ≤ ((757916797/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1958 :
    ((757967881/100000000 : ℚ) : ℝ) ≤ Real.log (1958 : ℕ)
      ∧ Real.log (1958 : ℕ) ≤ ((757967883/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1959 :
    ((758018941/100000000 : ℚ) : ℝ) ≤ Real.log (1959 : ℕ)
      ∧ Real.log (1959 : ℕ) ≤ ((379009471/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1960 :
    ((379034987/50000000 : ℚ) : ℝ) ≤ Real.log (1960 : ℕ)
      ∧ Real.log (1960 : ℕ) ≤ ((94758747/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1961 :
    ((379060491/50000000 : ℚ) : ℝ) ≤ Real.log (1961 : ℕ)
      ∧ Real.log (1961 : ℕ) ≤ ((758120983/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1962 :
    ((758171963/100000000 : ℚ) : ℝ) ≤ Real.log (1962 : ℕ)
      ∧ Real.log (1962 : ℕ) ≤ ((151634393/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1963 :
    ((758222919/100000000 : ℚ) : ℝ) ≤ Real.log (1963 : ℕ)
      ∧ Real.log (1963 : ℕ) ≤ ((18955573/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1964 :
    ((94784231/12500000 : ℚ) : ℝ) ≤ Real.log (1964 : ℕ)
      ∧ Real.log (1964 : ℕ) ≤ ((758273849/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1965 :
    ((47395297/6250000 : ℚ) : ℝ) ≤ Real.log (1965 : ℕ)
      ∧ Real.log (1965 : ℕ) ≤ ((758324753/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1966 :
    ((758375629/100000000 : ℚ) : ℝ) ≤ Real.log (1966 : ℕ)
      ∧ Real.log (1966 : ℕ) ≤ ((758375631/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1967 :
    ((758426481/100000000 : ℚ) : ℝ) ≤ Real.log (1967 : ℕ)
      ∧ Real.log (1967 : ℕ) ≤ ((379213241/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1968 :
    ((758477307/100000000 : ℚ) : ℝ) ≤ Real.log (1968 : ℕ)
      ∧ Real.log (1968 : ℕ) ≤ ((189619327/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1969 :
    ((758528107/100000000 : ℚ) : ℝ) ≤ Real.log (1969 : ℕ)
      ∧ Real.log (1969 : ℕ) ≤ ((189632027/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1970 :
    ((758578881/100000000 : ℚ) : ℝ) ≤ Real.log (1970 : ℕ)
      ∧ Real.log (1970 : ℕ) ≤ ((758578883/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1971 :
    ((75862963/10000000 : ℚ) : ℝ) ≤ Real.log (1971 : ℕ)
      ∧ Real.log (1971 : ℕ) ≤ ((758629631/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1972 :
    ((758680353/100000000 : ℚ) : ℝ) ≤ Real.log (1972 : ℕ)
      ∧ Real.log (1972 : ℕ) ≤ ((379340177/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1973 :
    ((15174621/2000000 : ℚ) : ℝ) ≤ Real.log (1973 : ℕ)
      ∧ Real.log (1973 : ℕ) ≤ ((758731051/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1974 :
    ((758781721/100000000 : ℚ) : ℝ) ≤ Real.log (1974 : ℕ)
      ∧ Real.log (1974 : ℕ) ≤ ((758781723/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1975 :
    ((758832367/100000000 : ℚ) : ℝ) ≤ Real.log (1975 : ℕ)
      ∧ Real.log (1975 : ℕ) ≤ ((47427023/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1976 :
    ((758882987/100000000 : ℚ) : ℝ) ≤ Real.log (1976 : ℕ)
      ∧ Real.log (1976 : ℕ) ≤ ((189720747/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1977 :
    ((758933581/100000000 : ℚ) : ℝ) ≤ Real.log (1977 : ℕ)
      ∧ Real.log (1977 : ℕ) ≤ ((758933583/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1978 :
    ((15179683/2000000 : ℚ) : ℝ) ≤ Real.log (1978 : ℕ)
      ∧ Real.log (1978 : ℕ) ≤ ((94873019/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1979 :
    ((379517347/50000000 : ℚ) : ℝ) ≤ Real.log (1979 : ℕ)
      ∧ Real.log (1979 : ℕ) ≤ ((151806939/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1980 :
    ((189771303/25000000 : ℚ) : ℝ) ≤ Real.log (1980 : ℕ)
      ∧ Real.log (1980 : ℕ) ≤ ((759085213/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1981 :
    ((94891963/12500000 : ℚ) : ℝ) ≤ Real.log (1981 : ℕ)
      ∧ Real.log (1981 : ℕ) ≤ ((151827141/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1982 :
    ((759186171/100000000 : ℚ) : ℝ) ≤ Real.log (1982 : ℕ)
      ∧ Real.log (1982 : ℕ) ≤ ((189796543/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1983 :
    ((189809153/25000000 : ℚ) : ℝ) ≤ Real.log (1983 : ℕ)
      ∧ Real.log (1983 : ℕ) ≤ ((759236613/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1984 :
    ((189821757/25000000 : ℚ) : ℝ) ≤ Real.log (1984 : ℕ)
      ∧ Real.log (1984 : ℕ) ≤ ((759287029/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1985 :
    ((759337419/100000000 : ℚ) : ℝ) ≤ Real.log (1985 : ℕ)
      ∧ Real.log (1985 : ℕ) ≤ ((37966871/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1986 :
    ((94923473/12500000 : ℚ) : ℝ) ≤ Real.log (1986 : ℕ)
      ∧ Real.log (1986 : ℕ) ≤ ((151877557/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1987 :
    ((759438123/100000000 : ℚ) : ℝ) ≤ Real.log (1987 : ℕ)
      ∧ Real.log (1987 : ℕ) ≤ ((1215101/160000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1988 :
    ((379744219/50000000 : ℚ) : ℝ) ≤ Real.log (1988 : ℕ)
      ∧ Real.log (1988 : ℕ) ≤ ((759488439/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1989 :
    ((759538727/100000000 : ℚ) : ℝ) ≤ Real.log (1989 : ℕ)
      ∧ Real.log (1989 : ℕ) ≤ ((94942341/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1990 :
    ((759588991/100000000 : ℚ) : ℝ) ≤ Real.log (1990 : ℕ)
      ∧ Real.log (1990 : ℕ) ≤ ((5934289/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1991 :
    ((75963923/10000000 : ℚ) : ℝ) ≤ Real.log (1991 : ℕ)
      ∧ Real.log (1991 : ℕ) ≤ ((759639231/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1992 :
    ((759689443/100000000 : ℚ) : ℝ) ≤ Real.log (1992 : ℕ)
      ∧ Real.log (1992 : ℕ) ≤ ((189922361/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1993 :
    ((759739631/100000000 : ℚ) : ℝ) ≤ Real.log (1993 : ℕ)
      ∧ Real.log (1993 : ℕ) ≤ ((759739633/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1994 :
    ((379894897/50000000 : ℚ) : ℝ) ≤ Real.log (1994 : ℕ)
      ∧ Real.log (1994 : ℕ) ≤ ((189947449/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1995 :
    ((189959983/25000000 : ℚ) : ℝ) ≤ Real.log (1995 : ℕ)
      ∧ Real.log (1995 : ℕ) ≤ ((759839933/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1996 :
    ((151978009/20000000 : ℚ) : ℝ) ≤ Real.log (1996 : ℕ)
      ∧ Real.log (1996 : ℕ) ≤ ((379945023/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1997 :
    ((759940133/100000000 : ℚ) : ℝ) ≤ Real.log (1997 : ℕ)
      ∧ Real.log (1997 : ℕ) ≤ ((379970067/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1998 :
    ((151998039/20000000 : ℚ) : ℝ) ≤ Real.log (1998 : ℕ)
      ∧ Real.log (1998 : ℕ) ≤ ((189997549/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_1999 :
    ((760040233/100000000 : ℚ) : ℝ) ≤ Real.log (1999 : ℕ)
      ∧ Real.log (1999 : ℕ) ≤ ((380020117/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_brs_2000 :
    ((152018049/20000000 : ℚ) : ℝ) ≤ Real.log (2000 : ℕ)
      ∧ Real.log (2000 : ℕ) ≤ ((760090247/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_brs_2000
end AxiomAudit
