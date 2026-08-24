import RequestProject.DVPLogBracket

/-!
# Natural-log brackets 501-1000 (quarter-station support)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_501 :
    ((62166061/10000000 : ℚ) : ℝ) ≤ Real.log (501 : ℕ)
      ∧ Real.log (501 : ℕ) ≤ ((31083031/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_502 :
    ((62186001/10000000 : ℚ) : ℝ) ≤ Real.log (502 : ℕ)
      ∧ Real.log (502 : ℕ) ≤ ((31093001/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_503 :
    ((62205901/10000000 : ℚ) : ℝ) ≤ Real.log (503 : ℕ)
      ∧ Real.log (503 : ℕ) ≤ ((31102951/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_504 :
    ((31112881/5000000 : ℚ) : ℝ) ≤ Real.log (504 : ℕ)
      ∧ Real.log (504 : ℕ) ≤ ((62225763/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_505 :
    ((3890349/625000 : ℚ) : ℝ) ≤ Real.log (505 : ℕ)
      ∧ Real.log (505 : ℕ) ≤ ((12449117/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_506 :
    ((31132683/5000000 : ℚ) : ℝ) ≤ Real.log (506 : ℕ)
      ∧ Real.log (506 : ℕ) ≤ ((62265367/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_507 :
    ((6228511/1000000 : ℚ) : ℝ) ≤ Real.log (507 : ℕ)
      ∧ Real.log (507 : ℕ) ≤ ((62285111/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_508 :
    ((31152407/5000000 : ℚ) : ℝ) ≤ Real.log (508 : ℕ)
      ∧ Real.log (508 : ℕ) ≤ ((12460963/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_509 :
    ((97382/15625 : ℚ) : ℝ) ≤ Real.log (509 : ℕ)
      ∧ Real.log (509 : ℕ) ≤ ((62324481/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_510 :
    ((62344107/10000000 : ℚ) : ℝ) ≤ Real.log (510 : ℕ)
      ∧ Real.log (510 : ℕ) ≤ ((15586027/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_511 :
    ((12472739/2000000 : ℚ) : ℝ) ≤ Real.log (511 : ℕ)
      ∧ Real.log (511 : ℕ) ≤ ((3897731/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_512 :
    ((31191623/5000000 : ℚ) : ℝ) ≤ Real.log (512 : ℕ)
      ∧ Real.log (512 : ℕ) ≤ ((62383247/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_513 :
    ((31201379/5000000 : ℚ) : ℝ) ≤ Real.log (513 : ℕ)
      ∧ Real.log (513 : ℕ) ≤ ((62402759/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_514 :
    ((7802779/1250000 : ℚ) : ℝ) ≤ Real.log (514 : ℕ)
      ∧ Real.log (514 : ℕ) ≤ ((62422233/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_515 :
    ((62441669/10000000 : ℚ) : ℝ) ≤ Real.log (515 : ℕ)
      ∧ Real.log (515 : ℕ) ≤ ((6244167/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_516 :
    ((62461067/10000000 : ℚ) : ℝ) ≤ Real.log (516 : ℕ)
      ∧ Real.log (516 : ℕ) ≤ ((15615267/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_517 :
    ((15620107/2500000 : ℚ) : ℝ) ≤ Real.log (517 : ℕ)
      ∧ Real.log (517 : ℕ) ≤ ((62480429/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_518 :
    ((7812469/1250000 : ℚ) : ℝ) ≤ Real.log (518 : ℕ)
      ∧ Real.log (518 : ℕ) ≤ ((62499753/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_519 :
    ((31259519/5000000 : ℚ) : ℝ) ≤ Real.log (519 : ℕ)
      ∧ Real.log (519 : ℕ) ≤ ((62519039/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_520 :
    ((3908643/625000 : ℚ) : ℝ) ≤ Real.log (520 : ℕ)
      ∧ Real.log (520 : ℕ) ≤ ((62538289/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_521 :
    ((25023/4000 : ℚ) : ℝ) ≤ Real.log (521 : ℕ)
      ∧ Real.log (521 : ℕ) ≤ ((62557501/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_522 :
    ((2503067/400000 : ℚ) : ℝ) ≤ Real.log (522 : ℕ)
      ∧ Real.log (522 : ℕ) ≤ ((15644169/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_523 :
    ((31297907/5000000 : ℚ) : ℝ) ≤ Real.log (523 : ℕ)
      ∧ Real.log (523 : ℕ) ≤ ((12519163/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_524 :
    ((15653729/2500000 : ℚ) : ℝ) ≤ Real.log (524 : ℕ)
      ∧ Real.log (524 : ℕ) ≤ ((62614917/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_525 :
    ((31316991/5000000 : ℚ) : ℝ) ≤ Real.log (525 : ℕ)
      ∧ Real.log (525 : ℕ) ≤ ((62633983/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_526 :
    ((15663253/2500000 : ℚ) : ℝ) ≤ Real.log (526 : ℕ)
      ∧ Real.log (526 : ℕ) ≤ ((62653013/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_527 :
    ((12534401/2000000 : ℚ) : ℝ) ≤ Real.log (527 : ℕ)
      ∧ Real.log (527 : ℕ) ≤ ((31336003/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_528 :
    ((31345481/5000000 : ℚ) : ℝ) ≤ Real.log (528 : ℕ)
      ∧ Real.log (528 : ℕ) ≤ ((62690963/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_529 :
    ((15677471/2500000 : ℚ) : ℝ) ≤ Real.log (529 : ℕ)
      ∧ Real.log (529 : ℕ) ≤ ((12541977/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_530 :
    ((6272877/1000000 : ℚ) : ℝ) ≤ Real.log (530 : ℕ)
      ∧ Real.log (530 : ℕ) ≤ ((62728771/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_531 :
    ((3137381/500000 : ℚ) : ℝ) ≤ Real.log (531 : ℕ)
      ∧ Real.log (531 : ℕ) ≤ ((62747621/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_532 :
    ((31383217/5000000 : ℚ) : ℝ) ≤ Real.log (532 : ℕ)
      ∧ Real.log (532 : ℕ) ≤ ((12553287/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_533 :
    ((31392607/5000000 : ℚ) : ℝ) ≤ Real.log (533 : ℕ)
      ∧ Real.log (533 : ℕ) ≤ ((12557043/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_534 :
    ((31401979/5000000 : ℚ) : ℝ) ≤ Real.log (534 : ℕ)
      ∧ Real.log (534 : ℕ) ≤ ((62803959/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_535 :
    ((62822667/10000000 : ℚ) : ℝ) ≤ Real.log (535 : ℕ)
      ∧ Real.log (535 : ℕ) ≤ ((15705667/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_536 :
    ((62841341/10000000 : ℚ) : ℝ) ≤ Real.log (536 : ℕ)
      ∧ Real.log (536 : ℕ) ≤ ((31420671/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_537 :
    ((3142999/500000 : ℚ) : ℝ) ≤ Real.log (537 : ℕ)
      ∧ Real.log (537 : ℕ) ≤ ((62859981/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_538 :
    ((12575717/2000000 : ℚ) : ℝ) ≤ Real.log (538 : ℕ)
      ∧ Real.log (538 : ℕ) ≤ ((31439293/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_539 :
    ((12579431/2000000 : ℚ) : ℝ) ≤ Real.log (539 : ℕ)
      ∧ Real.log (539 : ℕ) ≤ ((15724289/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_540 :
    ((62915691/10000000 : ℚ) : ℝ) ≤ Real.log (540 : ℕ)
      ∧ Real.log (540 : ℕ) ≤ ((15728923/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_541 :
    ((3933387/625000 : ℚ) : ℝ) ≤ Real.log (541 : ℕ)
      ∧ Real.log (541 : ℕ) ≤ ((62934193/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_542 :
    ((3147633/500000 : ℚ) : ℝ) ≤ Real.log (542 : ℕ)
      ∧ Real.log (542 : ℕ) ≤ ((62952661/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_543 :
    ((62971093/10000000 : ℚ) : ℝ) ≤ Real.log (543 : ℕ)
      ∧ Real.log (543 : ℕ) ≤ ((31485547/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_544 :
    ((15747373/2500000 : ℚ) : ℝ) ≤ Real.log (544 : ℕ)
      ∧ Real.log (544 : ℕ) ≤ ((62989493/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_545 :
    ((63007857/10000000 : ℚ) : ℝ) ≤ Real.log (545 : ℕ)
      ∧ Real.log (545 : ℕ) ≤ ((31503929/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_546 :
    ((63026189/10000000 : ℚ) : ℝ) ≤ Real.log (546 : ℕ)
      ∧ Real.log (546 : ℕ) ≤ ((6302619/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_547 :
    ((7880561/1250000 : ℚ) : ℝ) ≤ Real.log (547 : ℕ)
      ∧ Real.log (547 : ℕ) ≤ ((63044489/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_548 :
    ((1970711/312500 : ℚ) : ℝ) ≤ Real.log (548 : ℕ)
      ∧ Real.log (548 : ℕ) ≤ ((63062753/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_549 :
    ((7885123/1250000 : ℚ) : ℝ) ≤ Real.log (549 : ℕ)
      ∧ Real.log (549 : ℕ) ≤ ((12616197/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_550 :
    ((31549591/5000000 : ℚ) : ℝ) ≤ Real.log (550 : ℕ)
      ∧ Real.log (550 : ℕ) ≤ ((63099183/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_551 :
    ((15779337/2500000 : ℚ) : ℝ) ≤ Real.log (551 : ℕ)
      ∧ Real.log (551 : ℕ) ≤ ((63117349/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_552 :
    ((1578387/250000 : ℚ) : ℝ) ≤ Real.log (552 : ℕ)
      ∧ Real.log (552 : ℕ) ≤ ((63135481/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_553 :
    ((3157679/500000 : ℚ) : ℝ) ≤ Real.log (553 : ℕ)
      ∧ Real.log (553 : ℕ) ≤ ((63153581/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_554 :
    ((31585823/5000000 : ℚ) : ℝ) ≤ Real.log (554 : ℕ)
      ∧ Real.log (554 : ℕ) ≤ ((63171647/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_555 :
    ((63189681/10000000 : ℚ) : ℝ) ≤ Real.log (555 : ℕ)
      ∧ Real.log (555 : ℕ) ≤ ((31594841/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_556 :
    ((31603841/5000000 : ℚ) : ℝ) ≤ Real.log (556 : ℕ)
      ∧ Real.log (556 : ℕ) ≤ ((63207683/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_557 :
    ((15806413/2500000 : ℚ) : ℝ) ≤ Real.log (557 : ℕ)
      ∧ Real.log (557 : ℕ) ≤ ((63225653/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_558 :
    ((63243589/10000000 : ℚ) : ℝ) ≤ Real.log (558 : ℕ)
      ∧ Real.log (558 : ℕ) ≤ ((6324359/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_559 :
    ((31630747/5000000 : ℚ) : ℝ) ≤ Real.log (559 : ℕ)
      ∧ Real.log (559 : ℕ) ≤ ((12652299/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_560 :
    ((63279367/10000000 : ℚ) : ℝ) ≤ Real.log (560 : ℕ)
      ∧ Real.log (560 : ℕ) ≤ ((7909921/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_561 :
    ((63297209/10000000 : ℚ) : ℝ) ≤ Real.log (561 : ℕ)
      ∧ Real.log (561 : ℕ) ≤ ((6329721/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_562 :
    ((31657509/5000000 : ℚ) : ℝ) ≤ Real.log (562 : ℕ)
      ∧ Real.log (562 : ℕ) ≤ ((63315019/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_563 :
    ((15833199/2500000 : ℚ) : ℝ) ≤ Real.log (563 : ℕ)
      ∧ Real.log (563 : ℕ) ≤ ((63332797/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_564 :
    ((31675271/5000000 : ℚ) : ℝ) ≤ Real.log (564 : ℕ)
      ∧ Real.log (564 : ℕ) ≤ ((63350543/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_565 :
    ((63368257/10000000 : ℚ) : ℝ) ≤ Real.log (565 : ℕ)
      ∧ Real.log (565 : ℕ) ≤ ((31684129/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_566 :
    ((3169297/500000 : ℚ) : ℝ) ≤ Real.log (566 : ℕ)
      ∧ Real.log (566 : ℕ) ≤ ((63385941/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_567 :
    ((63403593/10000000 : ℚ) : ℝ) ≤ Real.log (567 : ℕ)
      ∧ Real.log (567 : ℕ) ≤ ((31701797/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_568 :
    ((31710607/5000000 : ℚ) : ℝ) ≤ Real.log (568 : ℕ)
      ∧ Real.log (568 : ℕ) ≤ ((12684243/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_569 :
    ((15859701/2500000 : ℚ) : ℝ) ≤ Real.log (569 : ℕ)
      ∧ Real.log (569 : ℕ) ≤ ((12687761/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_570 :
    ((63456363/10000000 : ℚ) : ℝ) ≤ Real.log (570 : ℕ)
      ∧ Real.log (570 : ℕ) ≤ ((15864091/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_571 :
    ((15868473/2500000 : ℚ) : ℝ) ≤ Real.log (571 : ℕ)
      ∧ Real.log (571 : ℕ) ≤ ((63473893/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_572 :
    ((63491389/10000000 : ℚ) : ℝ) ≤ Real.log (572 : ℕ)
      ∧ Real.log (572 : ℕ) ≤ ((6349139/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_573 :
    ((63508857/10000000 : ℚ) : ℝ) ≤ Real.log (573 : ℕ)
      ∧ Real.log (573 : ℕ) ≤ ((31754429/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_574 :
    ((63526293/10000000 : ℚ) : ℝ) ≤ Real.log (574 : ℕ)
      ∧ Real.log (574 : ℕ) ≤ ((31763147/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_575 :
    ((635437/100000 : ℚ) : ℝ) ≤ Real.log (575 : ℕ)
      ∧ Real.log (575 : ℕ) ≤ ((63543701/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_576 :
    ((15890269/2500000 : ℚ) : ℝ) ≤ Real.log (576 : ℕ)
      ∧ Real.log (576 : ℕ) ≤ ((63561077/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_577 :
    ((31789211/5000000 : ℚ) : ℝ) ≤ Real.log (577 : ℕ)
      ∧ Real.log (577 : ℕ) ≤ ((63578423/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_578 :
    ((31797869/5000000 : ℚ) : ℝ) ≤ Real.log (578 : ℕ)
      ∧ Real.log (578 : ℕ) ≤ ((63595739/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_579 :
    ((1987907/312500 : ℚ) : ℝ) ≤ Real.log (579 : ℕ)
      ∧ Real.log (579 : ℕ) ≤ ((2544521/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_580 :
    ((63630281/10000000 : ℚ) : ℝ) ≤ Real.log (580 : ℕ)
      ∧ Real.log (580 : ℕ) ≤ ((31815141/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_581 :
    ((63647507/10000000 : ℚ) : ℝ) ≤ Real.log (581 : ℕ)
      ∧ Real.log (581 : ℕ) ≤ ((15911877/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_582 :
    ((994761/156250 : ℚ) : ℝ) ≤ Real.log (582 : ℕ)
      ∧ Real.log (582 : ℕ) ≤ ((12732941/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_583 :
    ((63681871/10000000 : ℚ) : ℝ) ≤ Real.log (583 : ℕ)
      ∧ Real.log (583 : ℕ) ≤ ((3980117/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_584 :
    ((63699009/10000000 : ℚ) : ℝ) ≤ Real.log (584 : ℕ)
      ∧ Real.log (584 : ℕ) ≤ ((6369901/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_585 :
    ((31858059/5000000 : ℚ) : ℝ) ≤ Real.log (585 : ℕ)
      ∧ Real.log (585 : ℕ) ≤ ((63716119/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_586 :
    ((63733197/10000000 : ℚ) : ℝ) ≤ Real.log (586 : ℕ)
      ∧ Real.log (586 : ℕ) ≤ ((31866599/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_587 :
    ((7968781/1250000 : ℚ) : ℝ) ≤ Real.log (587 : ℕ)
      ∧ Real.log (587 : ℕ) ≤ ((63750249/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_588 :
    ((63767269/10000000 : ℚ) : ℝ) ≤ Real.log (588 : ℕ)
      ∧ Real.log (588 : ℕ) ≤ ((6376727/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_589 :
    ((63784261/10000000 : ℚ) : ℝ) ≤ Real.log (589 : ℕ)
      ∧ Real.log (589 : ℕ) ≤ ((31892131/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_590 :
    ((2552049/400000 : ℚ) : ℝ) ≤ Real.log (590 : ℕ)
      ∧ Real.log (590 : ℕ) ≤ ((31900613/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_591 :
    ((797727/125000 : ℚ) : ℝ) ≤ Real.log (591 : ℕ)
      ∧ Real.log (591 : ℕ) ≤ ((63818161/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_592 :
    ((31917533/5000000 : ℚ) : ℝ) ≤ Real.log (592 : ℕ)
      ∧ Real.log (592 : ℕ) ≤ ((63835067/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_593 :
    ((31925971/5000000 : ℚ) : ℝ) ≤ Real.log (593 : ℕ)
      ∧ Real.log (593 : ℕ) ≤ ((12770389/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_594 :
    ((63868793/10000000 : ℚ) : ℝ) ≤ Real.log (594 : ℕ)
      ∧ Real.log (594 : ℕ) ≤ ((31934397/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_595 :
    ((31942807/5000000 : ℚ) : ℝ) ≤ Real.log (595 : ℕ)
      ∧ Real.log (595 : ℕ) ≤ ((12777123/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_596 :
    ((31951203/5000000 : ℚ) : ℝ) ≤ Real.log (596 : ℕ)
      ∧ Real.log (596 : ℕ) ≤ ((63902407/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_597 :
    ((63919171/10000000 : ℚ) : ℝ) ≤ Real.log (597 : ℕ)
      ∧ Real.log (597 : ℕ) ≤ ((15979793/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_598 :
    ((63935907/10000000 : ℚ) : ℝ) ≤ Real.log (598 : ℕ)
      ∧ Real.log (598 : ℕ) ≤ ((15983977/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_599 :
    ((12790523/2000000 : ℚ) : ℝ) ≤ Real.log (599 : ℕ)
      ∧ Real.log (599 : ℕ) ≤ ((7994077/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_600 :
    ((3998081/625000 : ℚ) : ℝ) ≤ Real.log (600 : ℕ)
      ∧ Real.log (600 : ℕ) ≤ ((63969297/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_601 :
    ((63985949/10000000 : ℚ) : ℝ) ≤ Real.log (601 : ℕ)
      ∧ Real.log (601 : ℕ) ≤ ((1279719/200000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_602 :
    ((32001287/5000000 : ℚ) : ℝ) ≤ Real.log (602 : ℕ)
      ∧ Real.log (602 : ℕ) ≤ ((2560103/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_603 :
    ((64019171/10000000 : ℚ) : ℝ) ≤ Real.log (603 : ℕ)
      ∧ Real.log (603 : ℕ) ≤ ((16004793/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_604 :
    ((64035741/10000000 : ℚ) : ℝ) ≤ Real.log (604 : ℕ)
      ∧ Real.log (604 : ℕ) ≤ ((32017871/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_605 :
    ((16013071/2500000 : ℚ) : ℝ) ≤ Real.log (605 : ℕ)
      ∧ Real.log (605 : ℕ) ≤ ((12810457/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_606 :
    ((64068799/10000000 : ℚ) : ℝ) ≤ Real.log (606 : ℕ)
      ∧ Real.log (606 : ℕ) ≤ ((40043/6250 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_607 :
    ((64085287/10000000 : ℚ) : ℝ) ≤ Real.log (607 : ℕ)
      ∧ Real.log (607 : ℕ) ≤ ((8010661/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_608 :
    ((16025437/2500000 : ℚ) : ℝ) ≤ Real.log (608 : ℕ)
      ∧ Real.log (608 : ℕ) ≤ ((64101749/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_609 :
    ((32059091/5000000 : ℚ) : ℝ) ≤ Real.log (609 : ℕ)
      ∧ Real.log (609 : ℕ) ≤ ((64118183/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_610 :
    ((64134589/10000000 : ℚ) : ℝ) ≤ Real.log (610 : ℕ)
      ∧ Real.log (610 : ℕ) ≤ ((6413459/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_611 :
    ((64150969/10000000 : ℚ) : ℝ) ≤ Real.log (611 : ℕ)
      ∧ Real.log (611 : ℕ) ≤ ((6415097/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_612 :
    ((32083661/5000000 : ℚ) : ℝ) ≤ Real.log (612 : ℕ)
      ∧ Real.log (612 : ℕ) ≤ ((64167323/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_613 :
    ((64183649/10000000 : ℚ) : ℝ) ≤ Real.log (613 : ℕ)
      ∧ Real.log (613 : ℕ) ≤ ((1283673/200000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_614 :
    ((64199949/10000000 : ℚ) : ℝ) ≤ Real.log (614 : ℕ)
      ∧ Real.log (614 : ℕ) ≤ ((1283999/200000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_615 :
    ((32108111/5000000 : ℚ) : ℝ) ≤ Real.log (615 : ℕ)
      ∧ Real.log (615 : ℕ) ≤ ((64216223/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_616 :
    ((64232469/10000000 : ℚ) : ℝ) ≤ Real.log (616 : ℕ)
      ∧ Real.log (616 : ℕ) ≤ ((6423247/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_617 :
    ((6424869/1000000 : ℚ) : ℝ) ≤ Real.log (617 : ℕ)
      ∧ Real.log (617 : ℕ) ≤ ((64248691/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_618 :
    ((16066221/2500000 : ℚ) : ℝ) ≤ Real.log (618 : ℕ)
      ∧ Real.log (618 : ℕ) ≤ ((12852977/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_619 :
    ((16070263/2500000 : ℚ) : ℝ) ≤ Real.log (619 : ℕ)
      ∧ Real.log (619 : ℕ) ≤ ((64281053/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_620 :
    ((32148597/5000000 : ℚ) : ℝ) ≤ Real.log (620 : ℕ)
      ∧ Real.log (620 : ℕ) ≤ ((12859439/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_621 :
    ((6431331/1000000 : ℚ) : ℝ) ≤ Real.log (621 : ℕ)
      ∧ Real.log (621 : ℕ) ≤ ((64313311/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_622 :
    ((321647/50000 : ℚ) : ℝ) ≤ Real.log (622 : ℕ)
      ∧ Real.log (622 : ℕ) ≤ ((64329401/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_623 :
    ((12869093/2000000 : ℚ) : ℝ) ≤ Real.log (623 : ℕ)
      ∧ Real.log (623 : ℕ) ≤ ((32172733/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_624 :
    ((64361503/10000000 : ℚ) : ℝ) ≤ Real.log (624 : ℕ)
      ∧ Real.log (624 : ℕ) ≤ ((2011297/312500 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_625 :
    ((16094379/2500000 : ℚ) : ℝ) ≤ Real.log (625 : ℕ)
      ∧ Real.log (625 : ℕ) ≤ ((64377517/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_626 :
    ((64393503/10000000 : ℚ) : ℝ) ≤ Real.log (626 : ℕ)
      ∧ Real.log (626 : ℕ) ≤ ((2012297/312500 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_627 :
    ((12881893/2000000 : ℚ) : ℝ) ≤ Real.log (627 : ℕ)
      ∧ Real.log (627 : ℕ) ≤ ((32204733/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_628 :
    ((64425401/10000000 : ℚ) : ℝ) ≤ Real.log (628 : ℕ)
      ∧ Real.log (628 : ℕ) ≤ ((32212701/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_629 :
    ((2013791/312500 : ℚ) : ℝ) ≤ Real.log (629 : ℕ)
      ∧ Real.log (629 : ℕ) ≤ ((64441313/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_630 :
    ((32228599/5000000 : ℚ) : ℝ) ≤ Real.log (630 : ℕ)
      ∧ Real.log (630 : ℕ) ≤ ((64457199/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_631 :
    ((32236529/5000000 : ℚ) : ℝ) ≤ Real.log (631 : ℕ)
      ∧ Real.log (631 : ℕ) ≤ ((64473059/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_632 :
    ((64488893/10000000 : ℚ) : ℝ) ≤ Real.log (632 : ℕ)
      ∧ Real.log (632 : ℕ) ≤ ((32244447/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_633 :
    ((503943/78125 : ℚ) : ℝ) ≤ Real.log (633 : ℕ)
      ∧ Real.log (633 : ℕ) ≤ ((12900941/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_634 :
    ((64520489/10000000 : ℚ) : ℝ) ≤ Real.log (634 : ℕ)
      ∧ Real.log (634 : ℕ) ≤ ((6452049/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_635 :
    ((8067031/1250000 : ℚ) : ℝ) ≤ Real.log (635 : ℕ)
      ∧ Real.log (635 : ℕ) ≤ ((64536251/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_636 :
    ((12910397/2000000 : ℚ) : ℝ) ≤ Real.log (636 : ℕ)
      ∧ Real.log (636 : ℕ) ≤ ((32275993/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_637 :
    ((4035481/625000 : ℚ) : ℝ) ≤ Real.log (637 : ℕ)
      ∧ Real.log (637 : ℕ) ≤ ((64567697/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_638 :
    ((32291691/5000000 : ℚ) : ℝ) ≤ Real.log (638 : ℕ)
      ∧ Real.log (638 : ℕ) ≤ ((64583383/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_639 :
    ((16149761/2500000 : ℚ) : ℝ) ≤ Real.log (639 : ℕ)
      ∧ Real.log (639 : ℕ) ≤ ((12919809/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_640 :
    ((64614681/10000000 : ℚ) : ℝ) ≤ Real.log (640 : ℕ)
      ∧ Real.log (640 : ℕ) ≤ ((32307341/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_641 :
    ((32315147/5000000 : ℚ) : ℝ) ≤ Real.log (641 : ℕ)
      ∧ Real.log (641 : ℕ) ≤ ((12926059/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_642 :
    ((64645883/10000000 : ℚ) : ℝ) ≤ Real.log (642 : ℕ)
      ∧ Real.log (642 : ℕ) ≤ ((16161471/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_643 :
    ((64661447/10000000 : ℚ) : ℝ) ≤ Real.log (643 : ℕ)
      ∧ Real.log (643 : ℕ) ≤ ((8082681/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_644 :
    ((64676987/10000000 : ℚ) : ℝ) ≤ Real.log (644 : ℕ)
      ∧ Real.log (644 : ℕ) ≤ ((16169247/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_645 :
    ((64692503/10000000 : ℚ) : ℝ) ≤ Real.log (645 : ℕ)
      ∧ Real.log (645 : ℕ) ≤ ((8086563/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_646 :
    ((12941599/2000000 : ℚ) : ℝ) ≤ Real.log (646 : ℕ)
      ∧ Real.log (646 : ℕ) ≤ ((16176999/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_647 :
    ((32361731/5000000 : ℚ) : ℝ) ≤ Real.log (647 : ℕ)
      ∧ Real.log (647 : ℕ) ≤ ((64723463/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_648 :
    ((12947781/2000000 : ℚ) : ℝ) ≤ Real.log (648 : ℕ)
      ∧ Real.log (648 : ℕ) ≤ ((16184727/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_649 :
    ((64754327/10000000 : ℚ) : ℝ) ≤ Real.log (649 : ℕ)
      ∧ Real.log (649 : ℕ) ≤ ((8094291/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_650 :
    ((64769723/10000000 : ℚ) : ℝ) ≤ Real.log (650 : ℕ)
      ∧ Real.log (650 : ℕ) ≤ ((16192431/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_651 :
    ((8098137/1250000 : ℚ) : ℝ) ≤ Real.log (651 : ℕ)
      ∧ Real.log (651 : ℕ) ≤ ((64785097/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_652 :
    ((12960089/2000000 : ℚ) : ℝ) ≤ Real.log (652 : ℕ)
      ∧ Real.log (652 : ℕ) ≤ ((32400223/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_653 :
    ((64815771/10000000 : ℚ) : ℝ) ≤ Real.log (653 : ℕ)
      ∧ Real.log (653 : ℕ) ≤ ((16203943/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_654 :
    ((64831073/10000000 : ℚ) : ℝ) ≤ Real.log (654 : ℕ)
      ∧ Real.log (654 : ℕ) ≤ ((32415537/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_655 :
    ((4052897/625000 : ℚ) : ℝ) ≤ Real.log (655 : ℕ)
      ∧ Real.log (655 : ℕ) ≤ ((64846353/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_656 :
    ((64861607/10000000 : ℚ) : ℝ) ≤ Real.log (656 : ℕ)
      ∧ Real.log (656 : ℕ) ≤ ((8107701/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_657 :
    ((1621921/250000 : ℚ) : ℝ) ≤ Real.log (657 : ℕ)
      ∧ Real.log (657 : ℕ) ≤ ((64876841/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_658 :
    ((64892049/10000000 : ℚ) : ℝ) ≤ Real.log (658 : ℕ)
      ∧ Real.log (658 : ℕ) ≤ ((1297841/200000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_659 :
    ((12981447/2000000 : ℚ) : ℝ) ≤ Real.log (659 : ℕ)
      ∧ Real.log (659 : ℕ) ≤ ((16226809/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_660 :
    ((32461199/5000000 : ℚ) : ℝ) ≤ Real.log (660 : ℕ)
      ∧ Real.log (660 : ℕ) ≤ ((64922399/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_661 :
    ((32468769/5000000 : ℚ) : ℝ) ≤ Real.log (661 : ℕ)
      ∧ Real.log (661 : ℕ) ≤ ((64937539/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_662 :
    ((12990531/2000000 : ℚ) : ℝ) ≤ Real.log (662 : ℕ)
      ∧ Real.log (662 : ℕ) ≤ ((4059541/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_663 :
    ((64967749/10000000 : ℚ) : ℝ) ≤ Real.log (663 : ℕ)
      ∧ Real.log (663 : ℕ) ≤ ((259871/40000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_664 :
    ((64982821/10000000 : ℚ) : ℝ) ≤ Real.log (664 : ℕ)
      ∧ Real.log (664 : ℕ) ≤ ((32491411/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_665 :
    ((6499787/1000000 : ℚ) : ℝ) ≤ Real.log (665 : ℕ)
      ∧ Real.log (665 : ℕ) ≤ ((64997871/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_666 :
    ((2031653/312500 : ℚ) : ℝ) ≤ Real.log (666 : ℕ)
      ∧ Real.log (666 : ℕ) ≤ ((65012897/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_667 :
    ((650279/100000 : ℚ) : ℝ) ≤ Real.log (667 : ℕ)
      ∧ Real.log (667 : ℕ) ≤ ((65027901/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_668 :
    ((65042881/10000000 : ℚ) : ℝ) ≤ Real.log (668 : ℕ)
      ∧ Real.log (668 : ℕ) ≤ ((32521441/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_669 :
    ((813223/125000 : ℚ) : ℝ) ≤ Real.log (669 : ℕ)
      ∧ Real.log (669 : ℕ) ≤ ((65057841/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_670 :
    ((8134097/1250000 : ℚ) : ℝ) ≤ Real.log (670 : ℕ)
      ∧ Real.log (670 : ℕ) ≤ ((65072779/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_671 :
    ((65087691/10000000 : ℚ) : ℝ) ≤ Real.log (671 : ℕ)
      ∧ Real.log (671 : ℕ) ≤ ((16271923/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_672 :
    ((65102583/10000000 : ℚ) : ℝ) ≤ Real.log (672 : ℕ)
      ∧ Real.log (672 : ℕ) ≤ ((8137823/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_673 :
    ((65117453/10000000 : ℚ) : ℝ) ≤ Real.log (673 : ℕ)
      ∧ Real.log (673 : ℕ) ≤ ((32558727/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_674 :
    ((651323/100000 : ℚ) : ℝ) ≤ Real.log (674 : ℕ)
      ∧ Real.log (674 : ℕ) ≤ ((65132303/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_675 :
    ((32573563/5000000 : ℚ) : ℝ) ≤ Real.log (675 : ℕ)
      ∧ Real.log (675 : ℕ) ≤ ((65147127/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_676 :
    ((6516193/1000000 : ℚ) : ℝ) ≤ Real.log (676 : ℕ)
      ∧ Real.log (676 : ℕ) ≤ ((65161931/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_677 :
    ((8147089/1250000 : ℚ) : ℝ) ≤ Real.log (677 : ℕ)
      ∧ Real.log (677 : ℕ) ≤ ((65176713/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_678 :
    ((4074467/625000 : ℚ) : ℝ) ≤ Real.log (678 : ℕ)
      ∧ Real.log (678 : ℕ) ≤ ((65191473/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_679 :
    ((65206211/10000000 : ℚ) : ℝ) ≤ Real.log (679 : ℕ)
      ∧ Real.log (679 : ℕ) ≤ ((16301553/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_680 :
    ((65220927/10000000 : ℚ) : ℝ) ≤ Real.log (680 : ℕ)
      ∧ Real.log (680 : ℕ) ≤ ((1019077/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_681 :
    ((32617811/5000000 : ℚ) : ℝ) ≤ Real.log (681 : ℕ)
      ∧ Real.log (681 : ℕ) ≤ ((104377/16000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_682 :
    ((8156287/1250000 : ℚ) : ℝ) ≤ Real.log (682 : ℕ)
      ∧ Real.log (682 : ℕ) ≤ ((65250297/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_683 :
    ((16316237/2500000 : ℚ) : ℝ) ≤ Real.log (683 : ℕ)
      ∧ Real.log (683 : ℕ) ≤ ((65264949/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_684 :
    ((65279579/10000000 : ℚ) : ℝ) ≤ Real.log (684 : ℕ)
      ∧ Real.log (684 : ℕ) ≤ ((3263979/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_685 :
    ((16323547/2500000 : ℚ) : ℝ) ≤ Real.log (685 : ℕ)
      ∧ Real.log (685 : ℕ) ≤ ((65294189/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_686 :
    ((8163597/1250000 : ℚ) : ℝ) ≤ Real.log (686 : ℕ)
      ∧ Real.log (686 : ℕ) ≤ ((65308777/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_687 :
    ((32661671/5000000 : ℚ) : ℝ) ≤ Real.log (687 : ℕ)
      ∧ Real.log (687 : ℕ) ≤ ((65323343/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_688 :
    ((2041809/312500 : ℚ) : ℝ) ≤ Real.log (688 : ℕ)
      ∧ Real.log (688 : ℕ) ≤ ((65337889/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_689 :
    ((16338103/2500000 : ℚ) : ℝ) ≤ Real.log (689 : ℕ)
      ∧ Real.log (689 : ℕ) ≤ ((65352413/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_690 :
    ((13073383/2000000 : ℚ) : ℝ) ≤ Real.log (690 : ℕ)
      ∧ Real.log (690 : ℕ) ≤ ((16341729/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_691 :
    ((32690699/5000000 : ℚ) : ℝ) ≤ Real.log (691 : ℕ)
      ∧ Real.log (691 : ℕ) ≤ ((65381399/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_692 :
    ((65395859/10000000 : ℚ) : ℝ) ≤ Real.log (692 : ℕ)
      ∧ Real.log (692 : ℕ) ≤ ((3269793/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_693 :
    ((32705149/5000000 : ℚ) : ℝ) ≤ Real.log (693 : ℕ)
      ∧ Real.log (693 : ℕ) ≤ ((65410301/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_694 :
    ((65424719/10000000 : ℚ) : ℝ) ≤ Real.log (694 : ℕ)
      ∧ Real.log (694 : ℕ) ≤ ((817809/125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_695 :
    ((32719559/5000000 : ℚ) : ℝ) ≤ Real.log (695 : ℕ)
      ∧ Real.log (695 : ℕ) ≤ ((65439119/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_696 :
    ((8181687/1250000 : ℚ) : ℝ) ≤ Real.log (696 : ℕ)
      ∧ Real.log (696 : ℕ) ≤ ((65453497/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_697 :
    ((32733927/5000000 : ℚ) : ℝ) ≤ Real.log (697 : ℕ)
      ∧ Real.log (697 : ℕ) ≤ ((13093571/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_698 :
    ((6548219/1000000 : ℚ) : ℝ) ≤ Real.log (698 : ℕ)
      ∧ Real.log (698 : ℕ) ≤ ((65482193/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_699 :
    ((65496507/10000000 : ℚ) : ℝ) ≤ Real.log (699 : ℕ)
      ∧ Real.log (699 : ℕ) ≤ ((16374127/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_700 :
    ((65510803/10000000 : ℚ) : ℝ) ≤ Real.log (700 : ℕ)
      ∧ Real.log (700 : ℕ) ≤ ((16377701/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_701 :
    ((32762539/5000000 : ℚ) : ℝ) ≤ Real.log (701 : ℕ)
      ∧ Real.log (701 : ℕ) ≤ ((65525079/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_702 :
    ((65539333/10000000 : ℚ) : ℝ) ≤ Real.log (702 : ℕ)
      ∧ Real.log (702 : ℕ) ≤ ((8192417/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_703 :
    ((2048549/312500 : ℚ) : ℝ) ≤ Real.log (703 : ℕ)
      ∧ Real.log (703 : ℕ) ≤ ((65553569/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_704 :
    ((65567783/10000000 : ℚ) : ℝ) ≤ Real.log (704 : ℕ)
      ∧ Real.log (704 : ℕ) ≤ ((8195973/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_705 :
    ((65581977/10000000 : ℚ) : ℝ) ≤ Real.log (705 : ℕ)
      ∧ Real.log (705 : ℕ) ≤ ((3279099/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_706 :
    ((8199519/1250000 : ℚ) : ℝ) ≤ Real.log (706 : ℕ)
      ∧ Real.log (706 : ℕ) ≤ ((65596153/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_707 :
    ((32805153/5000000 : ℚ) : ℝ) ≤ Real.log (707 : ℕ)
      ∧ Real.log (707 : ℕ) ≤ ((65610307/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_708 :
    ((1640611/250000 : ℚ) : ℝ) ≤ Real.log (708 : ℕ)
      ∧ Real.log (708 : ℕ) ≤ ((65624441/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_709 :
    ((13127711/2000000 : ℚ) : ℝ) ≤ Real.log (709 : ℕ)
      ∧ Real.log (709 : ℕ) ≤ ((16409639/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_710 :
    ((65652649/10000000 : ℚ) : ℝ) ≤ Real.log (710 : ℕ)
      ∧ Real.log (710 : ℕ) ≤ ((1313053/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_711 :
    ((16416681/2500000 : ℚ) : ℝ) ≤ Real.log (711 : ℕ)
      ∧ Real.log (711 : ℕ) ≤ ((2626669/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_712 :
    ((65680779/10000000 : ℚ) : ℝ) ≤ Real.log (712 : ℕ)
      ∧ Real.log (712 : ℕ) ≤ ((3284039/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_713 :
    ((32847407/5000000 : ℚ) : ℝ) ≤ Real.log (713 : ℕ)
      ∧ Real.log (713 : ℕ) ≤ ((13138963/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_714 :
    ((65708829/10000000 : ℚ) : ℝ) ≤ Real.log (714 : ℕ)
      ∧ Real.log (714 : ℕ) ≤ ((6570883/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_715 :
    ((2628913/400000 : ℚ) : ℝ) ≤ Real.log (715 : ℕ)
      ∧ Real.log (715 : ℕ) ≤ ((32861413/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_716 :
    ((65736801/10000000 : ℚ) : ℝ) ≤ Real.log (716 : ℕ)
      ∧ Real.log (716 : ℕ) ≤ ((32868401/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_717 :
    ((32875379/5000000 : ℚ) : ℝ) ≤ Real.log (717 : ℕ)
      ∧ Real.log (717 : ℕ) ≤ ((65750759/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_718 :
    ((13152939/2000000 : ℚ) : ℝ) ≤ Real.log (718 : ℕ)
      ∧ Real.log (718 : ℕ) ≤ ((8220587/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_719 :
    ((65778613/10000000 : ℚ) : ℝ) ≤ Real.log (719 : ℕ)
      ∧ Real.log (719 : ℕ) ≤ ((32889307/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_720 :
    ((514004/78125 : ℚ) : ℝ) ≤ Real.log (720 : ℕ)
      ∧ Real.log (720 : ℕ) ≤ ((65792513/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_721 :
    ((65806391/10000000 : ℚ) : ℝ) ≤ Real.log (721 : ℕ)
      ∧ Real.log (721 : ℕ) ≤ ((8225799/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_722 :
    ((65820251/10000000 : ℚ) : ℝ) ≤ Real.log (722 : ℕ)
      ∧ Real.log (722 : ℕ) ≤ ((16455063/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_723 :
    ((16458523/2500000 : ℚ) : ℝ) ≤ Real.log (723 : ℕ)
      ∧ Real.log (723 : ℕ) ≤ ((65834093/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_724 :
    ((65847913/10000000 : ℚ) : ℝ) ≤ Real.log (724 : ℕ)
      ∧ Real.log (724 : ℕ) ≤ ((32923957/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_725 :
    ((16465429/2500000 : ℚ) : ℝ) ≤ Real.log (725 : ℕ)
      ∧ Real.log (725 : ℕ) ≤ ((65861717/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_726 :
    ((131751/20000 : ℚ) : ℝ) ≤ Real.log (726 : ℕ)
      ∧ Real.log (726 : ℕ) ≤ ((65875501/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_727 :
    ((4118079/625000 : ℚ) : ℝ) ≤ Real.log (727 : ℕ)
      ∧ Real.log (727 : ℕ) ≤ ((13177853/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_728 :
    ((6590301/1000000 : ℚ) : ℝ) ≤ Real.log (728 : ℕ)
      ∧ Real.log (728 : ℕ) ≤ ((65903011/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_729 :
    ((65916737/10000000 : ℚ) : ℝ) ≤ Real.log (729 : ℕ)
      ∧ Real.log (729 : ℕ) ≤ ((32958369/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_730 :
    ((13186089/2000000 : ℚ) : ℝ) ≤ Real.log (730 : ℕ)
      ∧ Real.log (730 : ℕ) ≤ ((32965223/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_731 :
    ((32972067/5000000 : ℚ) : ℝ) ≤ Real.log (731 : ℕ)
      ∧ Real.log (731 : ℕ) ≤ ((13188827/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_732 :
    ((13191561/2000000 : ℚ) : ℝ) ≤ Real.log (732 : ℕ)
      ∧ Real.log (732 : ℕ) ≤ ((32978903/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_733 :
    ((515402/78125 : ℚ) : ℝ) ≤ Real.log (733 : ℕ)
      ∧ Real.log (733 : ℕ) ≤ ((65971459/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_734 :
    ((6598509/1000000 : ℚ) : ℝ) ≤ Real.log (734 : ℕ)
      ∧ Real.log (734 : ℕ) ≤ ((65985091/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_735 :
    ((4124919/625000 : ℚ) : ℝ) ≤ Real.log (735 : ℕ)
      ∧ Real.log (735 : ℕ) ≤ ((13199741/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_736 :
    ((66012301/10000000 : ℚ) : ℝ) ≤ Real.log (736 : ℕ)
      ∧ Real.log (736 : ℕ) ≤ ((33006151/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_737 :
    ((33012939/5000000 : ℚ) : ℝ) ≤ Real.log (737 : ℕ)
      ∧ Real.log (737 : ℕ) ≤ ((66025879/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_738 :
    ((33019719/5000000 : ℚ) : ℝ) ≤ Real.log (738 : ℕ)
      ∧ Real.log (738 : ℕ) ≤ ((66039439/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_739 :
    ((66052979/10000000 : ℚ) : ℝ) ≤ Real.log (739 : ℕ)
      ∧ Real.log (739 : ℕ) ≤ ((3302649/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_740 :
    ((66066501/10000000 : ℚ) : ℝ) ≤ Real.log (740 : ℕ)
      ∧ Real.log (740 : ℕ) ≤ ((33033251/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_741 :
    ((33040003/5000000 : ℚ) : ℝ) ≤ Real.log (741 : ℕ)
      ∧ Real.log (741 : ℕ) ≤ ((66080007/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_742 :
    ((16523373/2500000 : ℚ) : ℝ) ≤ Real.log (742 : ℕ)
      ∧ Real.log (742 : ℕ) ≤ ((66093493/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_743 :
    ((826337/125000 : ℚ) : ℝ) ≤ Real.log (743 : ℕ)
      ∧ Real.log (743 : ℕ) ≤ ((66106961/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_744 :
    ((6612041/1000000 : ℚ) : ℝ) ≤ Real.log (744 : ℕ)
      ∧ Real.log (744 : ℕ) ≤ ((66120411/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_745 :
    ((33066921/5000000 : ℚ) : ℝ) ≤ Real.log (745 : ℕ)
      ∧ Real.log (745 : ℕ) ≤ ((66133843/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_746 :
    ((13229451/2000000 : ℚ) : ℝ) ≤ Real.log (746 : ℕ)
      ∧ Real.log (746 : ℕ) ≤ ((33073629/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_747 :
    ((66160651/10000000 : ℚ) : ℝ) ≤ Real.log (747 : ℕ)
      ∧ Real.log (747 : ℕ) ≤ ((16540163/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_748 :
    ((66174029/10000000 : ℚ) : ℝ) ≤ Real.log (748 : ℕ)
      ∧ Real.log (748 : ℕ) ≤ ((6617403/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_749 :
    ((66187389/10000000 : ℚ) : ℝ) ≤ Real.log (749 : ℕ)
      ∧ Real.log (749 : ℕ) ≤ ((6618739/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_750 :
    ((16550183/2500000 : ℚ) : ℝ) ≤ Real.log (750 : ℕ)
      ∧ Real.log (750 : ℕ) ≤ ((66200733/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_751 :
    ((8276757/1250000 : ℚ) : ℝ) ≤ Real.log (751 : ℕ)
      ∧ Real.log (751 : ℕ) ≤ ((66214057/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_752 :
    ((66227363/10000000 : ℚ) : ℝ) ≤ Real.log (752 : ℕ)
      ∧ Real.log (752 : ℕ) ≤ ((16556841/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_753 :
    ((16560163/2500000 : ℚ) : ℝ) ≤ Real.log (753 : ℕ)
      ∧ Real.log (753 : ℕ) ≤ ((66240653/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_754 :
    ((66253923/10000000 : ℚ) : ℝ) ≤ Real.log (754 : ℕ)
      ∧ Real.log (754 : ℕ) ≤ ((16563481/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_755 :
    ((66267177/10000000 : ℚ) : ℝ) ≤ Real.log (755 : ℕ)
      ∧ Real.log (755 : ℕ) ≤ ((33133589/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_756 :
    ((66280413/10000000 : ℚ) : ℝ) ≤ Real.log (756 : ℕ)
      ∧ Real.log (756 : ℕ) ≤ ((33140207/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_757 :
    ((517919/78125 : ℚ) : ℝ) ≤ Real.log (757 : ℕ)
      ∧ Real.log (757 : ℕ) ≤ ((66293633/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_758 :
    ((66306833/10000000 : ℚ) : ℝ) ≤ Real.log (758 : ℕ)
      ∧ Real.log (758 : ℕ) ≤ ((33153417/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_759 :
    ((66320017/10000000 : ℚ) : ℝ) ≤ Real.log (759 : ℕ)
      ∧ Real.log (759 : ℕ) ≤ ((33160009/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_760 :
    ((518228/78125 : ℚ) : ℝ) ≤ Real.log (760 : ℕ)
      ∧ Real.log (760 : ℕ) ≤ ((13266637/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_761 :
    ((66346333/10000000 : ℚ) : ℝ) ≤ Real.log (761 : ℕ)
      ∧ Real.log (761 : ℕ) ≤ ((33173167/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_762 :
    ((13271893/2000000 : ℚ) : ℝ) ≤ Real.log (762 : ℕ)
      ∧ Real.log (762 : ℕ) ≤ ((33179733/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_763 :
    ((3318629/500000 : ℚ) : ℝ) ≤ Real.log (763 : ℕ)
      ∧ Real.log (763 : ℕ) ≤ ((66372581/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_764 :
    ((66385677/10000000 : ℚ) : ℝ) ≤ Real.log (764 : ℕ)
      ∧ Real.log (764 : ℕ) ≤ ((33192839/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_765 :
    ((33199379/5000000 : ℚ) : ℝ) ≤ Real.log (765 : ℕ)
      ∧ Real.log (765 : ℕ) ≤ ((66398759/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_766 :
    ((66411821/10000000 : ℚ) : ℝ) ≤ Real.log (766 : ℕ)
      ∧ Real.log (766 : ℕ) ≤ ((33205911/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_767 :
    ((16606217/2500000 : ℚ) : ℝ) ≤ Real.log (767 : ℕ)
      ∧ Real.log (767 : ℕ) ≤ ((66424869/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_768 :
    ((66437897/10000000 : ℚ) : ℝ) ≤ Real.log (768 : ℕ)
      ∧ Real.log (768 : ℕ) ≤ ((33218949/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_769 :
    ((66450909/10000000 : ℚ) : ℝ) ≤ Real.log (769 : ℕ)
      ∧ Real.log (769 : ℕ) ≤ ((6645091/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_770 :
    ((13292781/2000000 : ℚ) : ℝ) ≤ Real.log (770 : ℕ)
      ∧ Real.log (770 : ℕ) ≤ ((33231953/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_771 :
    ((66476883/10000000 : ℚ) : ℝ) ≤ Real.log (771 : ℕ)
      ∧ Real.log (771 : ℕ) ≤ ((16619221/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_772 :
    ((13297969/2000000 : ℚ) : ℝ) ≤ Real.log (772 : ℕ)
      ∧ Real.log (772 : ℕ) ≤ ((33244923/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_773 :
    ((6650279/1000000 : ℚ) : ℝ) ≤ Real.log (773 : ℕ)
      ∧ Real.log (773 : ℕ) ≤ ((66502791/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_774 :
    ((33257859/5000000 : ℚ) : ℝ) ≤ Real.log (774 : ℕ)
      ∧ Real.log (774 : ℕ) ≤ ((66515719/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_775 :
    ((6652863/1000000 : ℚ) : ℝ) ≤ Real.log (775 : ℕ)
      ∧ Real.log (775 : ℕ) ≤ ((66528631/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_776 :
    ((2661661/400000 : ℚ) : ℝ) ≤ Real.log (776 : ℕ)
      ∧ Real.log (776 : ℕ) ≤ ((33270763/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_777 :
    ((66554403/10000000 : ℚ) : ℝ) ≤ Real.log (777 : ℕ)
      ∧ Real.log (777 : ℕ) ≤ ((16638601/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_778 :
    ((13313453/2000000 : ℚ) : ℝ) ≤ Real.log (778 : ℕ)
      ∧ Real.log (778 : ℕ) ≤ ((33283633/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_779 :
    ((6658011/1000000 : ℚ) : ℝ) ≤ Real.log (779 : ℕ)
      ∧ Real.log (779 : ℕ) ≤ ((66580111/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_780 :
    ((66592939/10000000 : ℚ) : ℝ) ≤ Real.log (780 : ℕ)
      ∧ Real.log (780 : ℕ) ≤ ((3329647/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_781 :
    ((66605751/10000000 : ℚ) : ℝ) ≤ Real.log (781 : ℕ)
      ∧ Real.log (781 : ℕ) ≤ ((8325719/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_782 :
    ((66618547/10000000 : ℚ) : ℝ) ≤ Real.log (782 : ℕ)
      ∧ Real.log (782 : ℕ) ≤ ((16654637/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_783 :
    ((33315663/5000000 : ℚ) : ℝ) ≤ Real.log (783 : ℕ)
      ∧ Real.log (783 : ℕ) ≤ ((66631327/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_784 :
    ((6664409/1000000 : ℚ) : ℝ) ≤ Real.log (784 : ℕ)
      ∧ Real.log (784 : ℕ) ≤ ((66644091/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_785 :
    ((66656837/10000000 : ℚ) : ℝ) ≤ Real.log (785 : ℕ)
      ∧ Real.log (785 : ℕ) ≤ ((33328419/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_786 :
    ((66669567/10000000 : ℚ) : ℝ) ≤ Real.log (786 : ℕ)
      ∧ Real.log (786 : ℕ) ≤ ((520856/78125 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_787 :
    ((33341141/5000000 : ℚ) : ℝ) ≤ Real.log (787 : ℕ)
      ∧ Real.log (787 : ℕ) ≤ ((66682283/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_788 :
    ((3334749/500000 : ℚ) : ℝ) ≤ Real.log (788 : ℕ)
      ∧ Real.log (788 : ℕ) ≤ ((66694981/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_789 :
    ((66707663/10000000 : ℚ) : ℝ) ≤ Real.log (789 : ℕ)
      ∧ Real.log (789 : ℕ) ≤ ((4169229/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_790 :
    ((66720329/10000000 : ℚ) : ℝ) ≤ Real.log (790 : ℕ)
      ∧ Real.log (790 : ℕ) ≤ ((6672033/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_791 :
    ((66732979/10000000 : ℚ) : ℝ) ≤ Real.log (791 : ℕ)
      ∧ Real.log (791 : ℕ) ≤ ((3336649/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_792 :
    ((66745613/10000000 : ℚ) : ℝ) ≤ Real.log (792 : ℕ)
      ∧ Real.log (792 : ℕ) ≤ ((33372807/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_793 :
    ((8344779/1250000 : ℚ) : ℝ) ≤ Real.log (793 : ℕ)
      ∧ Real.log (793 : ℕ) ≤ ((66758233/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_794 :
    ((33385417/5000000 : ℚ) : ℝ) ≤ Real.log (794 : ℕ)
      ∧ Real.log (794 : ℕ) ≤ ((13354167/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_795 :
    ((66783421/10000000 : ℚ) : ℝ) ≤ Real.log (795 : ℕ)
      ∧ Real.log (795 : ℕ) ≤ ((33391711/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_796 :
    ((66795991/10000000 : ℚ) : ℝ) ≤ Real.log (796 : ℕ)
      ∧ Real.log (796 : ℕ) ≤ ((8349499/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_797 :
    ((33404273/5000000 : ℚ) : ℝ) ≤ Real.log (797 : ℕ)
      ∧ Real.log (797 : ℕ) ≤ ((66808547/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_798 :
    ((13364217/2000000 : ℚ) : ℝ) ≤ Real.log (798 : ℕ)
      ∧ Real.log (798 : ℕ) ≤ ((33410543/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_799 :
    ((66833609/10000000 : ℚ) : ℝ) ≤ Real.log (799 : ℕ)
      ∧ Real.log (799 : ℕ) ≤ ((6683361/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_800 :
    ((66846117/10000000 : ℚ) : ℝ) ≤ Real.log (800 : ℕ)
      ∧ Real.log (800 : ℕ) ≤ ((33423059/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_801 :
    ((66858609/10000000 : ℚ) : ℝ) ≤ Real.log (801 : ℕ)
      ∧ Real.log (801 : ℕ) ≤ ((6685861/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_802 :
    ((33435543/5000000 : ℚ) : ℝ) ≤ Real.log (802 : ℕ)
      ∧ Real.log (802 : ℕ) ≤ ((66871087/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_803 :
    ((66883547/10000000 : ℚ) : ℝ) ≤ Real.log (803 : ℕ)
      ∧ Real.log (803 : ℕ) ≤ ((16720887/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_804 :
    ((8361999/1250000 : ℚ) : ℝ) ≤ Real.log (804 : ℕ)
      ∧ Real.log (804 : ℕ) ≤ ((66895993/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_805 :
    ((33454211/5000000 : ℚ) : ℝ) ≤ Real.log (805 : ℕ)
      ∧ Real.log (805 : ℕ) ≤ ((66908423/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_806 :
    ((66920837/10000000 : ℚ) : ℝ) ≤ Real.log (806 : ℕ)
      ∧ Real.log (806 : ℕ) ≤ ((33460419/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_807 :
    ((16733309/2500000 : ℚ) : ℝ) ≤ Real.log (807 : ℕ)
      ∧ Real.log (807 : ℕ) ≤ ((66933237/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_808 :
    ((3347281/500000 : ℚ) : ℝ) ≤ Real.log (808 : ℕ)
      ∧ Real.log (808 : ℕ) ≤ ((66945621/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_809 :
    ((66957989/10000000 : ℚ) : ℝ) ≤ Real.log (809 : ℕ)
      ∧ Real.log (809 : ℕ) ≤ ((6695799/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_810 :
    ((33485171/5000000 : ℚ) : ℝ) ≤ Real.log (810 : ℕ)
      ∧ Real.log (810 : ℕ) ≤ ((66970343/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_811 :
    ((1674567/250000 : ℚ) : ℝ) ≤ Real.log (811 : ℕ)
      ∧ Real.log (811 : ℕ) ≤ ((66982681/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_812 :
    ((66995003/10000000 : ℚ) : ℝ) ≤ Real.log (812 : ℕ)
      ∧ Real.log (812 : ℕ) ≤ ((16748751/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_813 :
    ((67007311/10000000 : ℚ) : ℝ) ≤ Real.log (813 : ℕ)
      ∧ Real.log (813 : ℕ) ≤ ((4187957/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_814 :
    ((67019603/10000000 : ℚ) : ℝ) ≤ Real.log (814 : ℕ)
      ∧ Real.log (814 : ℕ) ≤ ((16754901/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_815 :
    ((67031881/10000000 : ℚ) : ℝ) ≤ Real.log (815 : ℕ)
      ∧ Real.log (815 : ℕ) ≤ ((33515941/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_816 :
    ((67044143/10000000 : ℚ) : ℝ) ≤ Real.log (816 : ℕ)
      ∧ Real.log (816 : ℕ) ≤ ((4190259/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_817 :
    ((6705639/1000000 : ℚ) : ℝ) ≤ Real.log (817 : ℕ)
      ∧ Real.log (817 : ℕ) ≤ ((67056391/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_818 :
    ((67068623/10000000 : ℚ) : ℝ) ≤ Real.log (818 : ℕ)
      ∧ Real.log (818 : ℕ) ≤ ((4191789/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_819 :
    ((1677021/250000 : ℚ) : ℝ) ≤ Real.log (819 : ℕ)
      ∧ Real.log (819 : ℕ) ≤ ((67080841/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_820 :
    ((67093043/10000000 : ℚ) : ℝ) ≤ Real.log (820 : ℕ)
      ∧ Real.log (820 : ℕ) ≤ ((16773261/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_821 :
    ((67105231/10000000 : ℚ) : ℝ) ≤ Real.log (821 : ℕ)
      ∧ Real.log (821 : ℕ) ≤ ((4194077/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_822 :
    ((67117403/10000000 : ℚ) : ℝ) ≤ Real.log (822 : ℕ)
      ∧ Real.log (822 : ℕ) ≤ ((16779351/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_823 :
    ((33564781/5000000 : ℚ) : ℝ) ≤ Real.log (823 : ℕ)
      ∧ Real.log (823 : ℕ) ≤ ((67129563/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_824 :
    ((13428341/2000000 : ℚ) : ℝ) ≤ Real.log (824 : ℕ)
      ∧ Real.log (824 : ℕ) ≤ ((33570853/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_825 :
    ((67153833/10000000 : ℚ) : ℝ) ≤ Real.log (825 : ℕ)
      ∧ Real.log (825 : ℕ) ≤ ((33576917/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_826 :
    ((67165947/10000000 : ℚ) : ℝ) ≤ Real.log (826 : ℕ)
      ∧ Real.log (826 : ℕ) ≤ ((16791487/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_827 :
    ((33589023/5000000 : ℚ) : ℝ) ≤ Real.log (827 : ℕ)
      ∧ Real.log (827 : ℕ) ≤ ((67178047/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_828 :
    ((67190131/10000000 : ℚ) : ℝ) ≤ Real.log (828 : ℕ)
      ∧ Real.log (828 : ℕ) ≤ ((16797533/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_829 :
    ((67202201/10000000 : ℚ) : ℝ) ≤ Real.log (829 : ℕ)
      ∧ Real.log (829 : ℕ) ≤ ((33601101/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_830 :
    ((67214257/10000000 : ℚ) : ℝ) ≤ Real.log (830 : ℕ)
      ∧ Real.log (830 : ℕ) ≤ ((33607129/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_831 :
    ((67226297/10000000 : ℚ) : ℝ) ≤ Real.log (831 : ℕ)
      ∧ Real.log (831 : ℕ) ≤ ((33613149/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_832 :
    ((16809581/2500000 : ℚ) : ℝ) ≤ Real.log (832 : ℕ)
      ∧ Real.log (832 : ℕ) ≤ ((2689533/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_833 :
    ((2101573/312500 : ℚ) : ℝ) ≤ Real.log (833 : ℕ)
      ∧ Real.log (833 : ℕ) ≤ ((67250337/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_834 :
    ((33631167/5000000 : ℚ) : ℝ) ≤ Real.log (834 : ℕ)
      ∧ Real.log (834 : ℕ) ≤ ((13452467/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_835 :
    ((67274317/10000000 : ℚ) : ℝ) ≤ Real.log (835 : ℕ)
      ∧ Real.log (835 : ℕ) ≤ ((33637159/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_836 :
    ((33643143/5000000 : ℚ) : ℝ) ≤ Real.log (836 : ℕ)
      ∧ Real.log (836 : ℕ) ≤ ((67286287/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_837 :
    ((210307/31250 : ℚ) : ℝ) ≤ Real.log (837 : ℕ)
      ∧ Real.log (837 : ℕ) ≤ ((67298241/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_838 :
    ((67310181/10000000 : ℚ) : ℝ) ≤ Real.log (838 : ℕ)
      ∧ Real.log (838 : ℕ) ≤ ((33655091/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_839 :
    ((67322107/10000000 : ℚ) : ℝ) ≤ Real.log (839 : ℕ)
      ∧ Real.log (839 : ℕ) ≤ ((16830527/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_840 :
    ((33667009/5000000 : ℚ) : ℝ) ≤ Real.log (840 : ℕ)
      ∧ Real.log (840 : ℕ) ≤ ((67334019/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_841 :
    ((16836479/2500000 : ℚ) : ℝ) ≤ Real.log (841 : ℕ)
      ∧ Real.log (841 : ℕ) ≤ ((67345917/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_842 :
    ((336789/50000 : ℚ) : ℝ) ≤ Real.log (842 : ℕ)
      ∧ Real.log (842 : ℕ) ≤ ((67357801/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_843 :
    ((67369669/10000000 : ℚ) : ℝ) ≤ Real.log (843 : ℕ)
      ∧ Real.log (843 : ℕ) ≤ ((6736967/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_844 :
    ((16845381/2500000 : ℚ) : ℝ) ≤ Real.log (844 : ℕ)
      ∧ Real.log (844 : ℕ) ≤ ((2695261/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_845 :
    ((33696683/5000000 : ℚ) : ℝ) ≤ Real.log (845 : ℕ)
      ∧ Real.log (845 : ℕ) ≤ ((67393367/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_846 :
    ((67405193/10000000 : ℚ) : ℝ) ≤ Real.log (846 : ℕ)
      ∧ Real.log (846 : ℕ) ≤ ((33702597/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_847 :
    ((33708503/5000000 : ℚ) : ℝ) ≤ Real.log (847 : ℕ)
      ∧ Real.log (847 : ℕ) ≤ ((67417007/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_848 :
    ((33714403/5000000 : ℚ) : ℝ) ≤ Real.log (848 : ℕ)
      ∧ Real.log (848 : ℕ) ≤ ((67428807/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_849 :
    ((67440591/10000000 : ℚ) : ℝ) ≤ Real.log (849 : ℕ)
      ∧ Real.log (849 : ℕ) ≤ ((4215037/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_850 :
    ((67452363/10000000 : ℚ) : ℝ) ≤ Real.log (850 : ℕ)
      ∧ Real.log (850 : ℕ) ≤ ((16863091/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_851 :
    ((67464121/10000000 : ℚ) : ℝ) ≤ Real.log (851 : ℕ)
      ∧ Real.log (851 : ℕ) ≤ ((33732061/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_852 :
    ((13495173/2000000 : ℚ) : ℝ) ≤ Real.log (852 : ℕ)
      ∧ Real.log (852 : ℕ) ≤ ((33737933/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_853 :
    ((13497519/2000000 : ℚ) : ℝ) ≤ Real.log (853 : ℕ)
      ∧ Real.log (853 : ℕ) ≤ ((16871899/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_854 :
    ((67499311/10000000 : ℚ) : ℝ) ≤ Real.log (854 : ℕ)
      ∧ Real.log (854 : ℕ) ≤ ((4218707/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_855 :
    ((33755507/5000000 : ℚ) : ℝ) ≤ Real.log (855 : ℕ)
      ∧ Real.log (855 : ℕ) ≤ ((13502203/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_856 :
    ((67522703/10000000 : ℚ) : ℝ) ≤ Real.log (856 : ℕ)
      ∧ Real.log (856 : ℕ) ≤ ((4220169/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_857 :
    ((67534379/10000000 : ℚ) : ℝ) ≤ Real.log (857 : ℕ)
      ∧ Real.log (857 : ℕ) ≤ ((3376719/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_858 :
    ((1688651/250000 : ℚ) : ℝ) ≤ Real.log (858 : ℕ)
      ∧ Real.log (858 : ℕ) ≤ ((67546041/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_859 :
    ((67557689/10000000 : ℚ) : ℝ) ≤ Real.log (859 : ℕ)
      ∧ Real.log (859 : ℕ) ≤ ((6755769/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_860 :
    ((67569323/10000000 : ℚ) : ℝ) ≤ Real.log (860 : ℕ)
      ∧ Real.log (860 : ℕ) ≤ ((16892331/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_861 :
    ((13516189/2000000 : ℚ) : ℝ) ≤ Real.log (861 : ℕ)
      ∧ Real.log (861 : ℕ) ≤ ((33790473/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_862 :
    ((8449069/1250000 : ℚ) : ℝ) ≤ Real.log (862 : ℕ)
      ∧ Real.log (862 : ℕ) ≤ ((67592553/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_863 :
    ((33802073/5000000 : ℚ) : ℝ) ≤ Real.log (863 : ℕ)
      ∧ Real.log (863 : ℕ) ≤ ((67604147/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_864 :
    ((67615727/10000000 : ℚ) : ℝ) ≤ Real.log (864 : ℕ)
      ∧ Real.log (864 : ℕ) ≤ ((4225983/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_865 :
    ((13525459/2000000 : ℚ) : ℝ) ≤ Real.log (865 : ℕ)
      ∧ Real.log (865 : ℕ) ≤ ((2113353/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_866 :
    ((67638849/10000000 : ℚ) : ℝ) ≤ Real.log (866 : ℕ)
      ∧ Real.log (866 : ℕ) ≤ ((1352777/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_867 :
    ((67650389/10000000 : ℚ) : ℝ) ≤ Real.log (867 : ℕ)
      ∧ Real.log (867 : ℕ) ≤ ((6765039/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_868 :
    ((67661917/10000000 : ℚ) : ℝ) ≤ Real.log (868 : ℕ)
      ∧ Real.log (868 : ℕ) ≤ ((33830959/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_869 :
    ((67673431/10000000 : ℚ) : ℝ) ≤ Real.log (869 : ℕ)
      ∧ Real.log (869 : ℕ) ≤ ((8459179/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_870 :
    ((16921233/2500000 : ℚ) : ℝ) ≤ Real.log (870 : ℕ)
      ∧ Real.log (870 : ℕ) ≤ ((67684933/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_871 :
    ((67696419/10000000 : ℚ) : ℝ) ≤ Real.log (871 : ℕ)
      ∧ Real.log (871 : ℕ) ≤ ((3384821/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_872 :
    ((33853947/5000000 : ℚ) : ℝ) ≤ Real.log (872 : ℕ)
      ∧ Real.log (872 : ℕ) ≤ ((13541579/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_873 :
    ((13543871/2000000 : ℚ) : ℝ) ≤ Real.log (873 : ℕ)
      ∧ Real.log (873 : ℕ) ≤ ((16929839/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_874 :
    ((67730803/10000000 : ℚ) : ℝ) ≤ Real.log (874 : ℕ)
      ∧ Real.log (874 : ℕ) ≤ ((16932701/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_875 :
    ((33871119/5000000 : ℚ) : ℝ) ≤ Real.log (875 : ℕ)
      ∧ Real.log (875 : ℕ) ≤ ((67742239/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_876 :
    ((3387683/500000 : ℚ) : ℝ) ≤ Real.log (876 : ℕ)
      ∧ Real.log (876 : ℕ) ≤ ((67753661/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_877 :
    ((67765069/10000000 : ℚ) : ℝ) ≤ Real.log (877 : ℕ)
      ∧ Real.log (877 : ℕ) ≤ ((6776507/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_878 :
    ((13555293/2000000 : ℚ) : ℝ) ≤ Real.log (878 : ℕ)
      ∧ Real.log (878 : ℕ) ≤ ((33888233/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_879 :
    ((8473481/1250000 : ℚ) : ℝ) ≤ Real.log (879 : ℕ)
      ∧ Real.log (879 : ℕ) ≤ ((67787849/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_880 :
    ((67799219/10000000 : ℚ) : ℝ) ≤ Real.log (880 : ℕ)
      ∧ Real.log (880 : ℕ) ≤ ((3389961/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_881 :
    ((4238161/625000 : ℚ) : ℝ) ≤ Real.log (881 : ℕ)
      ∧ Real.log (881 : ℕ) ≤ ((67810577/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_882 :
    ((423887/62500 : ℚ) : ℝ) ≤ Real.log (882 : ℕ)
      ∧ Real.log (882 : ℕ) ≤ ((67821921/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_883 :
    ((16958313/2500000 : ℚ) : ℝ) ≤ Real.log (883 : ℕ)
      ∧ Real.log (883 : ℕ) ≤ ((67833253/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_884 :
    ((6784457/1000000 : ℚ) : ℝ) ≤ Real.log (884 : ℕ)
      ∧ Real.log (884 : ℕ) ≤ ((67844571/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_885 :
    ((16963969/2500000 : ℚ) : ℝ) ≤ Real.log (885 : ℕ)
      ∧ Real.log (885 : ℕ) ≤ ((67855877/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_886 :
    ((67867169/10000000 : ℚ) : ℝ) ≤ Real.log (886 : ℕ)
      ∧ Real.log (886 : ℕ) ≤ ((6786717/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_887 :
    ((67878449/10000000 : ℚ) : ℝ) ≤ Real.log (887 : ℕ)
      ∧ Real.log (887 : ℕ) ≤ ((1357569/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_888 :
    ((67889717/10000000 : ℚ) : ℝ) ≤ Real.log (888 : ℕ)
      ∧ Real.log (888 : ℕ) ≤ ((33944859/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_889 :
    ((16975243/2500000 : ℚ) : ℝ) ≤ Real.log (889 : ℕ)
      ∧ Real.log (889 : ℕ) ≤ ((67900973/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_890 :
    ((33956107/5000000 : ℚ) : ℝ) ≤ Real.log (890 : ℕ)
      ∧ Real.log (890 : ℕ) ≤ ((13582443/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_891 :
    ((16980861/2500000 : ℚ) : ℝ) ≤ Real.log (891 : ℕ)
      ∧ Real.log (891 : ℕ) ≤ ((13584689/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_892 :
    ((67934661/10000000 : ℚ) : ℝ) ≤ Real.log (892 : ℕ)
      ∧ Real.log (892 : ℕ) ≤ ((33967331/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_893 :
    ((13589173/2000000 : ℚ) : ℝ) ≤ Real.log (893 : ℕ)
      ∧ Real.log (893 : ℕ) ≤ ((33972933/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_894 :
    ((67957057/10000000 : ℚ) : ℝ) ≤ Real.log (894 : ℕ)
      ∧ Real.log (894 : ℕ) ≤ ((33978529/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_895 :
    ((67968237/10000000 : ℚ) : ℝ) ≤ Real.log (895 : ℕ)
      ∧ Real.log (895 : ℕ) ≤ ((33984119/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_896 :
    ((16994851/2500000 : ℚ) : ℝ) ≤ Real.log (896 : ℕ)
      ∧ Real.log (896 : ℕ) ≤ ((13595881/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_897 :
    ((33995279/5000000 : ℚ) : ℝ) ≤ Real.log (897 : ℕ)
      ∧ Real.log (897 : ℕ) ≤ ((67990559/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_898 :
    ((680017/100000 : ℚ) : ℝ) ≤ Real.log (898 : ℕ)
      ∧ Real.log (898 : ℕ) ≤ ((68001701/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_899 :
    ((6801283/1000000 : ℚ) : ℝ) ≤ Real.log (899 : ℕ)
      ∧ Real.log (899 : ℕ) ≤ ((68012831/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_900 :
    ((68023947/10000000 : ℚ) : ℝ) ≤ Real.log (900 : ℕ)
      ∧ Real.log (900 : ℕ) ≤ ((17005987/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_901 :
    ((17008763/2500000 : ℚ) : ℝ) ≤ Real.log (901 : ℕ)
      ∧ Real.log (901 : ℕ) ≤ ((68035053/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_902 :
    ((13609229/2000000 : ℚ) : ℝ) ≤ Real.log (902 : ℕ)
      ∧ Real.log (902 : ℕ) ≤ ((34023073/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_903 :
    ((2722289/400000 : ℚ) : ℝ) ≤ Real.log (903 : ℕ)
      ∧ Real.log (903 : ℕ) ≤ ((34028613/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_904 :
    ((68068293/10000000 : ℚ) : ℝ) ≤ Real.log (904 : ℕ)
      ∧ Real.log (904 : ℕ) ≤ ((34034147/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_905 :
    ((68079349/10000000 : ℚ) : ℝ) ≤ Real.log (905 : ℕ)
      ∧ Real.log (905 : ℕ) ≤ ((1361587/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_906 :
    ((68090393/10000000 : ℚ) : ℝ) ≤ Real.log (906 : ℕ)
      ∧ Real.log (906 : ℕ) ≤ ((34045197/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_907 :
    ((4256339/625000 : ℚ) : ℝ) ≤ Real.log (907 : ℕ)
      ∧ Real.log (907 : ℕ) ≤ ((2724057/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_908 :
    ((68112443/10000000 : ℚ) : ℝ) ≤ Real.log (908 : ℕ)
      ∧ Real.log (908 : ℕ) ≤ ((17028111/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_909 :
    ((1362469/200000 : ℚ) : ℝ) ≤ Real.log (909 : ℕ)
      ∧ Real.log (909 : ℕ) ≤ ((68123451/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_910 :
    ((13626889/2000000 : ℚ) : ℝ) ≤ Real.log (910 : ℕ)
      ∧ Real.log (910 : ℕ) ≤ ((34067223/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_911 :
    ((17036357/2500000 : ℚ) : ℝ) ≤ Real.log (911 : ℕ)
      ∧ Real.log (911 : ℕ) ≤ ((68145429/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_912 :
    ((68156399/10000000 : ℚ) : ℝ) ≤ Real.log (912 : ℕ)
      ∧ Real.log (912 : ℕ) ≤ ((170391/25000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_913 :
    ((34083679/5000000 : ℚ) : ℝ) ≤ Real.log (913 : ℕ)
      ∧ Real.log (913 : ℕ) ≤ ((68167359/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_914 :
    ((13635661/2000000 : ℚ) : ℝ) ≤ Real.log (914 : ℕ)
      ∧ Real.log (914 : ℕ) ≤ ((34089153/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_915 :
    ((1704731/250000 : ℚ) : ℝ) ≤ Real.log (915 : ℕ)
      ∧ Real.log (915 : ℕ) ≤ ((68189241/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_916 :
    ((68200163/10000000 : ℚ) : ℝ) ≤ Real.log (916 : ℕ)
      ∧ Real.log (916 : ℕ) ≤ ((17050041/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_917 :
    ((34105537/5000000 : ℚ) : ℝ) ≤ Real.log (917 : ℕ)
      ∧ Real.log (917 : ℕ) ≤ ((2728443/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_918 :
    ((68221973/10000000 : ℚ) : ℝ) ≤ Real.log (918 : ℕ)
      ∧ Real.log (918 : ℕ) ≤ ((34110987/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_919 :
    ((68232861/10000000 : ℚ) : ℝ) ≤ Real.log (919 : ℕ)
      ∧ Real.log (919 : ℕ) ≤ ((34116431/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_920 :
    ((8530467/1250000 : ℚ) : ℝ) ≤ Real.log (920 : ℕ)
      ∧ Real.log (920 : ℕ) ≤ ((68243737/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_921 :
    ((341273/50000 : ℚ) : ℝ) ≤ Real.log (921 : ℕ)
      ∧ Real.log (921 : ℕ) ≤ ((68254601/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_922 :
    ((17066363/2500000 : ℚ) : ℝ) ≤ Real.log (922 : ℕ)
      ∧ Real.log (922 : ℕ) ≤ ((68265453/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_923 :
    ((17069073/2500000 : ℚ) : ℝ) ≤ Real.log (923 : ℕ)
      ∧ Real.log (923 : ℕ) ≤ ((68276293/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_924 :
    ((853589/125000 : ℚ) : ℝ) ≤ Real.log (924 : ℕ)
      ∧ Real.log (924 : ℕ) ≤ ((68287121/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_925 :
    ((68297937/10000000 : ℚ) : ℝ) ≤ Real.log (925 : ℕ)
      ∧ Real.log (925 : ℕ) ≤ ((34148969/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_926 :
    ((34154371/5000000 : ℚ) : ℝ) ≤ Real.log (926 : ℕ)
      ∧ Real.log (926 : ℕ) ≤ ((68308743/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_927 :
    ((13663907/2000000 : ℚ) : ℝ) ≤ Real.log (927 : ℕ)
      ∧ Real.log (927 : ℕ) ≤ ((4269971/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_928 :
    ((68330317/10000000 : ℚ) : ℝ) ≤ Real.log (928 : ℕ)
      ∧ Real.log (928 : ℕ) ≤ ((34165159/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_929 :
    ((68341087/10000000 : ℚ) : ℝ) ≤ Real.log (929 : ℕ)
      ∧ Real.log (929 : ℕ) ≤ ((2135659/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_930 :
    ((13670369/2000000 : ℚ) : ℝ) ≤ Real.log (930 : ℕ)
      ∧ Real.log (930 : ℕ) ≤ ((34175923/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_931 :
    ((2136331/312500 : ℚ) : ℝ) ≤ Real.log (931 : ℕ)
      ∧ Real.log (931 : ℕ) ≤ ((68362593/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_932 :
    ((4273333/625000 : ℚ) : ℝ) ≤ Real.log (932 : ℕ)
      ∧ Real.log (932 : ℕ) ≤ ((68373329/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_933 :
    ((17096013/2500000 : ℚ) : ℝ) ≤ Real.log (933 : ℕ)
      ∧ Real.log (933 : ℕ) ≤ ((68384053/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_934 :
    ((17098691/2500000 : ℚ) : ℝ) ≤ Real.log (934 : ℕ)
      ∧ Real.log (934 : ℕ) ≤ ((13678953/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_935 :
    ((13681093/2000000 : ℚ) : ℝ) ≤ Real.log (935 : ℕ)
      ∧ Real.log (935 : ℕ) ≤ ((34202733/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_936 :
    ((34208077/5000000 : ℚ) : ℝ) ≤ Real.log (936 : ℕ)
      ∧ Real.log (936 : ℕ) ≤ ((13683231/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_937 :
    ((4276677/625000 : ℚ) : ℝ) ≤ Real.log (937 : ℕ)
      ∧ Real.log (937 : ℕ) ≤ ((68426833/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_938 :
    ((68437499/10000000 : ℚ) : ℝ) ≤ Real.log (938 : ℕ)
      ∧ Real.log (938 : ℕ) ≤ ((219/32 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_939 :
    ((34224077/5000000 : ℚ) : ℝ) ≤ Real.log (939 : ℕ)
      ∧ Real.log (939 : ℕ) ≤ ((13689631/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_940 :
    ((34229399/5000000 : ℚ) : ℝ) ≤ Real.log (940 : ℕ)
      ∧ Real.log (940 : ℕ) ≤ ((68458799/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_941 :
    ((68469431/10000000 : ℚ) : ℝ) ≤ Real.log (941 : ℕ)
      ∧ Real.log (941 : ℕ) ≤ ((8558679/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_942 :
    ((17120013/2500000 : ℚ) : ℝ) ≤ Real.log (942 : ℕ)
      ∧ Real.log (942 : ℕ) ≤ ((68480053/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_943 :
    ((34245331/5000000 : ℚ) : ℝ) ≤ Real.log (943 : ℕ)
      ∧ Real.log (943 : ℕ) ≤ ((68490663/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_944 :
    ((68501261/10000000 : ℚ) : ℝ) ≤ Real.log (944 : ℕ)
      ∧ Real.log (944 : ℕ) ≤ ((34250631/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_945 :
    ((68511849/10000000 : ℚ) : ℝ) ≤ Real.log (945 : ℕ)
      ∧ Real.log (945 : ℕ) ≤ ((1370237/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_946 :
    ((2740897/400000 : ℚ) : ℝ) ≤ Real.log (946 : ℕ)
      ∧ Real.log (946 : ℕ) ≤ ((34261213/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_947 :
    ((6853299/1000000 : ℚ) : ℝ) ≤ Real.log (947 : ℕ)
      ∧ Real.log (947 : ℕ) ≤ ((68532991/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_948 :
    ((13708709/2000000 : ℚ) : ℝ) ≤ Real.log (948 : ℕ)
      ∧ Real.log (948 : ℕ) ≤ ((34271773/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_949 :
    ((68554087/10000000 : ℚ) : ℝ) ≤ Real.log (949 : ℕ)
      ∧ Real.log (949 : ℕ) ≤ ((8569261/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_950 :
    ((68564619/10000000 : ℚ) : ℝ) ≤ Real.log (950 : ℕ)
      ∧ Real.log (950 : ℕ) ≤ ((3428231/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_951 :
    ((3428757/500000 : ℚ) : ℝ) ≤ Real.log (951 : ℕ)
      ∧ Real.log (951 : ℕ) ≤ ((68575141/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_952 :
    ((1371713/200000 : ℚ) : ℝ) ≤ Real.log (952 : ℕ)
      ∧ Real.log (952 : ℕ) ≤ ((68585651/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_953 :
    ((68596149/10000000 : ℚ) : ℝ) ≤ Real.log (953 : ℕ)
      ∧ Real.log (953 : ℕ) ≤ ((1371923/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_954 :
    ((17151659/2500000 : ℚ) : ℝ) ≤ Real.log (954 : ℕ)
      ∧ Real.log (954 : ℕ) ≤ ((68606637/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_955 :
    ((68617113/10000000 : ℚ) : ℝ) ≤ Real.log (955 : ℕ)
      ∧ Real.log (955 : ℕ) ≤ ((34308557/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_956 :
    ((68627579/10000000 : ℚ) : ℝ) ≤ Real.log (956 : ℕ)
      ∧ Real.log (956 : ℕ) ≤ ((3431379/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_957 :
    ((68638033/10000000 : ℚ) : ℝ) ≤ Real.log (957 : ℕ)
      ∧ Real.log (957 : ℕ) ≤ ((34319017/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_958 :
    ((68648477/10000000 : ℚ) : ℝ) ≤ Real.log (958 : ℕ)
      ∧ Real.log (958 : ℕ) ≤ ((34324239/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_959 :
    ((6865891/1000000 : ℚ) : ℝ) ≤ Real.log (959 : ℕ)
      ∧ Real.log (959 : ℕ) ≤ ((68658911/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_960 :
    ((17167333/2500000 : ℚ) : ℝ) ≤ Real.log (960 : ℕ)
      ∧ Real.log (960 : ℕ) ≤ ((68669333/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_961 :
    ((1073121/156250 : ℚ) : ℝ) ≤ Real.log (961 : ℕ)
      ∧ Real.log (961 : ℕ) ≤ ((13735949/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_962 :
    ((2146567/312500 : ℚ) : ℝ) ≤ Real.log (962 : ℕ)
      ∧ Real.log (962 : ℕ) ≤ ((13738029/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_963 :
    ((34350267/5000000 : ℚ) : ℝ) ≤ Real.log (963 : ℕ)
      ∧ Real.log (963 : ℕ) ≤ ((13740107/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_964 :
    ((536804/78125 : ℚ) : ℝ) ≤ Real.log (964 : ℕ)
      ∧ Real.log (964 : ℕ) ≤ ((68710913/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_965 :
    ((68721281/10000000 : ℚ) : ℝ) ≤ Real.log (965 : ℕ)
      ∧ Real.log (965 : ℕ) ≤ ((34360641/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_966 :
    ((34365819/5000000 : ℚ) : ℝ) ≤ Real.log (966 : ℕ)
      ∧ Real.log (966 : ℕ) ≤ ((68731639/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_967 :
    ((2148187/312500 : ℚ) : ℝ) ≤ Real.log (967 : ℕ)
      ∧ Real.log (967 : ℕ) ≤ ((13748397/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_968 :
    ((214851/31250 : ℚ) : ℝ) ≤ Real.log (968 : ℕ)
      ∧ Real.log (968 : ℕ) ≤ ((68752321/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_969 :
    ((34381323/5000000 : ℚ) : ℝ) ≤ Real.log (969 : ℕ)
      ∧ Real.log (969 : ℕ) ≤ ((68762647/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_970 :
    ((429831/62500 : ℚ) : ℝ) ≤ Real.log (970 : ℕ)
      ∧ Real.log (970 : ℕ) ≤ ((68772961/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_971 :
    ((2149477/312500 : ℚ) : ℝ) ≤ Real.log (971 : ℕ)
      ∧ Real.log (971 : ℕ) ≤ ((13756653/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_972 :
    ((34396779/5000000 : ℚ) : ℝ) ≤ Real.log (972 : ℕ)
      ∧ Real.log (972 : ℕ) ≤ ((68793559/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_973 :
    ((107506/15625 : ℚ) : ℝ) ≤ Real.log (973 : ℕ)
      ∧ Real.log (973 : ℕ) ≤ ((68803841/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_974 :
    ((68814113/10000000 : ℚ) : ℝ) ≤ Real.log (974 : ℕ)
      ∧ Real.log (974 : ℕ) ≤ ((34407057/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_975 :
    ((34412187/5000000 : ℚ) : ℝ) ≤ Real.log (975 : ℕ)
      ∧ Real.log (975 : ℕ) ≤ ((110119/16000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_976 :
    ((550677/80000 : ℚ) : ℝ) ≤ Real.log (976 : ℕ)
      ∧ Real.log (976 : ℕ) ≤ ((34417313/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_977 :
    ((34422433/5000000 : ℚ) : ℝ) ≤ Real.log (977 : ℕ)
      ∧ Real.log (977 : ℕ) ≤ ((68844867/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_978 :
    ((8606887/1250000 : ℚ) : ℝ) ≤ Real.log (978 : ℕ)
      ∧ Real.log (978 : ℕ) ≤ ((68855097/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_979 :
    ((17216329/2500000 : ℚ) : ℝ) ≤ Real.log (979 : ℕ)
      ∧ Real.log (979 : ℕ) ≤ ((68865317/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_980 :
    ((2755021/400000 : ℚ) : ℝ) ≤ Real.log (980 : ℕ)
      ∧ Real.log (980 : ℕ) ≤ ((34437763/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_981 :
    ((17221431/2500000 : ℚ) : ℝ) ≤ Real.log (981 : ℕ)
      ∧ Real.log (981 : ℕ) ≤ ((2755429/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_982 :
    ((68895913/10000000 : ℚ) : ℝ) ≤ Real.log (982 : ℕ)
      ∧ Real.log (982 : ℕ) ≤ ((34447957/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_983 :
    ((68906091/10000000 : ℚ) : ℝ) ≤ Real.log (983 : ℕ)
      ∧ Real.log (983 : ℕ) ≤ ((17226523/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_984 :
    ((34458129/5000000 : ℚ) : ℝ) ≤ Real.log (984 : ℕ)
      ∧ Real.log (984 : ℕ) ≤ ((68916259/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_985 :
    ((4307901/625000 : ℚ) : ℝ) ≤ Real.log (985 : ℕ)
      ∧ Real.log (985 : ℕ) ≤ ((68926417/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_986 :
    ((68936563/10000000 : ℚ) : ℝ) ≤ Real.log (986 : ℕ)
      ∧ Real.log (986 : ℕ) ≤ ((17234141/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_987 :
    ((689467/100000 : ℚ) : ℝ) ≤ Real.log (987 : ℕ)
      ∧ Real.log (987 : ℕ) ≤ ((68946701/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_988 :
    ((34478413/5000000 : ℚ) : ℝ) ≤ Real.log (988 : ℕ)
      ∧ Real.log (988 : ℕ) ≤ ((68956827/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_989 :
    ((68966943/10000000 : ℚ) : ℝ) ≤ Real.log (989 : ℕ)
      ∧ Real.log (989 : ℕ) ≤ ((2155217/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_990 :
    ((68977049/10000000 : ℚ) : ℝ) ≤ Real.log (990 : ℕ)
      ∧ Real.log (990 : ℕ) ≤ ((1379541/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_991 :
    ((13797429/2000000 : ℚ) : ℝ) ≤ Real.log (991 : ℕ)
      ∧ Real.log (991 : ℕ) ≤ ((34493573/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_992 :
    ((68997231/10000000 : ℚ) : ℝ) ≤ Real.log (992 : ℕ)
      ∧ Real.log (992 : ℕ) ≤ ((4312327/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_993 :
    ((34503653/5000000 : ℚ) : ℝ) ≤ Real.log (993 : ℕ)
      ∧ Real.log (993 : ℕ) ≤ ((69007307/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_994 :
    ((17254343/2500000 : ℚ) : ℝ) ≤ Real.log (994 : ℕ)
      ∧ Real.log (994 : ℕ) ≤ ((69017373/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_995 :
    ((69027427/10000000 : ℚ) : ℝ) ≤ Real.log (995 : ℕ)
      ∧ Real.log (995 : ℕ) ≤ ((17256857/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_996 :
    ((2157421/312500 : ℚ) : ℝ) ≤ Real.log (996 : ℕ)
      ∧ Real.log (996 : ℕ) ≤ ((69037473/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_997 :
    ((69047507/10000000 : ℚ) : ℝ) ≤ Real.log (997 : ℕ)
      ∧ Real.log (997 : ℕ) ≤ ((17261877/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_998 :
    ((17264383/2500000 : ℚ) : ℝ) ≤ Real.log (998 : ℕ)
      ∧ Real.log (998 : ℕ) ≤ ((69057533/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_999 :
    ((69067547/10000000 : ℚ) : ℝ) ≤ Real.log (999 : ℕ)
      ∧ Real.log (999 : ℕ) ≤ ((17266887/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1000 :
    ((4317347/625000 : ℚ) : ℝ) ≤ Real.log (1000 : ℕ)
      ∧ Real.log (1000 : ℕ) ≤ ((69077553/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_br_1000
end AxiomAudit
