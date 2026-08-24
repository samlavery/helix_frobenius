import RequestProject.DVPLogBracket

/-!
# Natural-log brackets 1001-2000 (deep thin-gap station support)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_1001 :
    ((69087547/10000000 : ℚ) : ℝ) ≤ Real.log (1001 : ℕ)
      ∧ Real.log (1001 : ℕ) ≤ ((17271887/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1002 :
    ((17274383/2500000 : ℚ) : ℝ) ≤ Real.log (1002 : ℕ)
      ∧ Real.log (1002 : ℕ) ≤ ((69097533/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1003 :
    ((69107507/10000000 : ℚ) : ℝ) ≤ Real.log (1003 : ℕ)
      ∧ Real.log (1003 : ℕ) ≤ ((17276877/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1004 :
    ((2159921/312500 : ℚ) : ℝ) ≤ Real.log (1004 : ℕ)
      ∧ Real.log (1004 : ℕ) ≤ ((2764699/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1005 :
    ((17281857/2500000 : ℚ) : ℝ) ≤ Real.log (1005 : ℕ)
      ∧ Real.log (1005 : ℕ) ≤ ((69127429/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1006 :
    ((69137373/10000000 : ℚ) : ℝ) ≤ Real.log (1006 : ℕ)
      ∧ Real.log (1006 : ℕ) ≤ ((34568687/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1007 :
    ((17286827/2500000 : ℚ) : ℝ) ≤ Real.log (1007 : ℕ)
      ∧ Real.log (1007 : ℕ) ≤ ((69147309/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1008 :
    ((34578617/5000000 : ℚ) : ℝ) ≤ Real.log (1008 : ℕ)
      ∧ Real.log (1008 : ℕ) ≤ ((13831447/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1009 :
    ((1383343/200000 : ℚ) : ℝ) ≤ Real.log (1009 : ℕ)
      ∧ Real.log (1009 : ℕ) ≤ ((69167151/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1010 :
    ((2161783/312500 : ℚ) : ℝ) ≤ Real.log (1010 : ℕ)
      ∧ Real.log (1010 : ℕ) ≤ ((69177057/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1011 :
    ((8648369/1250000 : ℚ) : ℝ) ≤ Real.log (1011 : ℕ)
      ∧ Real.log (1011 : ℕ) ≤ ((69186953/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1012 :
    ((34598419/5000000 : ℚ) : ℝ) ≤ Real.log (1012 : ℕ)
      ∧ Real.log (1012 : ℕ) ≤ ((69196839/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1013 :
    ((13841343/2000000 : ℚ) : ℝ) ≤ Real.log (1013 : ℕ)
      ∧ Real.log (1013 : ℕ) ≤ ((17301679/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1014 :
    ((69216581/10000000 : ℚ) : ℝ) ≤ Real.log (1014 : ℕ)
      ∧ Real.log (1014 : ℕ) ≤ ((34608291/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1015 :
    ((34613219/5000000 : ℚ) : ℝ) ≤ Real.log (1015 : ℕ)
      ∧ Real.log (1015 : ℕ) ≤ ((69226439/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1016 :
    ((34618143/5000000 : ℚ) : ℝ) ≤ Real.log (1016 : ℕ)
      ∧ Real.log (1016 : ℕ) ≤ ((69236287/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1017 :
    ((69246123/10000000 : ℚ) : ℝ) ≤ Real.log (1017 : ℕ)
      ∧ Real.log (1017 : ℕ) ≤ ((17311531/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1018 :
    ((69255951/10000000 : ℚ) : ℝ) ≤ Real.log (1018 : ℕ)
      ∧ Real.log (1018 : ℕ) ≤ ((4328497/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1019 :
    ((6926577/1000000 : ℚ) : ℝ) ≤ Real.log (1019 : ℕ)
      ∧ Real.log (1019 : ℕ) ≤ ((69265771/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1020 :
    ((69275579/10000000 : ℚ) : ℝ) ≤ Real.log (1020 : ℕ)
      ∧ Real.log (1020 : ℕ) ≤ ((3463779/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1021 :
    ((34642689/5000000 : ℚ) : ℝ) ≤ Real.log (1021 : ℕ)
      ∧ Real.log (1021 : ℕ) ≤ ((69285379/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1022 :
    ((69295167/10000000 : ℚ) : ℝ) ≤ Real.log (1022 : ℕ)
      ∧ Real.log (1022 : ℕ) ≤ ((1082737/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1023 :
    ((69304947/10000000 : ℚ) : ℝ) ≤ Real.log (1023 : ℕ)
      ∧ Real.log (1023 : ℕ) ≤ ((17326237/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1024 :
    ((34657359/5000000 : ℚ) : ℝ) ≤ Real.log (1024 : ℕ)
      ∧ Real.log (1024 : ℕ) ≤ ((69314719/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1025 :
    ((34662239/5000000 : ℚ) : ℝ) ≤ Real.log (1025 : ℕ)
      ∧ Real.log (1025 : ℕ) ≤ ((69324479/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1026 :
    ((6933423/1000000 : ℚ) : ℝ) ≤ Real.log (1026 : ℕ)
      ∧ Real.log (1026 : ℕ) ≤ ((69334231/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1027 :
    ((17335993/2500000 : ℚ) : ℝ) ≤ Real.log (1027 : ℕ)
      ∧ Real.log (1027 : ℕ) ≤ ((69343973/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1028 :
    ((8669213/1250000 : ℚ) : ℝ) ≤ Real.log (1028 : ℕ)
      ∧ Real.log (1028 : ℕ) ≤ ((13870741/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1029 :
    ((69363427/10000000 : ℚ) : ℝ) ≤ Real.log (1029 : ℕ)
      ∧ Real.log (1029 : ℕ) ≤ ((17340857/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1030 :
    ((3468657/500000 : ℚ) : ℝ) ≤ Real.log (1030 : ℕ)
      ∧ Real.log (1030 : ℕ) ≤ ((69373141/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1031 :
    ((17345711/2500000 : ℚ) : ℝ) ≤ Real.log (1031 : ℕ)
      ∧ Real.log (1031 : ℕ) ≤ ((13876569/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1032 :
    ((69392539/10000000 : ℚ) : ℝ) ≤ Real.log (1032 : ℕ)
      ∧ Real.log (1032 : ℕ) ≤ ((3469627/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1033 :
    ((4337639/625000 : ℚ) : ℝ) ≤ Real.log (1033 : ℕ)
      ∧ Real.log (1033 : ℕ) ≤ ((2776089/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1034 :
    ((694119/100000 : ℚ) : ℝ) ≤ Real.log (1034 : ℕ)
      ∧ Real.log (1034 : ℕ) ≤ ((69411901/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1035 :
    ((69421567/10000000 : ℚ) : ℝ) ≤ Real.log (1035 : ℕ)
      ∧ Real.log (1035 : ℕ) ≤ ((542356/78125 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1036 :
    ((8678903/1250000 : ℚ) : ℝ) ≤ Real.log (1036 : ℕ)
      ∧ Real.log (1036 : ℕ) ≤ ((2777249/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1037 :
    ((8680109/1250000 : ℚ) : ℝ) ≤ Real.log (1037 : ℕ)
      ∧ Real.log (1037 : ℕ) ≤ ((69440873/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1038 :
    ((6945051/1000000 : ℚ) : ℝ) ≤ Real.log (1038 : ℕ)
      ∧ Real.log (1038 : ℕ) ≤ ((69450511/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1039 :
    ((69460139/10000000 : ℚ) : ℝ) ≤ Real.log (1039 : ℕ)
      ∧ Real.log (1039 : ℕ) ≤ ((3473007/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1040 :
    ((69469759/10000000 : ℚ) : ℝ) ≤ Real.log (1040 : ℕ)
      ∧ Real.log (1040 : ℕ) ≤ ((217093/31250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1041 :
    ((6947937/1000000 : ℚ) : ℝ) ≤ Real.log (1041 : ℕ)
      ∧ Real.log (1041 : ℕ) ≤ ((69479371/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1042 :
    ((17372243/2500000 : ℚ) : ℝ) ≤ Real.log (1042 : ℕ)
      ∧ Real.log (1042 : ℕ) ≤ ((69488973/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1043 :
    ((17374641/2500000 : ℚ) : ℝ) ≤ Real.log (1043 : ℕ)
      ∧ Real.log (1043 : ℕ) ≤ ((13899713/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1044 :
    ((69508147/10000000 : ℚ) : ℝ) ≤ Real.log (1044 : ℕ)
      ∧ Real.log (1044 : ℕ) ≤ ((17377037/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1045 :
    ((69517721/10000000 : ℚ) : ℝ) ≤ Real.log (1045 : ℕ)
      ∧ Real.log (1045 : ℕ) ≤ ((34758861/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1046 :
    ((34763643/5000000 : ℚ) : ℝ) ≤ Real.log (1046 : ℕ)
      ∧ Real.log (1046 : ℕ) ≤ ((69527287/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1047 :
    ((34768421/5000000 : ℚ) : ℝ) ≤ Real.log (1047 : ℕ)
      ∧ Real.log (1047 : ℕ) ≤ ((69536843/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1048 :
    ((17386597/2500000 : ℚ) : ℝ) ≤ Real.log (1048 : ℕ)
      ∧ Real.log (1048 : ℕ) ≤ ((69546389/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1049 :
    ((34777963/5000000 : ℚ) : ℝ) ≤ Real.log (1049 : ℕ)
      ∧ Real.log (1049 : ℕ) ≤ ((69555927/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1050 :
    ((34782727/5000000 : ℚ) : ℝ) ≤ Real.log (1050 : ℕ)
      ∧ Real.log (1050 : ℕ) ≤ ((13913091/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1051 :
    ((69574973/10000000 : ℚ) : ℝ) ≤ Real.log (1051 : ℕ)
      ∧ Real.log (1051 : ℕ) ≤ ((34787487/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1052 :
    ((69584483/10000000 : ℚ) : ℝ) ≤ Real.log (1052 : ℕ)
      ∧ Real.log (1052 : ℕ) ≤ ((17396121/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1053 :
    ((13918797/2000000 : ℚ) : ℝ) ≤ Real.log (1053 : ℕ)
      ∧ Real.log (1053 : ℕ) ≤ ((34796993/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1054 :
    ((69603477/10000000 : ℚ) : ℝ) ≤ Real.log (1054 : ℕ)
      ∧ Real.log (1054 : ℕ) ≤ ((34801739/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1055 :
    ((435081/62500 : ℚ) : ℝ) ≤ Real.log (1055 : ℕ)
      ∧ Real.log (1055 : ℕ) ≤ ((69612961/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1056 :
    ((34811217/5000000 : ℚ) : ℝ) ≤ Real.log (1056 : ℕ)
      ∧ Real.log (1056 : ℕ) ≤ ((13924487/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1057 :
    ((69631899/10000000 : ℚ) : ℝ) ≤ Real.log (1057 : ℕ)
      ∧ Real.log (1057 : ℕ) ≤ ((696319/100000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1058 :
    ((17410339/2500000 : ℚ) : ℝ) ≤ Real.log (1058 : ℕ)
      ∧ Real.log (1058 : ℕ) ≤ ((69641357/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1059 :
    ((69650803/10000000 : ℚ) : ℝ) ≤ Real.log (1059 : ℕ)
      ∧ Real.log (1059 : ℕ) ≤ ((17412701/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1060 :
    ((69660241/10000000 : ℚ) : ℝ) ≤ Real.log (1060 : ℕ)
      ∧ Real.log (1060 : ℕ) ≤ ((34830121/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1061 :
    ((69669671/10000000 : ℚ) : ℝ) ≤ Real.log (1061 : ℕ)
      ∧ Real.log (1061 : ℕ) ≤ ((8708709/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1062 :
    ((17419773/2500000 : ℚ) : ℝ) ≤ Real.log (1062 : ℕ)
      ∧ Real.log (1062 : ℕ) ≤ ((69679093/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1063 :
    ((69688503/10000000 : ℚ) : ℝ) ≤ Real.log (1063 : ℕ)
      ∧ Real.log (1063 : ℕ) ≤ ((8711063/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1064 :
    ((34848953/5000000 : ℚ) : ℝ) ≤ Real.log (1064 : ℕ)
      ∧ Real.log (1064 : ℕ) ≤ ((69697907/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1065 :
    ((697073/100000 : ℚ) : ℝ) ≤ Real.log (1065 : ℕ)
      ∧ Real.log (1065 : ℕ) ≤ ((69707301/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1066 :
    ((34858343/5000000 : ℚ) : ℝ) ≤ Real.log (1066 : ℕ)
      ∧ Real.log (1066 : ℕ) ≤ ((69716687/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1067 :
    ((34863031/5000000 : ℚ) : ℝ) ≤ Real.log (1067 : ℕ)
      ∧ Real.log (1067 : ℕ) ≤ ((69726063/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1068 :
    ((6973543/1000000 : ℚ) : ℝ) ≤ Real.log (1068 : ℕ)
      ∧ Real.log (1068 : ℕ) ≤ ((69735431/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1069 :
    ((69744789/10000000 : ℚ) : ℝ) ≤ Real.log (1069 : ℕ)
      ∧ Real.log (1069 : ℕ) ≤ ((6974479/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1070 :
    ((69754139/10000000 : ℚ) : ℝ) ≤ Real.log (1070 : ℕ)
      ∧ Real.log (1070 : ℕ) ≤ ((3487707/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1071 :
    ((1744087/250000 : ℚ) : ℝ) ≤ Real.log (1071 : ℕ)
      ∧ Real.log (1071 : ℕ) ≤ ((69763481/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1072 :
    ((69772813/10000000 : ℚ) : ℝ) ≤ Real.log (1072 : ℕ)
      ∧ Real.log (1072 : ℕ) ≤ ((34886407/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1073 :
    ((69782137/10000000 : ℚ) : ℝ) ≤ Real.log (1073 : ℕ)
      ∧ Real.log (1073 : ℕ) ≤ ((34891069/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1074 :
    ((17447863/2500000 : ℚ) : ℝ) ≤ Real.log (1074 : ℕ)
      ∧ Real.log (1074 : ℕ) ≤ ((69791453/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1075 :
    ((69800759/10000000 : ℚ) : ℝ) ≤ Real.log (1075 : ℕ)
      ∧ Real.log (1075 : ℕ) ≤ ((1745019/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1076 :
    ((69810057/10000000 : ℚ) : ℝ) ≤ Real.log (1076 : ℕ)
      ∧ Real.log (1076 : ℕ) ≤ ((34905029/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1077 :
    ((34909673/5000000 : ℚ) : ℝ) ≤ Real.log (1077 : ℕ)
      ∧ Real.log (1077 : ℕ) ≤ ((69819347/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1078 :
    ((69828627/10000000 : ℚ) : ℝ) ≤ Real.log (1078 : ℕ)
      ∧ Real.log (1078 : ℕ) ≤ ((17457157/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1079 :
    ((69837899/10000000 : ℚ) : ℝ) ≤ Real.log (1079 : ℕ)
      ∧ Real.log (1079 : ℕ) ≤ ((698379/100000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1080 :
    ((69847163/10000000 : ℚ) : ℝ) ≤ Real.log (1080 : ℕ)
      ∧ Real.log (1080 : ℕ) ≤ ((17461791/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1081 :
    ((34928209/5000000 : ℚ) : ℝ) ≤ Real.log (1081 : ℕ)
      ∧ Real.log (1081 : ℕ) ≤ ((69856419/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1082 :
    ((1091651/156250 : ℚ) : ℝ) ≤ Real.log (1082 : ℕ)
      ∧ Real.log (1082 : ℕ) ≤ ((13973133/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1083 :
    ((34937451/5000000 : ℚ) : ℝ) ≤ Real.log (1083 : ℕ)
      ∧ Real.log (1083 : ℕ) ≤ ((69874903/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1084 :
    ((69884131/10000000 : ℚ) : ℝ) ≤ Real.log (1084 : ℕ)
      ∧ Real.log (1084 : ℕ) ≤ ((17471033/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1085 :
    ((8736669/1250000 : ℚ) : ℝ) ≤ Real.log (1085 : ℕ)
      ∧ Real.log (1085 : ℕ) ≤ ((69893353/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1086 :
    ((13980513/2000000 : ℚ) : ℝ) ≤ Real.log (1086 : ℕ)
      ∧ Real.log (1086 : ℕ) ≤ ((34951283/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1087 :
    ((8738971/1250000 : ℚ) : ℝ) ≤ Real.log (1087 : ℕ)
      ∧ Real.log (1087 : ℕ) ≤ ((69911769/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1088 :
    ((17480241/2500000 : ℚ) : ℝ) ≤ Real.log (1088 : ℕ)
      ∧ Real.log (1088 : ℕ) ≤ ((13984193/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1089 :
    ((69930151/10000000 : ℚ) : ℝ) ≤ Real.log (1089 : ℕ)
      ∧ Real.log (1089 : ℕ) ≤ ((8741269/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1090 :
    ((69939329/10000000 : ℚ) : ℝ) ≤ Real.log (1090 : ℕ)
      ∧ Real.log (1090 : ℕ) ≤ ((6993933/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1091 :
    ((69948499/10000000 : ℚ) : ℝ) ≤ Real.log (1091 : ℕ)
      ∧ Real.log (1091 : ℕ) ≤ ((139897/20000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1092 :
    ((69957661/10000000 : ℚ) : ℝ) ≤ Real.log (1092 : ℕ)
      ∧ Real.log (1092 : ℕ) ≤ ((34978831/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1093 :
    ((34983407/5000000 : ℚ) : ℝ) ≤ Real.log (1093 : ℕ)
      ∧ Real.log (1093 : ℕ) ≤ ((13993363/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1094 :
    ((69975959/10000000 : ℚ) : ℝ) ≤ Real.log (1094 : ℕ)
      ∧ Real.log (1094 : ℕ) ≤ ((1749399/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1095 :
    ((8748137/1250000 : ℚ) : ℝ) ≤ Real.log (1095 : ℕ)
      ∧ Real.log (1095 : ℕ) ≤ ((69985097/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1096 :
    ((4374639/625000 : ℚ) : ℝ) ≤ Real.log (1096 : ℕ)
      ∧ Real.log (1096 : ℕ) ≤ ((2799769/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1097 :
    ((4375209/625000 : ℚ) : ℝ) ≤ Real.log (1097 : ℕ)
      ∧ Real.log (1097 : ℕ) ≤ ((14000669/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1098 :
    ((8751557/1250000 : ℚ) : ℝ) ≤ Real.log (1098 : ℕ)
      ∧ Real.log (1098 : ℕ) ≤ ((70012457/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1099 :
    ((70021559/10000000 : ℚ) : ℝ) ≤ Real.log (1099 : ℕ)
      ∧ Real.log (1099 : ℕ) ≤ ((1750539/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1100 :
    ((35015327/5000000 : ℚ) : ℝ) ≤ Real.log (1100 : ℕ)
      ∧ Real.log (1100 : ℕ) ≤ ((14006131/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1101 :
    ((70039741/10000000 : ℚ) : ℝ) ≤ Real.log (1101 : ℕ)
      ∧ Real.log (1101 : ℕ) ≤ ((35019871/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1102 :
    ((70048819/10000000 : ℚ) : ℝ) ≤ Real.log (1102 : ℕ)
      ∧ Real.log (1102 : ℕ) ≤ ((3502441/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1103 :
    ((7005789/1000000 : ℚ) : ℝ) ≤ Real.log (1103 : ℕ)
      ∧ Real.log (1103 : ℕ) ≤ ((70057891/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1104 :
    ((8758369/1250000 : ℚ) : ℝ) ≤ Real.log (1104 : ℕ)
      ∧ Real.log (1104 : ℕ) ≤ ((70066953/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1105 :
    ((35038003/5000000 : ℚ) : ℝ) ≤ Real.log (1105 : ℕ)
      ∧ Real.log (1105 : ℕ) ≤ ((70076007/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1106 :
    ((70085051/10000000 : ℚ) : ℝ) ≤ Real.log (1106 : ℕ)
      ∧ Real.log (1106 : ℕ) ≤ ((17521263/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1107 :
    ((70094089/10000000 : ℚ) : ℝ) ≤ Real.log (1107 : ℕ)
      ∧ Real.log (1107 : ℕ) ≤ ((7009409/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1108 :
    ((35051559/5000000 : ℚ) : ℝ) ≤ Real.log (1108 : ℕ)
      ∧ Real.log (1108 : ℕ) ≤ ((70103119/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1109 :
    ((70112139/10000000 : ℚ) : ℝ) ≤ Real.log (1109 : ℕ)
      ∧ Real.log (1109 : ℕ) ≤ ((3505607/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1110 :
    ((1095643/156250 : ℚ) : ℝ) ≤ Real.log (1110 : ℕ)
      ∧ Real.log (1110 : ℕ) ≤ ((70121153/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1111 :
    ((70130157/10000000 : ℚ) : ℝ) ≤ Real.log (1111 : ℕ)
      ∧ Real.log (1111 : ℕ) ≤ ((35065079/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1112 :
    ((35069577/5000000 : ℚ) : ℝ) ≤ Real.log (1112 : ℕ)
      ∧ Real.log (1112 : ℕ) ≤ ((14027831/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1113 :
    ((70148143/10000000 : ℚ) : ℝ) ≤ Real.log (1113 : ℕ)
      ∧ Real.log (1113 : ℕ) ≤ ((4384259/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1114 :
    ((17539281/2500000 : ℚ) : ℝ) ≤ Real.log (1114 : ℕ)
      ∧ Real.log (1114 : ℕ) ≤ ((561257/80000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1115 :
    ((4385381/625000 : ℚ) : ℝ) ≤ Real.log (1115 : ℕ)
      ∧ Real.log (1115 : ℕ) ≤ ((70166097/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1116 :
    ((70175061/10000000 : ℚ) : ℝ) ≤ Real.log (1116 : ℕ)
      ∧ Real.log (1116 : ℕ) ≤ ((35087531/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1117 :
    ((70184017/10000000 : ℚ) : ℝ) ≤ Real.log (1117 : ℕ)
      ∧ Real.log (1117 : ℕ) ≤ ((35092009/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1118 :
    ((35096483/5000000 : ℚ) : ℝ) ≤ Real.log (1118 : ℕ)
      ∧ Real.log (1118 : ℕ) ≤ ((70192967/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1119 :
    ((70201907/10000000 : ℚ) : ℝ) ≤ Real.log (1119 : ℕ)
      ∧ Real.log (1119 : ℕ) ≤ ((17550477/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1120 :
    ((70210839/10000000 : ℚ) : ℝ) ≤ Real.log (1120 : ℕ)
      ∧ Real.log (1120 : ℕ) ≤ ((1755271/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1121 :
    ((17554941/2500000 : ℚ) : ℝ) ≤ Real.log (1121 : ℕ)
      ∧ Real.log (1121 : ℕ) ≤ ((14043953/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1122 :
    ((1755717/250000 : ℚ) : ℝ) ≤ Real.log (1122 : ℕ)
      ∧ Real.log (1122 : ℕ) ≤ ((70228681/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1123 :
    ((70237589/10000000 : ℚ) : ℝ) ≤ Real.log (1123 : ℕ)
      ∧ Real.log (1123 : ℕ) ≤ ((7023759/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1124 :
    ((7024649/1000000 : ℚ) : ℝ) ≤ Real.log (1124 : ℕ)
      ∧ Real.log (1124 : ℕ) ≤ ((70246491/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1125 :
    ((70255383/10000000 : ℚ) : ℝ) ≤ Real.log (1125 : ℕ)
      ∧ Real.log (1125 : ℕ) ≤ ((8781923/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1126 :
    ((17566067/2500000 : ℚ) : ℝ) ≤ Real.log (1126 : ℕ)
      ∧ Real.log (1126 : ℕ) ≤ ((70264269/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1127 :
    ((14054629/2000000 : ℚ) : ℝ) ≤ Real.log (1127 : ℕ)
      ∧ Real.log (1127 : ℕ) ≤ ((35136573/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1128 :
    ((35141007/5000000 : ℚ) : ℝ) ≤ Real.log (1128 : ℕ)
      ∧ Real.log (1128 : ℕ) ≤ ((14056403/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1129 :
    ((562327/80000 : ℚ) : ℝ) ≤ Real.log (1129 : ℕ)
      ∧ Real.log (1129 : ℕ) ≤ ((17572719/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1130 :
    ((70299729/10000000 : ℚ) : ℝ) ≤ Real.log (1130 : ℕ)
      ∧ Real.log (1130 : ℕ) ≤ ((7029973/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1131 :
    ((35154287/5000000 : ℚ) : ℝ) ≤ Real.log (1131 : ℕ)
      ∧ Real.log (1131 : ℕ) ≤ ((2812343/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1132 :
    ((17579353/2500000 : ℚ) : ℝ) ≤ Real.log (1132 : ℕ)
      ∧ Real.log (1132 : ℕ) ≤ ((70317413/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1133 :
    ((35163121/5000000 : ℚ) : ℝ) ≤ Real.log (1133 : ℕ)
      ∧ Real.log (1133 : ℕ) ≤ ((70326243/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1134 :
    ((8791883/1250000 : ℚ) : ℝ) ≤ Real.log (1134 : ℕ)
      ∧ Real.log (1134 : ℕ) ≤ ((14067013/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1135 :
    ((70343879/10000000 : ℚ) : ℝ) ≤ Real.log (1135 : ℕ)
      ∧ Real.log (1135 : ℕ) ≤ ((1758597/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1136 :
    ((14070537/2000000 : ℚ) : ℝ) ≤ Real.log (1136 : ℕ)
      ∧ Real.log (1136 : ℕ) ≤ ((35176343/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1137 :
    ((17590371/2500000 : ℚ) : ℝ) ≤ Real.log (1137 : ℕ)
      ∧ Real.log (1137 : ℕ) ≤ ((14072297/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1138 :
    ((17592569/2500000 : ℚ) : ℝ) ≤ Real.log (1138 : ℕ)
      ∧ Real.log (1138 : ℕ) ≤ ((70370277/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1139 :
    ((70379059/10000000 : ℚ) : ℝ) ≤ Real.log (1139 : ℕ)
      ∧ Real.log (1139 : ℕ) ≤ ((3518953/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1140 :
    ((14077567/2000000 : ℚ) : ℝ) ≤ Real.log (1140 : ℕ)
      ∧ Real.log (1140 : ℕ) ≤ ((17596959/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1141 :
    ((70396603/10000000 : ℚ) : ℝ) ≤ Real.log (1141 : ℕ)
      ∧ Real.log (1141 : ℕ) ≤ ((17599151/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1142 :
    ((70405363/10000000 : ℚ) : ℝ) ≤ Real.log (1142 : ℕ)
      ∧ Real.log (1142 : ℕ) ≤ ((17601341/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1143 :
    ((17603529/2500000 : ℚ) : ℝ) ≤ Real.log (1143 : ℕ)
      ∧ Real.log (1143 : ℕ) ≤ ((70414117/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1144 :
    ((70422861/10000000 : ℚ) : ℝ) ≤ Real.log (1144 : ℕ)
      ∧ Real.log (1144 : ℕ) ≤ ((35211431/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1145 :
    ((70431599/10000000 : ℚ) : ℝ) ≤ Real.log (1145 : ℕ)
      ∧ Real.log (1145 : ℕ) ≤ ((176079/25000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1146 :
    ((8805041/1250000 : ℚ) : ℝ) ≤ Real.log (1146 : ℕ)
      ∧ Real.log (1146 : ℕ) ≤ ((70440329/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1147 :
    ((70449051/10000000 : ℚ) : ℝ) ≤ Real.log (1147 : ℕ)
      ∧ Real.log (1147 : ℕ) ≤ ((17612263/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1148 :
    ((14091553/2000000 : ℚ) : ℝ) ≤ Real.log (1148 : ℕ)
      ∧ Real.log (1148 : ℕ) ≤ ((35228883/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1149 :
    ((8808309/1250000 : ℚ) : ℝ) ≤ Real.log (1149 : ℕ)
      ∧ Real.log (1149 : ℕ) ≤ ((70466473/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1150 :
    ((17618793/2500000 : ℚ) : ℝ) ≤ Real.log (1150 : ℕ)
      ∧ Real.log (1150 : ℕ) ≤ ((70475173/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1151 :
    ((8810483/1250000 : ℚ) : ℝ) ≤ Real.log (1151 : ℕ)
      ∧ Real.log (1151 : ℕ) ≤ ((14096773/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1152 :
    ((17623137/2500000 : ℚ) : ℝ) ≤ Real.log (1152 : ℕ)
      ∧ Real.log (1152 : ℕ) ≤ ((70492549/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1153 :
    ((2820049/400000 : ℚ) : ℝ) ≤ Real.log (1153 : ℕ)
      ∧ Real.log (1153 : ℕ) ≤ ((35250613/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1154 :
    ((35254947/5000000 : ℚ) : ℝ) ≤ Real.log (1154 : ℕ)
      ∧ Real.log (1154 : ℕ) ≤ ((14101979/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1155 :
    ((17629639/2500000 : ℚ) : ℝ) ≤ Real.log (1155 : ℕ)
      ∧ Real.log (1155 : ℕ) ≤ ((70518557/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1156 :
    ((7052721/1000000 : ℚ) : ℝ) ≤ Real.log (1156 : ℕ)
      ∧ Real.log (1156 : ℕ) ≤ ((70527211/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1157 :
    ((70535857/10000000 : ℚ) : ℝ) ≤ Real.log (1157 : ℕ)
      ∧ Real.log (1157 : ℕ) ≤ ((35267929/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1158 :
    ((4409031/625000 : ℚ) : ℝ) ≤ Real.log (1158 : ℕ)
      ∧ Real.log (1158 : ℕ) ≤ ((70544497/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1159 :
    ((8819141/1250000 : ℚ) : ℝ) ≤ Real.log (1159 : ℕ)
      ∧ Real.log (1159 : ℕ) ≤ ((70553129/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1160 :
    ((8820219/1250000 : ℚ) : ℝ) ≤ Real.log (1160 : ℕ)
      ∧ Real.log (1160 : ℕ) ≤ ((70561753/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1161 :
    ((70570369/10000000 : ℚ) : ℝ) ≤ Real.log (1161 : ℕ)
      ∧ Real.log (1161 : ℕ) ≤ ((7057037/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1162 :
    ((70578979/10000000 : ℚ) : ℝ) ≤ Real.log (1162 : ℕ)
      ∧ Real.log (1162 : ℕ) ≤ ((3528949/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1163 :
    ((70587581/10000000 : ℚ) : ℝ) ≤ Real.log (1163 : ℕ)
      ∧ Real.log (1163 : ℕ) ≤ ((35293791/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1164 :
    ((4412261/625000 : ℚ) : ℝ) ≤ Real.log (1164 : ℕ)
      ∧ Real.log (1164 : ℕ) ≤ ((70596177/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1165 :
    ((70604763/10000000 : ℚ) : ℝ) ≤ Real.log (1165 : ℕ)
      ∧ Real.log (1165 : ℕ) ≤ ((17651191/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1166 :
    ((70613343/10000000 : ℚ) : ℝ) ≤ Real.log (1166 : ℕ)
      ∧ Real.log (1166 : ℕ) ≤ ((2206667/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1167 :
    ((17655479/2500000 : ℚ) : ℝ) ≤ Real.log (1167 : ℕ)
      ∧ Real.log (1167 : ℕ) ≤ ((70621917/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1168 :
    ((70630481/10000000 : ℚ) : ℝ) ≤ Real.log (1168 : ℕ)
      ∧ Real.log (1168 : ℕ) ≤ ((35315241/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1169 :
    ((70639039/10000000 : ℚ) : ℝ) ≤ Real.log (1169 : ℕ)
      ∧ Real.log (1169 : ℕ) ≤ ((220747/31250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1170 :
    ((7064759/1000000 : ℚ) : ℝ) ≤ Real.log (1170 : ℕ)
      ∧ Real.log (1170 : ℕ) ≤ ((70647591/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1171 :
    ((70656133/10000000 : ℚ) : ℝ) ≤ Real.log (1171 : ℕ)
      ∧ Real.log (1171 : ℕ) ≤ ((35328067/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1172 :
    ((70664669/10000000 : ℚ) : ℝ) ≤ Real.log (1172 : ℕ)
      ∧ Real.log (1172 : ℕ) ≤ ((7066467/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1173 :
    ((35336599/5000000 : ℚ) : ℝ) ≤ Real.log (1173 : ℕ)
      ∧ Real.log (1173 : ℕ) ≤ ((70673199/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1174 :
    ((1767043/250000 : ℚ) : ℝ) ≤ Real.log (1174 : ℕ)
      ∧ Real.log (1174 : ℕ) ≤ ((70681721/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1175 :
    ((35345117/5000000 : ℚ) : ℝ) ≤ Real.log (1175 : ℕ)
      ∧ Real.log (1175 : ℕ) ≤ ((14138047/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1176 :
    ((70698741/10000000 : ℚ) : ℝ) ≤ Real.log (1176 : ℕ)
      ∧ Real.log (1176 : ℕ) ≤ ((35349371/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1177 :
    ((70707241/10000000 : ℚ) : ℝ) ≤ Real.log (1177 : ℕ)
      ∧ Real.log (1177 : ℕ) ≤ ((35353621/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1178 :
    ((70715733/10000000 : ℚ) : ℝ) ≤ Real.log (1178 : ℕ)
      ∧ Real.log (1178 : ℕ) ≤ ((35357867/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1179 :
    ((70724219/10000000 : ℚ) : ℝ) ≤ Real.log (1179 : ℕ)
      ∧ Real.log (1179 : ℕ) ≤ ((3536211/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1180 :
    ((70732697/10000000 : ℚ) : ℝ) ≤ Real.log (1180 : ℕ)
      ∧ Real.log (1180 : ℕ) ≤ ((35366349/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1181 :
    ((4421323/625000 : ℚ) : ℝ) ≤ Real.log (1181 : ℕ)
      ∧ Real.log (1181 : ℕ) ≤ ((70741169/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1182 :
    ((70749631/10000000 : ℚ) : ℝ) ≤ Real.log (1182 : ℕ)
      ∧ Real.log (1182 : ℕ) ≤ ((1105463/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1183 :
    ((8844761/1250000 : ℚ) : ℝ) ≤ Real.log (1183 : ℕ)
      ∧ Real.log (1183 : ℕ) ≤ ((70758089/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1184 :
    ((35383269/5000000 : ℚ) : ℝ) ≤ Real.log (1184 : ℕ)
      ∧ Real.log (1184 : ℕ) ≤ ((70766539/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1185 :
    ((3538749/500000 : ℚ) : ℝ) ≤ Real.log (1185 : ℕ)
      ∧ Real.log (1185 : ℕ) ≤ ((70774981/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1186 :
    ((14156683/2000000 : ℚ) : ℝ) ≤ Real.log (1186 : ℕ)
      ∧ Real.log (1186 : ℕ) ≤ ((8847927/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1187 :
    ((70791843/10000000 : ℚ) : ℝ) ≤ Real.log (1187 : ℕ)
      ∧ Real.log (1187 : ℕ) ≤ ((17697961/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1188 :
    ((70800263/10000000 : ℚ) : ℝ) ≤ Real.log (1188 : ℕ)
      ∧ Real.log (1188 : ℕ) ≤ ((35400133/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1189 :
    ((35404339/5000000 : ℚ) : ℝ) ≤ Real.log (1189 : ℕ)
      ∧ Real.log (1189 : ℕ) ≤ ((70808679/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1190 :
    ((14163417/2000000 : ℚ) : ℝ) ≤ Real.log (1190 : ℕ)
      ∧ Real.log (1190 : ℕ) ≤ ((35408543/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1191 :
    ((14165097/2000000 : ℚ) : ℝ) ≤ Real.log (1191 : ℕ)
      ∧ Real.log (1191 : ℕ) ≤ ((35412743/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1192 :
    ((35416939/5000000 : ℚ) : ℝ) ≤ Real.log (1192 : ℕ)
      ∧ Real.log (1192 : ℕ) ≤ ((70833879/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1193 :
    ((8855283/1250000 : ℚ) : ℝ) ≤ Real.log (1193 : ℕ)
      ∧ Real.log (1193 : ℕ) ≤ ((14168453/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1194 :
    ((35425321/5000000 : ℚ) : ℝ) ≤ Real.log (1194 : ℕ)
      ∧ Real.log (1194 : ℕ) ≤ ((70850643/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1195 :
    ((35429507/5000000 : ℚ) : ℝ) ≤ Real.log (1195 : ℕ)
      ∧ Real.log (1195 : ℕ) ≤ ((14171803/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1196 :
    ((70867379/10000000 : ℚ) : ℝ) ≤ Real.log (1196 : ℕ)
      ∧ Real.log (1196 : ℕ) ≤ ((3543369/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1197 :
    ((70875737/10000000 : ℚ) : ℝ) ≤ Real.log (1197 : ℕ)
      ∧ Real.log (1197 : ℕ) ≤ ((35437869/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1198 :
    ((70884087/10000000 : ℚ) : ℝ) ≤ Real.log (1198 : ℕ)
      ∧ Real.log (1198 : ℕ) ≤ ((8860511/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1199 :
    ((70892431/10000000 : ℚ) : ℝ) ≤ Real.log (1199 : ℕ)
      ∧ Real.log (1199 : ℕ) ≤ ((4430777/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1200 :
    ((2215649/312500 : ℚ) : ℝ) ≤ Real.log (1200 : ℕ)
      ∧ Real.log (1200 : ℕ) ≤ ((70900769/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1201 :
    ((35454549/5000000 : ℚ) : ℝ) ≤ Real.log (1201 : ℕ)
      ∧ Real.log (1201 : ℕ) ≤ ((70909099/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1202 :
    ((70917421/10000000 : ℚ) : ℝ) ≤ Real.log (1202 : ℕ)
      ∧ Real.log (1202 : ℕ) ≤ ((35458711/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1203 :
    ((70925737/10000000 : ℚ) : ℝ) ≤ Real.log (1203 : ℕ)
      ∧ Real.log (1203 : ℕ) ≤ ((35462869/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1204 :
    ((35467023/5000000 : ℚ) : ℝ) ≤ Real.log (1204 : ℕ)
      ∧ Real.log (1204 : ℕ) ≤ ((70934047/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1205 :
    ((17735587/2500000 : ℚ) : ℝ) ≤ Real.log (1205 : ℕ)
      ∧ Real.log (1205 : ℕ) ≤ ((70942349/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1206 :
    ((70950643/10000000 : ℚ) : ℝ) ≤ Real.log (1206 : ℕ)
      ∧ Real.log (1206 : ℕ) ≤ ((17737661/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1207 :
    ((17739733/2500000 : ℚ) : ℝ) ≤ Real.log (1207 : ℕ)
      ∧ Real.log (1207 : ℕ) ≤ ((70958933/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1208 :
    ((70967213/10000000 : ℚ) : ℝ) ≤ Real.log (1208 : ℕ)
      ∧ Real.log (1208 : ℕ) ≤ ((35483607/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1209 :
    ((554496/78125 : ℚ) : ℝ) ≤ Real.log (1209 : ℕ)
      ∧ Real.log (1209 : ℕ) ≤ ((70975489/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1210 :
    ((17745939/2500000 : ℚ) : ℝ) ≤ Real.log (1210 : ℕ)
      ∧ Real.log (1210 : ℕ) ≤ ((70983757/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1211 :
    ((70992017/10000000 : ℚ) : ℝ) ≤ Real.log (1211 : ℕ)
      ∧ Real.log (1211 : ℕ) ≤ ((35496009/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1212 :
    ((71000271/10000000 : ℚ) : ℝ) ≤ Real.log (1212 : ℕ)
      ∧ Real.log (1212 : ℕ) ≤ ((4437517/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1213 :
    ((71008519/10000000 : ℚ) : ℝ) ≤ Real.log (1213 : ℕ)
      ∧ Real.log (1213 : ℕ) ≤ ((1775213/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1214 :
    ((71016759/10000000 : ℚ) : ℝ) ≤ Real.log (1214 : ℕ)
      ∧ Real.log (1214 : ℕ) ≤ ((1775419/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1215 :
    ((71024993/10000000 : ℚ) : ℝ) ≤ Real.log (1215 : ℕ)
      ∧ Real.log (1215 : ℕ) ≤ ((35512497/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1216 :
    ((3551661/500000 : ℚ) : ℝ) ≤ Real.log (1216 : ℕ)
      ∧ Real.log (1216 : ℕ) ≤ ((71033221/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1217 :
    ((444009/62500 : ℚ) : ℝ) ≤ Real.log (1217 : ℕ)
      ∧ Real.log (1217 : ℕ) ≤ ((71041441/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1218 :
    ((35524827/5000000 : ℚ) : ℝ) ≤ Real.log (1218 : ℕ)
      ∧ Real.log (1218 : ℕ) ≤ ((14209931/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1219 :
    ((71057861/10000000 : ℚ) : ℝ) ≤ Real.log (1219 : ℕ)
      ∧ Real.log (1219 : ℕ) ≤ ((35528931/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1220 :
    ((71066061/10000000 : ℚ) : ℝ) ≤ Real.log (1220 : ℕ)
      ∧ Real.log (1220 : ℕ) ≤ ((35533031/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1221 :
    ((35537127/5000000 : ℚ) : ℝ) ≤ Real.log (1221 : ℕ)
      ∧ Real.log (1221 : ℕ) ≤ ((14214851/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1222 :
    ((71082441/10000000 : ℚ) : ℝ) ≤ Real.log (1222 : ℕ)
      ∧ Real.log (1222 : ℕ) ≤ ((35541221/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1223 :
    ((71090621/10000000 : ℚ) : ℝ) ≤ Real.log (1223 : ℕ)
      ∧ Real.log (1223 : ℕ) ≤ ((35545311/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1224 :
    ((35549397/5000000 : ℚ) : ℝ) ≤ Real.log (1224 : ℕ)
      ∧ Real.log (1224 : ℕ) ≤ ((14219759/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1225 :
    ((71106961/10000000 : ℚ) : ℝ) ≤ Real.log (1225 : ℕ)
      ∧ Real.log (1225 : ℕ) ≤ ((35553481/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1226 :
    ((71115121/10000000 : ℚ) : ℝ) ≤ Real.log (1226 : ℕ)
      ∧ Real.log (1226 : ℕ) ≤ ((35557561/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1227 :
    ((35561637/5000000 : ℚ) : ℝ) ≤ Real.log (1227 : ℕ)
      ∧ Real.log (1227 : ℕ) ≤ ((2844931/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1228 :
    ((71131421/10000000 : ℚ) : ℝ) ≤ Real.log (1228 : ℕ)
      ∧ Real.log (1228 : ℕ) ≤ ((35565711/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1229 :
    ((71139561/10000000 : ℚ) : ℝ) ≤ Real.log (1229 : ℕ)
      ∧ Real.log (1229 : ℕ) ≤ ((35569781/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1230 :
    ((35573847/5000000 : ℚ) : ℝ) ≤ Real.log (1230 : ℕ)
      ∧ Real.log (1230 : ℕ) ≤ ((14229539/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1231 :
    ((71155821/10000000 : ℚ) : ℝ) ≤ Real.log (1231 : ℕ)
      ∧ Real.log (1231 : ℕ) ≤ ((35577911/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1232 :
    ((71163941/10000000 : ℚ) : ℝ) ≤ Real.log (1232 : ℕ)
      ∧ Real.log (1232 : ℕ) ≤ ((35581971/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1233 :
    ((14234411/2000000 : ℚ) : ℝ) ≤ Real.log (1233 : ℕ)
      ∧ Real.log (1233 : ℕ) ≤ ((8896507/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1234 :
    ((35590081/5000000 : ℚ) : ℝ) ≤ Real.log (1234 : ℕ)
      ∧ Real.log (1234 : ℕ) ≤ ((71180163/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1235 :
    ((35594131/5000000 : ℚ) : ℝ) ≤ Real.log (1235 : ℕ)
      ∧ Real.log (1235 : ℕ) ≤ ((71188263/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1236 :
    ((17799089/2500000 : ℚ) : ℝ) ≤ Real.log (1236 : ℕ)
      ∧ Real.log (1236 : ℕ) ≤ ((71196357/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1237 :
    ((71204443/10000000 : ℚ) : ℝ) ≤ Real.log (1237 : ℕ)
      ∧ Real.log (1237 : ℕ) ≤ ((17801111/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1238 :
    ((17803131/2500000 : ℚ) : ℝ) ≤ Real.log (1238 : ℕ)
      ∧ Real.log (1238 : ℕ) ≤ ((2848501/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1239 :
    ((35610299/5000000 : ℚ) : ℝ) ≤ Real.log (1239 : ℕ)
      ∧ Real.log (1239 : ℕ) ≤ ((71220599/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1240 :
    ((35614333/5000000 : ℚ) : ℝ) ≤ Real.log (1240 : ℕ)
      ∧ Real.log (1240 : ℕ) ≤ ((71228667/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1241 :
    ((71236727/10000000 : ℚ) : ℝ) ≤ Real.log (1241 : ℕ)
      ∧ Real.log (1241 : ℕ) ≤ ((8904591/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1242 :
    ((35622391/5000000 : ℚ) : ℝ) ≤ Real.log (1242 : ℕ)
      ∧ Real.log (1242 : ℕ) ≤ ((71244783/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1243 :
    ((7125283/1000000 : ℚ) : ℝ) ≤ Real.log (1243 : ℕ)
      ∧ Real.log (1243 : ℕ) ≤ ((71252831/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1244 :
    ((8907609/1250000 : ℚ) : ℝ) ≤ Real.log (1244 : ℕ)
      ∧ Real.log (1244 : ℕ) ≤ ((71260873/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1245 :
    ((17817227/2500000 : ℚ) : ℝ) ≤ Real.log (1245 : ℕ)
      ∧ Real.log (1245 : ℕ) ≤ ((71268909/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1246 :
    ((8909617/1250000 : ℚ) : ℝ) ≤ Real.log (1246 : ℕ)
      ∧ Real.log (1246 : ℕ) ≤ ((71276937/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1247 :
    ((71284959/10000000 : ℚ) : ℝ) ≤ Real.log (1247 : ℕ)
      ∧ Real.log (1247 : ℕ) ≤ ((445531/62500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1248 :
    ((2851719/400000 : ℚ) : ℝ) ≤ Real.log (1248 : ℕ)
      ∧ Real.log (1248 : ℕ) ≤ ((4455811/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1249 :
    ((14260197/2000000 : ℚ) : ℝ) ≤ Real.log (1249 : ℕ)
      ∧ Real.log (1249 : ℕ) ≤ ((35650493/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1250 :
    ((17827247/2500000 : ℚ) : ℝ) ≤ Real.log (1250 : ℕ)
      ∧ Real.log (1250 : ℕ) ≤ ((71308989/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1251 :
    ((14263397/2000000 : ℚ) : ℝ) ≤ Real.log (1251 : ℕ)
      ∧ Real.log (1251 : ℕ) ≤ ((35658493/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1252 :
    ((2852999/400000 : ℚ) : ℝ) ≤ Real.log (1252 : ℕ)
      ∧ Real.log (1252 : ℕ) ≤ ((4457811/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1253 :
    ((71332959/10000000 : ℚ) : ℝ) ≤ Real.log (1253 : ℕ)
      ∧ Real.log (1253 : ℕ) ≤ ((445831/62500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1254 :
    ((71340937/10000000 : ℚ) : ℝ) ≤ Real.log (1254 : ℕ)
      ∧ Real.log (1254 : ℕ) ≤ ((35670469/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1255 :
    ((17837227/2500000 : ℚ) : ℝ) ≤ Real.log (1255 : ℕ)
      ∧ Real.log (1255 : ℕ) ≤ ((71348909/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1256 :
    ((71356873/10000000 : ℚ) : ℝ) ≤ Real.log (1256 : ℕ)
      ∧ Real.log (1256 : ℕ) ≤ ((35678437/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1257 :
    ((2230151/312500 : ℚ) : ℝ) ≤ Real.log (1257 : ℕ)
      ∧ Real.log (1257 : ℕ) ≤ ((71364833/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1258 :
    ((4460799/625000 : ℚ) : ℝ) ≤ Real.log (1258 : ℕ)
      ∧ Real.log (1258 : ℕ) ≤ ((14274557/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1259 :
    ((7138073/1000000 : ℚ) : ℝ) ≤ Real.log (1259 : ℕ)
      ∧ Real.log (1259 : ℕ) ≤ ((71380731/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1260 :
    ((17847167/2500000 : ℚ) : ℝ) ≤ Real.log (1260 : ℕ)
      ∧ Real.log (1260 : ℕ) ≤ ((71388671/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1261 :
    ((71396603/10000000 : ℚ) : ℝ) ≤ Real.log (1261 : ℕ)
      ∧ Real.log (1261 : ℕ) ≤ ((17849151/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1262 :
    ((7140453/1000000 : ℚ) : ℝ) ≤ Real.log (1262 : ℕ)
      ∧ Real.log (1262 : ℕ) ≤ ((71404531/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1263 :
    ((71412451/10000000 : ℚ) : ℝ) ≤ Real.log (1263 : ℕ)
      ∧ Real.log (1263 : ℕ) ≤ ((17853113/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1264 :
    ((14284073/2000000 : ℚ) : ℝ) ≤ Real.log (1264 : ℕ)
      ∧ Real.log (1264 : ℕ) ≤ ((35710183/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1265 :
    ((35714137/5000000 : ℚ) : ℝ) ≤ Real.log (1265 : ℕ)
      ∧ Real.log (1265 : ℕ) ≤ ((2857131/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1266 :
    ((4464761/625000 : ℚ) : ℝ) ≤ Real.log (1266 : ℕ)
      ∧ Real.log (1266 : ℕ) ≤ ((71436177/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1267 :
    ((71444071/10000000 : ℚ) : ℝ) ≤ Real.log (1267 : ℕ)
      ∧ Real.log (1267 : ℕ) ≤ ((8930509/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1268 :
    ((71451961/10000000 : ℚ) : ℝ) ≤ Real.log (1268 : ℕ)
      ∧ Real.log (1268 : ℕ) ≤ ((35725981/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1269 :
    ((17864961/2500000 : ℚ) : ℝ) ≤ Real.log (1269 : ℕ)
      ∧ Real.log (1269 : ℕ) ≤ ((14291969/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1270 :
    ((71467721/10000000 : ℚ) : ℝ) ≤ Real.log (1270 : ℕ)
      ∧ Real.log (1270 : ℕ) ≤ ((35733861/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1271 :
    ((8934449/1250000 : ℚ) : ℝ) ≤ Real.log (1271 : ℕ)
      ∧ Real.log (1271 : ℕ) ≤ ((71475593/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1272 :
    ((71483457/10000000 : ℚ) : ℝ) ≤ Real.log (1272 : ℕ)
      ∧ Real.log (1272 : ℕ) ≤ ((35741729/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1273 :
    ((14298263/2000000 : ℚ) : ℝ) ≤ Real.log (1273 : ℕ)
      ∧ Real.log (1273 : ℕ) ≤ ((17872829/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1274 :
    ((2234349/312500 : ℚ) : ℝ) ≤ Real.log (1274 : ℕ)
      ∧ Real.log (1274 : ℕ) ≤ ((71499169/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1275 :
    ((35753507/5000000 : ℚ) : ℝ) ≤ Real.log (1275 : ℕ)
      ∧ Real.log (1275 : ℕ) ≤ ((14301403/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1276 :
    ((35757427/5000000 : ℚ) : ℝ) ≤ Real.log (1276 : ℕ)
      ∧ Real.log (1276 : ℕ) ≤ ((14302971/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1277 :
    ((558771/78125 : ℚ) : ℝ) ≤ Real.log (1277 : ℕ)
      ∧ Real.log (1277 : ℕ) ≤ ((71522689/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1278 :
    ((17882629/2500000 : ℚ) : ℝ) ≤ Real.log (1278 : ℕ)
      ∧ Real.log (1278 : ℕ) ≤ ((71530517/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1279 :
    ((35769169/5000000 : ℚ) : ℝ) ≤ Real.log (1279 : ℕ)
      ∧ Real.log (1279 : ℕ) ≤ ((71538339/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1280 :
    ((71546153/10000000 : ℚ) : ℝ) ≤ Real.log (1280 : ℕ)
      ∧ Real.log (1280 : ℕ) ≤ ((35773077/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1281 :
    ((71553963/10000000 : ℚ) : ℝ) ≤ Real.log (1281 : ℕ)
      ∧ Real.log (1281 : ℕ) ≤ ((17888491/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1282 :
    ((35780883/5000000 : ℚ) : ℝ) ≤ Real.log (1282 : ℕ)
      ∧ Real.log (1282 : ℕ) ≤ ((71561767/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1283 :
    ((71569563/10000000 : ℚ) : ℝ) ≤ Real.log (1283 : ℕ)
      ∧ Real.log (1283 : ℕ) ≤ ((17892391/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1284 :
    ((35788677/5000000 : ℚ) : ℝ) ≤ Real.log (1284 : ℕ)
      ∧ Real.log (1284 : ℕ) ≤ ((14315471/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1285 :
    ((71585139/10000000 : ℚ) : ℝ) ≤ Real.log (1285 : ℕ)
      ∧ Real.log (1285 : ℕ) ≤ ((3579257/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1286 :
    ((71592919/10000000 : ℚ) : ℝ) ≤ Real.log (1286 : ℕ)
      ∧ Real.log (1286 : ℕ) ≤ ((1789823/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1287 :
    ((17900173/2500000 : ℚ) : ℝ) ≤ Real.log (1287 : ℕ)
      ∧ Real.log (1287 : ℕ) ≤ ((71600693/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1288 :
    ((71608459/10000000 : ℚ) : ℝ) ≤ Real.log (1288 : ℕ)
      ∧ Real.log (1288 : ℕ) ≤ ((3580423/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1289 :
    ((3580811/500000 : ℚ) : ℝ) ≤ Real.log (1289 : ℕ)
      ∧ Real.log (1289 : ℕ) ≤ ((71616221/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1290 :
    ((35811987/5000000 : ℚ) : ℝ) ≤ Real.log (1290 : ℕ)
      ∧ Real.log (1290 : ℕ) ≤ ((2864959/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1291 :
    ((71631723/10000000 : ℚ) : ℝ) ≤ Real.log (1291 : ℕ)
      ∧ Real.log (1291 : ℕ) ≤ ((17907931/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1292 :
    ((35819733/5000000 : ℚ) : ℝ) ≤ Real.log (1292 : ℕ)
      ∧ Real.log (1292 : ℕ) ≤ ((71639467/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1293 :
    ((71647203/10000000 : ℚ) : ℝ) ≤ Real.log (1293 : ℕ)
      ∧ Real.log (1293 : ℕ) ≤ ((17911801/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1294 :
    ((35827467/5000000 : ℚ) : ℝ) ≤ Real.log (1294 : ℕ)
      ∧ Real.log (1294 : ℕ) ≤ ((14330987/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1295 :
    ((71662659/10000000 : ℚ) : ℝ) ≤ Real.log (1295 : ℕ)
      ∧ Real.log (1295 : ℕ) ≤ ((3583133/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1296 :
    ((35835189/5000000 : ℚ) : ℝ) ≤ Real.log (1296 : ℕ)
      ∧ Real.log (1296 : ℕ) ≤ ((71670379/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1297 :
    ((71678091/10000000 : ℚ) : ℝ) ≤ Real.log (1297 : ℕ)
      ∧ Real.log (1297 : ℕ) ≤ ((17919523/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1298 :
    ((35842899/5000000 : ℚ) : ℝ) ≤ Real.log (1298 : ℕ)
      ∧ Real.log (1298 : ℕ) ≤ ((71685799/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1299 :
    ((143387/20000 : ℚ) : ℝ) ≤ Real.log (1299 : ℕ)
      ∧ Real.log (1299 : ℕ) ≤ ((71693501/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1300 :
    ((14340239/2000000 : ℚ) : ℝ) ≤ Real.log (1300 : ℕ)
      ∧ Real.log (1300 : ℕ) ≤ ((17925299/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1301 :
    ((17927221/2500000 : ℚ) : ℝ) ≤ Real.log (1301 : ℕ)
      ∧ Real.log (1301 : ℕ) ≤ ((14341777/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1302 :
    ((8964571/1250000 : ℚ) : ℝ) ≤ Real.log (1302 : ℕ)
      ∧ Real.log (1302 : ℕ) ≤ ((71716569/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1303 :
    ((14344849/2000000 : ℚ) : ℝ) ≤ Real.log (1303 : ℕ)
      ∧ Real.log (1303 : ℕ) ≤ ((35862123/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1304 :
    ((71731917/10000000 : ℚ) : ℝ) ≤ Real.log (1304 : ℕ)
      ∧ Real.log (1304 : ℕ) ≤ ((35865959/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1305 :
    ((71739583/10000000 : ℚ) : ℝ) ≤ Real.log (1305 : ℕ)
      ∧ Real.log (1305 : ℕ) ≤ ((1120931/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1306 :
    ((71747243/10000000 : ℚ) : ℝ) ≤ Real.log (1306 : ℕ)
      ∧ Real.log (1306 : ℕ) ≤ ((17936811/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1307 :
    ((71754897/10000000 : ℚ) : ℝ) ≤ Real.log (1307 : ℕ)
      ∧ Real.log (1307 : ℕ) ≤ ((35877449/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1308 :
    ((14352509/2000000 : ℚ) : ℝ) ≤ Real.log (1308 : ℕ)
      ∧ Real.log (1308 : ℕ) ≤ ((35881273/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1309 :
    ((71770187/10000000 : ℚ) : ℝ) ≤ Real.log (1309 : ℕ)
      ∧ Real.log (1309 : ℕ) ≤ ((17942547/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1310 :
    ((2243057/312500 : ℚ) : ℝ) ≤ Real.log (1310 : ℕ)
      ∧ Real.log (1310 : ℕ) ≤ ((2871113/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1311 :
    ((35892727/5000000 : ℚ) : ℝ) ≤ Real.log (1311 : ℕ)
      ∧ Real.log (1311 : ℕ) ≤ ((14357091/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1312 :
    ((71793079/10000000 : ℚ) : ℝ) ≤ Real.log (1312 : ℕ)
      ∧ Real.log (1312 : ℕ) ≤ ((1794827/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1313 :
    ((35900349/5000000 : ℚ) : ℝ) ≤ Real.log (1313 : ℕ)
      ∧ Real.log (1313 : ℕ) ≤ ((71800699/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1314 :
    ((71808311/10000000 : ℚ) : ℝ) ≤ Real.log (1314 : ℕ)
      ∧ Real.log (1314 : ℕ) ≤ ((8976039/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1315 :
    ((71815919/10000000 : ℚ) : ℝ) ≤ Real.log (1315 : ℕ)
      ∧ Real.log (1315 : ℕ) ≤ ((897699/125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1316 :
    ((71823521/10000000 : ℚ) : ℝ) ≤ Real.log (1316 : ℕ)
      ∧ Real.log (1316 : ℕ) ≤ ((35911761/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1317 :
    ((71831117/10000000 : ℚ) : ℝ) ≤ Real.log (1317 : ℕ)
      ∧ Real.log (1317 : ℕ) ≤ ((35915559/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1318 :
    ((71838707/10000000 : ℚ) : ℝ) ≤ Real.log (1318 : ℕ)
      ∧ Real.log (1318 : ℕ) ≤ ((17959677/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1319 :
    ((71846291/10000000 : ℚ) : ℝ) ≤ Real.log (1319 : ℕ)
      ∧ Real.log (1319 : ℕ) ≤ ((17961573/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1320 :
    ((7185387/1000000 : ℚ) : ℝ) ≤ Real.log (1320 : ℕ)
      ∧ Real.log (1320 : ℕ) ≤ ((71853871/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1321 :
    ((71861443/10000000 : ℚ) : ℝ) ≤ Real.log (1321 : ℕ)
      ∧ Real.log (1321 : ℕ) ≤ ((17965361/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1322 :
    ((7186901/1000000 : ℚ) : ℝ) ≤ Real.log (1322 : ℕ)
      ∧ Real.log (1322 : ℕ) ≤ ((71869011/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1323 :
    ((71876571/10000000 : ℚ) : ℝ) ≤ Real.log (1323 : ℕ)
      ∧ Real.log (1323 : ℕ) ≤ ((17969143/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1324 :
    ((71884127/10000000 : ℚ) : ℝ) ≤ Real.log (1324 : ℕ)
      ∧ Real.log (1324 : ℕ) ≤ ((2246379/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1325 :
    ((71891677/10000000 : ℚ) : ℝ) ≤ Real.log (1325 : ℕ)
      ∧ Real.log (1325 : ℕ) ≤ ((35945839/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1326 :
    ((71899221/10000000 : ℚ) : ℝ) ≤ Real.log (1326 : ℕ)
      ∧ Real.log (1326 : ℕ) ≤ ((35949611/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1327 :
    ((1797669/250000 : ℚ) : ℝ) ≤ Real.log (1327 : ℕ)
      ∧ Real.log (1327 : ℕ) ≤ ((71906761/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1328 :
    ((71914293/10000000 : ℚ) : ℝ) ≤ Real.log (1328 : ℕ)
      ∧ Real.log (1328 : ℕ) ≤ ((35957147/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1329 :
    ((3596091/500000 : ℚ) : ℝ) ≤ Real.log (1329 : ℕ)
      ∧ Real.log (1329 : ℕ) ≤ ((71921821/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1330 :
    ((35964671/5000000 : ℚ) : ℝ) ≤ Real.log (1330 : ℕ)
      ∧ Real.log (1330 : ℕ) ≤ ((71929343/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1331 :
    ((35968429/5000000 : ℚ) : ℝ) ≤ Real.log (1331 : ℕ)
      ∧ Real.log (1331 : ℕ) ≤ ((71936859/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1332 :
    ((4496523/625000 : ℚ) : ℝ) ≤ Real.log (1332 : ℕ)
      ∧ Real.log (1332 : ℕ) ≤ ((71944369/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1333 :
    ((71951873/10000000 : ℚ) : ℝ) ≤ Real.log (1333 : ℕ)
      ∧ Real.log (1333 : ℕ) ≤ ((35975937/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1334 :
    ((17989843/2500000 : ℚ) : ℝ) ≤ Real.log (1334 : ℕ)
      ∧ Real.log (1334 : ℕ) ≤ ((71959373/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1335 :
    ((14393373/2000000 : ℚ) : ℝ) ≤ Real.log (1335 : ℕ)
      ∧ Real.log (1335 : ℕ) ≤ ((35983433/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1336 :
    ((71974353/10000000 : ℚ) : ℝ) ≤ Real.log (1336 : ℕ)
      ∧ Real.log (1336 : ℕ) ≤ ((35987177/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1337 :
    ((14396367/2000000 : ℚ) : ℝ) ≤ Real.log (1337 : ℕ)
      ∧ Real.log (1337 : ℕ) ≤ ((17995459/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1338 :
    ((1124833/156250 : ℚ) : ℝ) ≤ Real.log (1338 : ℕ)
      ∧ Real.log (1338 : ℕ) ≤ ((71989313/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1339 :
    ((71996783/10000000 : ℚ) : ℝ) ≤ Real.log (1339 : ℕ)
      ∧ Real.log (1339 : ℕ) ≤ ((4499799/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1340 :
    ((9000531/1250000 : ℚ) : ℝ) ≤ Real.log (1340 : ℕ)
      ∧ Real.log (1340 : ℕ) ≤ ((72004249/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1341 :
    ((18002927/2500000 : ℚ) : ℝ) ≤ Real.log (1341 : ℕ)
      ∧ Real.log (1341 : ℕ) ≤ ((72011709/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1342 :
    ((72019163/10000000 : ℚ) : ℝ) ≤ Real.log (1342 : ℕ)
      ∧ Real.log (1342 : ℕ) ≤ ((18004791/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1343 :
    ((72026611/10000000 : ℚ) : ℝ) ≤ Real.log (1343 : ℕ)
      ∧ Real.log (1343 : ℕ) ≤ ((18006653/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1344 :
    ((14406811/2000000 : ℚ) : ℝ) ≤ Real.log (1344 : ℕ)
      ∧ Real.log (1344 : ℕ) ≤ ((9004257/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1345 :
    ((18010373/2500000 : ℚ) : ℝ) ≤ Real.log (1345 : ℕ)
      ∧ Real.log (1345 : ℕ) ≤ ((72041493/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1346 :
    ((2881957/400000 : ℚ) : ℝ) ≤ Real.log (1346 : ℕ)
      ∧ Real.log (1346 : ℕ) ≤ ((36024463/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1347 :
    ((72056351/10000000 : ℚ) : ℝ) ≤ Real.log (1347 : ℕ)
      ∧ Real.log (1347 : ℕ) ≤ ((2251761/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1348 :
    ((18015943/2500000 : ℚ) : ℝ) ≤ Real.log (1348 : ℕ)
      ∧ Real.log (1348 : ℕ) ≤ ((72063773/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1349 :
    ((18017797/2500000 : ℚ) : ℝ) ≤ Real.log (1349 : ℕ)
      ∧ Real.log (1349 : ℕ) ≤ ((72071189/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1350 :
    ((36039299/5000000 : ℚ) : ℝ) ≤ Real.log (1350 : ℕ)
      ∧ Real.log (1350 : ℕ) ≤ ((72078599/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1351 :
    ((72086003/10000000 : ℚ) : ℝ) ≤ Real.log (1351 : ℕ)
      ∧ Real.log (1351 : ℕ) ≤ ((18021501/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1352 :
    ((36046701/5000000 : ℚ) : ℝ) ≤ Real.log (1352 : ℕ)
      ∧ Real.log (1352 : ℕ) ≤ ((72093403/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1353 :
    ((18025199/2500000 : ℚ) : ℝ) ≤ Real.log (1353 : ℕ)
      ∧ Real.log (1353 : ℕ) ≤ ((72100797/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1354 :
    ((9013523/1250000 : ℚ) : ℝ) ≤ Real.log (1354 : ℕ)
      ∧ Real.log (1354 : ℕ) ≤ ((14421637/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1355 :
    ((72115567/10000000 : ℚ) : ℝ) ≤ Real.log (1355 : ℕ)
      ∧ Real.log (1355 : ℕ) ≤ ((4507223/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1356 :
    ((1126921/156250 : ℚ) : ℝ) ≤ Real.log (1356 : ℕ)
      ∧ Real.log (1356 : ℕ) ≤ ((14424589/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1357 :
    ((18032579/2500000 : ℚ) : ℝ) ≤ Real.log (1357 : ℕ)
      ∧ Real.log (1357 : ℕ) ≤ ((72130317/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1358 :
    ((72137683/10000000 : ℚ) : ℝ) ≤ Real.log (1358 : ℕ)
      ∧ Real.log (1358 : ℕ) ≤ ((18034421/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1359 :
    ((18036261/2500000 : ℚ) : ℝ) ≤ Real.log (1359 : ℕ)
      ∧ Real.log (1359 : ℕ) ≤ ((14429009/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1360 :
    ((72152399/10000000 : ℚ) : ℝ) ≤ Real.log (1360 : ℕ)
      ∧ Real.log (1360 : ℕ) ≤ ((180381/25000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1361 :
    ((288639/40000 : ℚ) : ℝ) ≤ Real.log (1361 : ℕ)
      ∧ Real.log (1361 : ℕ) ≤ ((72159751/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1362 :
    ((36083547/5000000 : ℚ) : ℝ) ≤ Real.log (1362 : ℕ)
      ∧ Real.log (1362 : ℕ) ≤ ((14433419/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1363 :
    ((36087217/5000000 : ℚ) : ℝ) ≤ Real.log (1363 : ℕ)
      ∧ Real.log (1363 : ℕ) ≤ ((14434887/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1364 :
    ((9022721/1250000 : ℚ) : ℝ) ≤ Real.log (1364 : ℕ)
      ∧ Real.log (1364 : ℕ) ≤ ((72181769/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1365 :
    ((72189097/10000000 : ℚ) : ℝ) ≤ Real.log (1365 : ℕ)
      ∧ Real.log (1365 : ℕ) ≤ ((36094549/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1366 :
    ((3609821/500000 : ℚ) : ℝ) ≤ Real.log (1366 : ℕ)
      ∧ Real.log (1366 : ℕ) ≤ ((72196421/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1367 :
    ((36101869/5000000 : ℚ) : ℝ) ≤ Real.log (1367 : ℕ)
      ∧ Real.log (1367 : ℕ) ≤ ((72203739/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1368 :
    ((1444221/200000 : ℚ) : ℝ) ≤ Real.log (1368 : ℕ)
      ∧ Real.log (1368 : ℕ) ≤ ((72211051/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1369 :
    ((36109179/5000000 : ℚ) : ℝ) ≤ Real.log (1369 : ℕ)
      ∧ Real.log (1369 : ℕ) ≤ ((72218359/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1370 :
    ((3611283/500000 : ℚ) : ℝ) ≤ Real.log (1370 : ℕ)
      ∧ Real.log (1370 : ℕ) ≤ ((72225661/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1371 :
    ((18058239/2500000 : ℚ) : ℝ) ≤ Real.log (1371 : ℕ)
      ∧ Real.log (1371 : ℕ) ≤ ((72232957/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1372 :
    ((9030031/1250000 : ℚ) : ℝ) ≤ Real.log (1372 : ℕ)
      ∧ Real.log (1372 : ℕ) ≤ ((72240249/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1373 :
    ((36123767/5000000 : ℚ) : ℝ) ≤ Real.log (1373 : ℕ)
      ∧ Real.log (1373 : ℕ) ≤ ((14449507/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1374 :
    ((36127407/5000000 : ℚ) : ℝ) ≤ Real.log (1374 : ℕ)
      ∧ Real.log (1374 : ℕ) ≤ ((14450963/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1375 :
    ((7226209/1000000 : ℚ) : ℝ) ≤ Real.log (1375 : ℕ)
      ∧ Real.log (1375 : ℕ) ≤ ((72262091/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1376 :
    ((903367/125000 : ℚ) : ℝ) ≤ Real.log (1376 : ℕ)
      ∧ Real.log (1376 : ℕ) ≤ ((72269361/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1377 :
    ((4517289/625000 : ℚ) : ℝ) ≤ Real.log (1377 : ℕ)
      ∧ Real.log (1377 : ℕ) ≤ ((578213/80000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1378 :
    ((18070971/2500000 : ℚ) : ℝ) ≤ Real.log (1378 : ℕ)
      ∧ Real.log (1378 : ℕ) ≤ ((14456777/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1379 :
    ((36145569/5000000 : ℚ) : ℝ) ≤ Real.log (1379 : ℕ)
      ∧ Real.log (1379 : ℕ) ≤ ((72291139/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1380 :
    ((72298387/10000000 : ℚ) : ℝ) ≤ Real.log (1380 : ℕ)
      ∧ Real.log (1380 : ℕ) ≤ ((18074597/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1381 :
    ((72305631/10000000 : ℚ) : ℝ) ≤ Real.log (1381 : ℕ)
      ∧ Real.log (1381 : ℕ) ≤ ((2259551/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1382 :
    ((7231287/1000000 : ℚ) : ℝ) ≤ Real.log (1382 : ℕ)
      ∧ Real.log (1382 : ℕ) ≤ ((72312871/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1383 :
    ((72320103/10000000 : ℚ) : ℝ) ≤ Real.log (1383 : ℕ)
      ∧ Real.log (1383 : ℕ) ≤ ((9040013/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1384 :
    ((72327331/10000000 : ℚ) : ℝ) ≤ Real.log (1384 : ℕ)
      ∧ Real.log (1384 : ℕ) ≤ ((18081833/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1385 :
    ((36167277/5000000 : ℚ) : ℝ) ≤ Real.log (1385 : ℕ)
      ∧ Real.log (1385 : ℕ) ≤ ((14466911/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1386 :
    ((72341771/10000000 : ℚ) : ℝ) ≤ Real.log (1386 : ℕ)
      ∧ Real.log (1386 : ℕ) ≤ ((18085443/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1387 :
    ((9043623/1250000 : ℚ) : ℝ) ≤ Real.log (1387 : ℕ)
      ∧ Real.log (1387 : ℕ) ≤ ((14469797/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1388 :
    ((72356191/10000000 : ℚ) : ℝ) ≤ Real.log (1388 : ℕ)
      ∧ Real.log (1388 : ℕ) ≤ ((2261131/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1389 :
    ((72363393/10000000 : ℚ) : ℝ) ≤ Real.log (1389 : ℕ)
      ∧ Real.log (1389 : ℕ) ≤ ((36181697/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1390 :
    ((7237059/1000000 : ℚ) : ℝ) ≤ Real.log (1390 : ℕ)
      ∧ Real.log (1390 : ℕ) ≤ ((72370591/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1391 :
    ((72377781/10000000 : ℚ) : ℝ) ≤ Real.log (1391 : ℕ)
      ∧ Real.log (1391 : ℕ) ≤ ((36188891/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1392 :
    ((9048121/1250000 : ℚ) : ℝ) ≤ Real.log (1392 : ℕ)
      ∧ Real.log (1392 : ℕ) ≤ ((72384969/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1393 :
    ((72392149/10000000 : ℚ) : ℝ) ≤ Real.log (1393 : ℕ)
      ∧ Real.log (1393 : ℕ) ≤ ((1447843/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1394 :
    ((2895973/400000 : ℚ) : ℝ) ≤ Real.log (1394 : ℕ)
      ∧ Real.log (1394 : ℕ) ≤ ((36199663/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1395 :
    ((2262703/312500 : ℚ) : ℝ) ≤ Real.log (1395 : ℕ)
      ∧ Real.log (1395 : ℕ) ≤ ((72406497/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1396 :
    ((36206831/5000000 : ℚ) : ℝ) ≤ Real.log (1396 : ℕ)
      ∧ Real.log (1396 : ℕ) ≤ ((72413663/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1397 :
    ((72420823/10000000 : ℚ) : ℝ) ≤ Real.log (1397 : ℕ)
      ∧ Real.log (1397 : ℕ) ≤ ((9052603/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1398 :
    ((72427979/10000000 : ℚ) : ℝ) ≤ Real.log (1398 : ℕ)
      ∧ Real.log (1398 : ℕ) ≤ ((3621399/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1399 :
    ((72435129/10000000 : ℚ) : ℝ) ≤ Real.log (1399 : ℕ)
      ∧ Real.log (1399 : ℕ) ≤ ((7243513/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1400 :
    ((2897691/400000 : ℚ) : ℝ) ≤ Real.log (1400 : ℕ)
      ∧ Real.log (1400 : ℕ) ≤ ((18110569/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1401 :
    ((14489883/2000000 : ℚ) : ℝ) ≤ Real.log (1401 : ℕ)
      ∧ Real.log (1401 : ℕ) ≤ ((9056177/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1402 :
    ((1449131/200000 : ℚ) : ℝ) ≤ Real.log (1402 : ℕ)
      ∧ Real.log (1402 : ℕ) ≤ ((72456551/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1403 :
    ((226449/31250 : ℚ) : ℝ) ≤ Real.log (1403 : ℕ)
      ∧ Real.log (1403 : ℕ) ≤ ((72463681/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1404 :
    ((14494161/2000000 : ℚ) : ℝ) ≤ Real.log (1404 : ℕ)
      ∧ Real.log (1404 : ℕ) ≤ ((36235403/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1405 :
    ((2899117/400000 : ℚ) : ℝ) ≤ Real.log (1405 : ℕ)
      ∧ Real.log (1405 : ℕ) ≤ ((36238963/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1406 :
    ((906063/125000 : ℚ) : ℝ) ≤ Real.log (1406 : ℕ)
      ∧ Real.log (1406 : ℕ) ≤ ((72485041/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1407 :
    ((1449843/200000 : ℚ) : ℝ) ≤ Real.log (1407 : ℕ)
      ∧ Real.log (1407 : ℕ) ≤ ((72492151/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1408 :
    ((14499851/2000000 : ℚ) : ℝ) ≤ Real.log (1408 : ℕ)
      ∧ Real.log (1408 : ℕ) ≤ ((9062407/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1409 :
    ((14501271/2000000 : ℚ) : ℝ) ≤ Real.log (1409 : ℕ)
      ∧ Real.log (1409 : ℕ) ≤ ((18126589/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1410 :
    ((72513449/10000000 : ℚ) : ℝ) ≤ Real.log (1410 : ℕ)
      ∧ Real.log (1410 : ℕ) ≤ ((1450269/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1411 :
    ((72520539/10000000 : ℚ) : ℝ) ≤ Real.log (1411 : ℕ)
      ∧ Real.log (1411 : ℕ) ≤ ((3626027/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1412 :
    ((9065953/1250000 : ℚ) : ℝ) ≤ Real.log (1412 : ℕ)
      ∧ Real.log (1412 : ℕ) ≤ ((580221/80000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1413 :
    ((72534703/10000000 : ℚ) : ℝ) ≤ Real.log (1413 : ℕ)
      ∧ Real.log (1413 : ℕ) ≤ ((4533419/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1414 :
    ((36270889/5000000 : ℚ) : ℝ) ≤ Real.log (1414 : ℕ)
      ∧ Real.log (1414 : ℕ) ≤ ((72541779/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1415 :
    ((4534303/625000 : ℚ) : ℝ) ≤ Real.log (1415 : ℕ)
      ∧ Real.log (1415 : ℕ) ≤ ((72548849/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1416 :
    ((9069489/1250000 : ℚ) : ℝ) ≤ Real.log (1416 : ℕ)
      ∧ Real.log (1416 : ℕ) ≤ ((72555913/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1417 :
    ((18140743/2500000 : ℚ) : ℝ) ≤ Real.log (1417 : ℕ)
      ∧ Real.log (1417 : ℕ) ≤ ((72562973/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1418 :
    ((72570027/10000000 : ℚ) : ℝ) ≤ Real.log (1418 : ℕ)
      ∧ Real.log (1418 : ℕ) ≤ ((18142507/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1419 :
    ((18144269/2500000 : ℚ) : ℝ) ≤ Real.log (1419 : ℕ)
      ∧ Real.log (1419 : ℕ) ≤ ((72577077/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1420 :
    ((72584121/10000000 : ℚ) : ℝ) ≤ Real.log (1420 : ℕ)
      ∧ Real.log (1420 : ℕ) ≤ ((36292061/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1421 :
    ((72591161/10000000 : ℚ) : ℝ) ≤ Real.log (1421 : ℕ)
      ∧ Real.log (1421 : ℕ) ≤ ((36295581/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1422 :
    ((18149549/2500000 : ℚ) : ℝ) ≤ Real.log (1422 : ℕ)
      ∧ Real.log (1422 : ℕ) ≤ ((72598197/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1423 :
    ((2904209/400000 : ℚ) : ℝ) ≤ Real.log (1423 : ℕ)
      ∧ Real.log (1423 : ℕ) ≤ ((36302613/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1424 :
    ((290449/40000 : ℚ) : ℝ) ≤ Real.log (1424 : ℕ)
      ∧ Real.log (1424 : ℕ) ≤ ((72612251/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1425 :
    ((7261927/1000000 : ℚ) : ℝ) ≤ Real.log (1425 : ℕ)
      ∧ Real.log (1425 : ℕ) ≤ ((72619271/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1426 :
    ((36313143/5000000 : ℚ) : ℝ) ≤ Real.log (1426 : ℕ)
      ∧ Real.log (1426 : ℕ) ≤ ((72626287/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1427 :
    ((4539581/625000 : ℚ) : ℝ) ≤ Real.log (1427 : ℕ)
      ∧ Real.log (1427 : ℕ) ≤ ((72633297/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1428 :
    ((72640301/10000000 : ℚ) : ℝ) ≤ Real.log (1428 : ℕ)
      ∧ Real.log (1428 : ℕ) ≤ ((36320151/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1429 :
    ((72647301/10000000 : ℚ) : ℝ) ≤ Real.log (1429 : ℕ)
      ∧ Real.log (1429 : ℕ) ≤ ((36323651/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1430 :
    ((72654297/10000000 : ℚ) : ℝ) ≤ Real.log (1430 : ℕ)
      ∧ Real.log (1430 : ℕ) ≤ ((36327149/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1431 :
    ((72661287/10000000 : ℚ) : ℝ) ≤ Real.log (1431 : ℕ)
      ∧ Real.log (1431 : ℕ) ≤ ((9082661/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1432 :
    ((72668273/10000000 : ℚ) : ℝ) ≤ Real.log (1432 : ℕ)
      ∧ Real.log (1432 : ℕ) ≤ ((36334137/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1433 :
    ((36337627/5000000 : ℚ) : ℝ) ≤ Real.log (1433 : ℕ)
      ∧ Real.log (1433 : ℕ) ≤ ((14535051/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1434 :
    ((7268223/1000000 : ℚ) : ℝ) ≤ Real.log (1434 : ℕ)
      ∧ Real.log (1434 : ℕ) ≤ ((72682231/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1435 :
    ((72689201/10000000 : ℚ) : ℝ) ≤ Real.log (1435 : ℕ)
      ∧ Real.log (1435 : ℕ) ≤ ((36344601/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1436 :
    ((72696167/10000000 : ℚ) : ℝ) ≤ Real.log (1436 : ℕ)
      ∧ Real.log (1436 : ℕ) ≤ ((9087021/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1437 :
    ((9087891/1250000 : ℚ) : ℝ) ≤ Real.log (1437 : ℕ)
      ∧ Real.log (1437 : ℕ) ≤ ((72703129/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1438 :
    ((14542017/2000000 : ℚ) : ℝ) ≤ Real.log (1438 : ℕ)
      ∧ Real.log (1438 : ℕ) ≤ ((36355043/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1439 :
    ((72717037/10000000 : ℚ) : ℝ) ≤ Real.log (1439 : ℕ)
      ∧ Real.log (1439 : ℕ) ≤ ((36358519/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1440 :
    ((72723983/10000000 : ℚ) : ℝ) ≤ Real.log (1440 : ℕ)
      ∧ Real.log (1440 : ℕ) ≤ ((4545249/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1441 :
    ((2909237/400000 : ℚ) : ℝ) ≤ Real.log (1441 : ℕ)
      ∧ Real.log (1441 : ℕ) ≤ ((36365463/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1442 :
    ((72737863/10000000 : ℚ) : ℝ) ≤ Real.log (1442 : ℕ)
      ∧ Real.log (1442 : ℕ) ≤ ((9092233/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1443 :
    ((14548959/2000000 : ℚ) : ℝ) ≤ Real.log (1443 : ℕ)
      ∧ Real.log (1443 : ℕ) ≤ ((18186199/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1444 :
    ((72751723/10000000 : ℚ) : ℝ) ≤ Real.log (1444 : ℕ)
      ∧ Real.log (1444 : ℕ) ≤ ((18187931/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1445 :
    ((36379323/5000000 : ℚ) : ℝ) ≤ Real.log (1445 : ℕ)
      ∧ Real.log (1445 : ℕ) ≤ ((72758647/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1446 :
    ((18191391/2500000 : ℚ) : ℝ) ≤ Real.log (1446 : ℕ)
      ∧ Real.log (1446 : ℕ) ≤ ((14553113/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1447 :
    ((72772477/10000000 : ℚ) : ℝ) ≤ Real.log (1447 : ℕ)
      ∧ Real.log (1447 : ℕ) ≤ ((36386239/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1448 :
    ((14555877/2000000 : ℚ) : ℝ) ≤ Real.log (1448 : ℕ)
      ∧ Real.log (1448 : ℕ) ≤ ((36389693/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1449 :
    ((72786289/10000000 : ℚ) : ℝ) ≤ Real.log (1449 : ℕ)
      ∧ Real.log (1449 : ℕ) ≤ ((7278629/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1450 :
    ((18198297/2500000 : ℚ) : ℝ) ≤ Real.log (1450 : ℕ)
      ∧ Real.log (1450 : ℕ) ≤ ((72793189/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1451 :
    ((36400041/5000000 : ℚ) : ℝ) ≤ Real.log (1451 : ℕ)
      ∧ Real.log (1451 : ℕ) ≤ ((72800083/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1452 :
    ((72806971/10000000 : ℚ) : ℝ) ≤ Real.log (1452 : ℕ)
      ∧ Real.log (1452 : ℕ) ≤ ((18201743/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1453 :
    ((2275433/312500 : ℚ) : ℝ) ≤ Real.log (1453 : ℕ)
      ∧ Real.log (1453 : ℕ) ≤ ((72813857/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1454 :
    ((568912/78125 : ℚ) : ℝ) ≤ Real.log (1454 : ℕ)
      ∧ Real.log (1454 : ℕ) ≤ ((72820737/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1455 :
    ((72827611/10000000 : ℚ) : ℝ) ≤ Real.log (1455 : ℕ)
      ∧ Real.log (1455 : ℕ) ≤ ((18206903/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1456 :
    ((36417241/5000000 : ℚ) : ℝ) ≤ Real.log (1456 : ℕ)
      ∧ Real.log (1456 : ℕ) ≤ ((72834483/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1457 :
    ((18210337/2500000 : ℚ) : ℝ) ≤ Real.log (1457 : ℕ)
      ∧ Real.log (1457 : ℕ) ≤ ((72841349/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1458 :
    ((72848209/10000000 : ℚ) : ℝ) ≤ Real.log (1458 : ℕ)
      ∧ Real.log (1458 : ℕ) ≤ ((7284821/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1459 :
    ((14571013/2000000 : ℚ) : ℝ) ≤ Real.log (1459 : ℕ)
      ∧ Real.log (1459 : ℕ) ≤ ((36427533/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1460 :
    ((72861917/10000000 : ℚ) : ℝ) ≤ Real.log (1460 : ℕ)
      ∧ Real.log (1460 : ℕ) ≤ ((36430959/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1461 :
    ((18217191/2500000 : ℚ) : ℝ) ≤ Real.log (1461 : ℕ)
      ∧ Real.log (1461 : ℕ) ≤ ((14573753/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1462 :
    ((36437803/5000000 : ℚ) : ℝ) ≤ Real.log (1462 : ℕ)
      ∧ Real.log (1462 : ℕ) ≤ ((72875607/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1463 :
    ((18220611/2500000 : ℚ) : ℝ) ≤ Real.log (1463 : ℕ)
      ∧ Real.log (1463 : ℕ) ≤ ((14576489/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1464 :
    ((18222319/2500000 : ℚ) : ℝ) ≤ Real.log (1464 : ℕ)
      ∧ Real.log (1464 : ℕ) ≤ ((72889277/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1465 :
    ((14579221/2000000 : ℚ) : ℝ) ≤ Real.log (1465 : ℕ)
      ∧ Real.log (1465 : ℕ) ≤ ((36448053/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1466 :
    ((4556433/625000 : ℚ) : ℝ) ≤ Real.log (1466 : ℕ)
      ∧ Real.log (1466 : ℕ) ≤ ((72902929/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1467 :
    ((72909747/10000000 : ℚ) : ℝ) ≤ Real.log (1467 : ℕ)
      ∧ Real.log (1467 : ℕ) ≤ ((18227437/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1468 :
    ((36458281/5000000 : ℚ) : ℝ) ≤ Real.log (1468 : ℕ)
      ∧ Real.log (1468 : ℕ) ≤ ((72916563/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1469 :
    ((72923371/10000000 : ℚ) : ℝ) ≤ Real.log (1469 : ℕ)
      ∧ Real.log (1469 : ℕ) ≤ ((18230843/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1470 :
    ((569767/78125 : ℚ) : ℝ) ≤ Real.log (1470 : ℕ)
      ∧ Real.log (1470 : ℕ) ≤ ((72930177/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1471 :
    ((72936977/10000000 : ℚ) : ℝ) ≤ Real.log (1471 : ℕ)
      ∧ Real.log (1471 : ℕ) ≤ ((36468489/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1472 :
    ((18235943/2500000 : ℚ) : ℝ) ≤ Real.log (1472 : ℕ)
      ∧ Real.log (1472 : ℕ) ≤ ((72943773/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1473 :
    ((18237641/2500000 : ℚ) : ℝ) ≤ Real.log (1473 : ℕ)
      ∧ Real.log (1473 : ℕ) ≤ ((14590113/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1474 :
    ((1459147/200000 : ℚ) : ℝ) ≤ Real.log (1474 : ℕ)
      ∧ Real.log (1474 : ℕ) ≤ ((72957351/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1475 :
    ((18241033/2500000 : ℚ) : ℝ) ≤ Real.log (1475 : ℕ)
      ∧ Real.log (1475 : ℕ) ≤ ((72964133/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1476 :
    ((7297091/1000000 : ℚ) : ℝ) ≤ Real.log (1476 : ℕ)
      ∧ Real.log (1476 : ℕ) ≤ ((72970911/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1477 :
    ((36488841/5000000 : ℚ) : ℝ) ≤ Real.log (1477 : ℕ)
      ∧ Real.log (1477 : ℕ) ≤ ((72977683/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1478 :
    ((72984451/10000000 : ℚ) : ℝ) ≤ Real.log (1478 : ℕ)
      ∧ Real.log (1478 : ℕ) ≤ ((18246113/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1479 :
    ((36495607/5000000 : ℚ) : ℝ) ≤ Real.log (1479 : ℕ)
      ∧ Real.log (1479 : ℕ) ≤ ((14598243/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1480 :
    ((72997973/10000000 : ℚ) : ℝ) ≤ Real.log (1480 : ℕ)
      ∧ Real.log (1480 : ℕ) ≤ ((36498987/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1481 :
    ((9125591/1250000 : ℚ) : ℝ) ≤ Real.log (1481 : ℕ)
      ∧ Real.log (1481 : ℕ) ≤ ((73004729/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1482 :
    ((36505739/5000000 : ℚ) : ℝ) ≤ Real.log (1482 : ℕ)
      ∧ Real.log (1482 : ℕ) ≤ ((73011479/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1483 :
    ((73018223/10000000 : ℚ) : ℝ) ≤ Real.log (1483 : ℕ)
      ∧ Real.log (1483 : ℕ) ≤ ((4563639/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1484 :
    ((18256241/2500000 : ℚ) : ℝ) ≤ Real.log (1484 : ℕ)
      ∧ Real.log (1484 : ℕ) ≤ ((14604993/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1485 :
    ((730317/100000 : ℚ) : ℝ) ≤ Real.log (1485 : ℕ)
      ∧ Real.log (1485 : ℕ) ≤ ((73031701/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1486 :
    ((2282451/312500 : ℚ) : ℝ) ≤ Real.log (1486 : ℕ)
      ∧ Real.log (1486 : ℕ) ≤ ((73038433/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1487 :
    ((73045159/10000000 : ℚ) : ℝ) ≤ Real.log (1487 : ℕ)
      ∧ Real.log (1487 : ℕ) ≤ ((1826129/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1488 :
    ((36525941/5000000 : ℚ) : ℝ) ≤ Real.log (1488 : ℕ)
      ∧ Real.log (1488 : ℕ) ≤ ((73051883/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1489 :
    ((365293/50000 : ℚ) : ℝ) ≤ Real.log (1489 : ℕ)
      ∧ Real.log (1489 : ℕ) ≤ ((73058601/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1490 :
    ((73065313/10000000 : ℚ) : ℝ) ≤ Real.log (1490 : ℕ)
      ∧ Real.log (1490 : ℕ) ≤ ((36532657/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1491 :
    ((73072023/10000000 : ℚ) : ℝ) ≤ Real.log (1491 : ℕ)
      ∧ Real.log (1491 : ℕ) ≤ ((9134003/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1492 :
    ((73078727/10000000 : ℚ) : ℝ) ≤ Real.log (1492 : ℕ)
      ∧ Real.log (1492 : ℕ) ≤ ((9134841/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1493 :
    ((73085427/10000000 : ℚ) : ℝ) ≤ Real.log (1493 : ℕ)
      ∧ Real.log (1493 : ℕ) ≤ ((18271357/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1494 :
    ((73092123/10000000 : ℚ) : ℝ) ≤ Real.log (1494 : ℕ)
      ∧ Real.log (1494 : ℕ) ≤ ((18273031/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1495 :
    ((36549407/5000000 : ℚ) : ℝ) ≤ Real.log (1495 : ℕ)
      ∧ Real.log (1495 : ℕ) ≤ ((14619763/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1496 :
    ((73105501/10000000 : ℚ) : ℝ) ≤ Real.log (1496 : ℕ)
      ∧ Real.log (1496 : ℕ) ≤ ((36552751/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1497 :
    ((73112183/10000000 : ℚ) : ℝ) ≤ Real.log (1497 : ℕ)
      ∧ Real.log (1497 : ℕ) ≤ ((9139023/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1498 :
    ((73118861/10000000 : ℚ) : ℝ) ≤ Real.log (1498 : ℕ)
      ∧ Real.log (1498 : ℕ) ≤ ((36559431/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1499 :
    ((36562767/5000000 : ℚ) : ℝ) ≤ Real.log (1499 : ℕ)
      ∧ Real.log (1499 : ℕ) ≤ ((14625107/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1500 :
    ((73132203/10000000 : ℚ) : ℝ) ≤ Real.log (1500 : ℕ)
      ∧ Real.log (1500 : ℕ) ≤ ((18283051/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1501 :
    ((18284717/2500000 : ℚ) : ℝ) ≤ Real.log (1501 : ℕ)
      ∧ Real.log (1501 : ℕ) ≤ ((73138869/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1502 :
    ((9143191/1250000 : ℚ) : ℝ) ≤ Real.log (1502 : ℕ)
      ∧ Real.log (1502 : ℕ) ≤ ((73145529/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1503 :
    ((73152183/10000000 : ℚ) : ℝ) ≤ Real.log (1503 : ℕ)
      ∧ Real.log (1503 : ℕ) ≤ ((9144023/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1504 :
    ((14631767/2000000 : ℚ) : ℝ) ≤ Real.log (1504 : ℕ)
      ∧ Real.log (1504 : ℕ) ≤ ((18289709/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1505 :
    ((73165481/10000000 : ℚ) : ℝ) ≤ Real.log (1505 : ℕ)
      ∧ Real.log (1505 : ℕ) ≤ ((36582741/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1506 :
    ((18293031/2500000 : ℚ) : ℝ) ≤ Real.log (1506 : ℕ)
      ∧ Real.log (1506 : ℕ) ≤ ((585377/80000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1507 :
    ((73178761/10000000 : ℚ) : ℝ) ≤ Real.log (1507 : ℕ)
      ∧ Real.log (1507 : ℕ) ≤ ((36589381/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1508 :
    ((14637079/2000000 : ℚ) : ℝ) ≤ Real.log (1508 : ℕ)
      ∧ Real.log (1508 : ℕ) ≤ ((18296349/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1509 :
    ((9149003/1250000 : ℚ) : ℝ) ≤ Real.log (1509 : ℕ)
      ∧ Real.log (1509 : ℕ) ≤ ((2927681/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1510 :
    ((73198649/10000000 : ℚ) : ℝ) ≤ Real.log (1510 : ℕ)
      ∧ Real.log (1510 : ℕ) ≤ ((1463973/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1511 :
    ((73205269/10000000 : ℚ) : ℝ) ≤ Real.log (1511 : ℕ)
      ∧ Real.log (1511 : ℕ) ≤ ((7320527/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1512 :
    ((14642377/2000000 : ℚ) : ℝ) ≤ Real.log (1512 : ℕ)
      ∧ Real.log (1512 : ℕ) ≤ ((36605943/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1513 :
    ((73218497/10000000 : ℚ) : ℝ) ≤ Real.log (1513 : ℕ)
      ∧ Real.log (1513 : ℕ) ≤ ((36609249/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1514 :
    ((4576569/625000 : ℚ) : ℝ) ≤ Real.log (1514 : ℕ)
      ∧ Real.log (1514 : ℕ) ≤ ((14645021/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1515 :
    ((73231707/10000000 : ℚ) : ℝ) ≤ Real.log (1515 : ℕ)
      ∧ Real.log (1515 : ℕ) ≤ ((18307927/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1516 :
    ((14647661/2000000 : ℚ) : ℝ) ≤ Real.log (1516 : ℕ)
      ∧ Real.log (1516 : ℕ) ≤ ((36619153/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1517 :
    ((73244899/10000000 : ℚ) : ℝ) ≤ Real.log (1517 : ℕ)
      ∧ Real.log (1517 : ℕ) ≤ ((732449/100000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1518 :
    ((73251489/10000000 : ℚ) : ℝ) ≤ Real.log (1518 : ℕ)
      ∧ Real.log (1518 : ℕ) ≤ ((7325149/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1519 :
    ((2930323/400000 : ℚ) : ℝ) ≤ Real.log (1519 : ℕ)
      ∧ Real.log (1519 : ℕ) ≤ ((18314519/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1520 :
    ((4579041/625000 : ℚ) : ℝ) ≤ Real.log (1520 : ℕ)
      ∧ Real.log (1520 : ℕ) ≤ ((73264657/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1521 :
    ((1144863/156250 : ℚ) : ℝ) ≤ Real.log (1521 : ℕ)
      ∧ Real.log (1521 : ℕ) ≤ ((73271233/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1522 :
    ((14655561/2000000 : ℚ) : ℝ) ≤ Real.log (1522 : ℕ)
      ∧ Real.log (1522 : ℕ) ≤ ((36638903/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1523 :
    ((73284373/10000000 : ℚ) : ℝ) ≤ Real.log (1523 : ℕ)
      ∧ Real.log (1523 : ℕ) ≤ ((36642187/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1524 :
    ((73290937/10000000 : ℚ) : ℝ) ≤ Real.log (1524 : ℕ)
      ∧ Real.log (1524 : ℕ) ≤ ((36645469/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1525 :
    ((9162187/1250000 : ℚ) : ℝ) ≤ Real.log (1525 : ℕ)
      ∧ Real.log (1525 : ℕ) ≤ ((73297497/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1526 :
    ((18326013/2500000 : ℚ) : ℝ) ≤ Real.log (1526 : ℕ)
      ∧ Real.log (1526 : ℕ) ≤ ((73304053/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1527 :
    ((73310603/10000000 : ℚ) : ℝ) ≤ Real.log (1527 : ℕ)
      ∧ Real.log (1527 : ℕ) ≤ ((18327651/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1528 :
    ((73317149/10000000 : ℚ) : ℝ) ≤ Real.log (1528 : ℕ)
      ∧ Real.log (1528 : ℕ) ≤ ((1466343/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1529 :
    ((18330923/2500000 : ℚ) : ℝ) ≤ Real.log (1529 : ℕ)
      ∧ Real.log (1529 : ℕ) ≤ ((73323693/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1530 :
    ((7333023/1000000 : ℚ) : ℝ) ≤ Real.log (1530 : ℕ)
      ∧ Real.log (1530 : ℕ) ≤ ((73330231/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1531 :
    ((73336763/10000000 : ℚ) : ℝ) ≤ Real.log (1531 : ℕ)
      ∧ Real.log (1531 : ℕ) ≤ ((18334191/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1532 :
    ((73343293/10000000 : ℚ) : ℝ) ≤ Real.log (1532 : ℕ)
      ∧ Real.log (1532 : ℕ) ≤ ((36671647/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1533 :
    ((36674909/5000000 : ℚ) : ℝ) ≤ Real.log (1533 : ℕ)
      ∧ Real.log (1533 : ℕ) ≤ ((73349819/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1534 :
    ((73356339/10000000 : ℚ) : ℝ) ≤ Real.log (1534 : ℕ)
      ∧ Real.log (1534 : ℕ) ≤ ((3667817/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1535 :
    ((9170357/1250000 : ℚ) : ℝ) ≤ Real.log (1535 : ℕ)
      ∧ Real.log (1535 : ℕ) ≤ ((73362857/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1536 :
    ((73369369/10000000 : ℚ) : ℝ) ≤ Real.log (1536 : ℕ)
      ∧ Real.log (1536 : ℕ) ≤ ((7336937/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1537 :
    ((73375877/10000000 : ℚ) : ℝ) ≤ Real.log (1537 : ℕ)
      ∧ Real.log (1537 : ℕ) ≤ ((36687939/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1538 :
    ((73382381/10000000 : ℚ) : ℝ) ≤ Real.log (1538 : ℕ)
      ∧ Real.log (1538 : ℕ) ≤ ((36691191/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1539 :
    ((73388881/10000000 : ℚ) : ℝ) ≤ Real.log (1539 : ℕ)
      ∧ Real.log (1539 : ℕ) ≤ ((36694441/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1540 :
    ((4587211/625000 : ℚ) : ℝ) ≤ Real.log (1540 : ℕ)
      ∧ Real.log (1540 : ℕ) ≤ ((73395377/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1541 :
    ((18350467/2500000 : ℚ) : ℝ) ≤ Real.log (1541 : ℕ)
      ∧ Real.log (1541 : ℕ) ≤ ((73401869/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1542 :
    ((14681671/2000000 : ℚ) : ℝ) ≤ Real.log (1542 : ℕ)
      ∧ Real.log (1542 : ℕ) ≤ ((18352089/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1543 :
    ((36707419/5000000 : ℚ) : ℝ) ≤ Real.log (1543 : ℕ)
      ∧ Real.log (1543 : ℕ) ≤ ((73414839/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1544 :
    ((73421317/10000000 : ℚ) : ℝ) ≤ Real.log (1544 : ℕ)
      ∧ Real.log (1544 : ℕ) ≤ ((36710659/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1545 :
    ((73427791/10000000 : ℚ) : ℝ) ≤ Real.log (1545 : ℕ)
      ∧ Real.log (1545 : ℕ) ≤ ((4589237/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1546 :
    ((36717131/5000000 : ℚ) : ℝ) ≤ Real.log (1546 : ℕ)
      ∧ Real.log (1546 : ℕ) ≤ ((73434263/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1547 :
    ((9180091/1250000 : ℚ) : ℝ) ≤ Real.log (1547 : ℕ)
      ∧ Real.log (1547 : ℕ) ≤ ((73440729/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1548 :
    ((7344719/1000000 : ℚ) : ℝ) ≤ Real.log (1548 : ℕ)
      ∧ Real.log (1548 : ℕ) ≤ ((73447191/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1549 :
    ((4590853/625000 : ℚ) : ℝ) ≤ Real.log (1549 : ℕ)
      ∧ Real.log (1549 : ℕ) ≤ ((73453649/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1550 :
    ((36730051/5000000 : ℚ) : ℝ) ≤ Real.log (1550 : ℕ)
      ∧ Real.log (1550 : ℕ) ≤ ((73460103/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1551 :
    ((73466551/10000000 : ℚ) : ℝ) ≤ Real.log (1551 : ℕ)
      ∧ Real.log (1551 : ℕ) ≤ ((9183319/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1552 :
    ((73472997/10000000 : ℚ) : ℝ) ≤ Real.log (1552 : ℕ)
      ∧ Real.log (1552 : ℕ) ≤ ((36736499/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1553 :
    ((36739719/5000000 : ℚ) : ℝ) ≤ Real.log (1553 : ℕ)
      ∧ Real.log (1553 : ℕ) ≤ ((73479439/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1554 :
    ((587887/80000 : ℚ) : ℝ) ≤ Real.log (1554 : ℕ)
      ∧ Real.log (1554 : ℕ) ≤ ((18371469/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1555 :
    ((18373077/2500000 : ℚ) : ℝ) ≤ Real.log (1555 : ℕ)
      ∧ Real.log (1555 : ℕ) ≤ ((73492309/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1556 :
    ((73498737/10000000 : ℚ) : ℝ) ≤ Real.log (1556 : ℕ)
      ∧ Real.log (1556 : ℕ) ≤ ((36749369/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1557 :
    ((73505161/10000000 : ℚ) : ℝ) ≤ Real.log (1557 : ℕ)
      ∧ Real.log (1557 : ℕ) ≤ ((36752581/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1558 :
    ((36755791/5000000 : ℚ) : ℝ) ≤ Real.log (1558 : ℕ)
      ∧ Real.log (1558 : ℕ) ≤ ((73511583/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1559 :
    ((36758999/5000000 : ℚ) : ℝ) ≤ Real.log (1559 : ℕ)
      ∧ Real.log (1559 : ℕ) ≤ ((73517999/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1560 :
    ((7352441/1000000 : ℚ) : ℝ) ≤ Real.log (1560 : ℕ)
      ∧ Real.log (1560 : ℕ) ≤ ((73524413/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1561 :
    ((73530819/10000000 : ℚ) : ℝ) ≤ Real.log (1561 : ℕ)
      ∧ Real.log (1561 : ℕ) ≤ ((3676541/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1562 :
    ((73537223/10000000 : ℚ) : ℝ) ≤ Real.log (1562 : ℕ)
      ∧ Real.log (1562 : ℕ) ≤ ((9192153/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1563 :
    ((73543623/10000000 : ℚ) : ℝ) ≤ Real.log (1563 : ℕ)
      ∧ Real.log (1563 : ℕ) ≤ ((9192953/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1564 :
    ((73550019/10000000 : ℚ) : ℝ) ≤ Real.log (1564 : ℕ)
      ∧ Real.log (1564 : ℕ) ≤ ((3677501/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1565 :
    ((73556411/10000000 : ℚ) : ℝ) ≤ Real.log (1565 : ℕ)
      ∧ Real.log (1565 : ℕ) ≤ ((18389103/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1566 :
    ((36781399/5000000 : ℚ) : ℝ) ≤ Real.log (1566 : ℕ)
      ∧ Real.log (1566 : ℕ) ≤ ((73562799/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1567 :
    ((36784591/5000000 : ℚ) : ℝ) ≤ Real.log (1567 : ℕ)
      ∧ Real.log (1567 : ℕ) ≤ ((73569183/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1568 :
    ((36787781/5000000 : ℚ) : ℝ) ≤ Real.log (1568 : ℕ)
      ∧ Real.log (1568 : ℕ) ≤ ((73575563/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1569 :
    ((73581937/10000000 : ℚ) : ℝ) ≤ Real.log (1569 : ℕ)
      ∧ Real.log (1569 : ℕ) ≤ ((36790969/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1570 :
    ((18397077/2500000 : ℚ) : ℝ) ≤ Real.log (1570 : ℕ)
      ∧ Real.log (1570 : ℕ) ≤ ((73588309/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1571 :
    ((18398669/2500000 : ℚ) : ℝ) ≤ Real.log (1571 : ℕ)
      ∧ Real.log (1571 : ℕ) ≤ ((73594677/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1572 :
    ((73601039/10000000 : ℚ) : ℝ) ≤ Real.log (1572 : ℕ)
      ∧ Real.log (1572 : ℕ) ≤ ((920013/125000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1573 :
    ((73607399/10000000 : ℚ) : ℝ) ≤ Real.log (1573 : ℕ)
      ∧ Real.log (1573 : ℕ) ≤ ((368037/50000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1574 :
    ((36806877/5000000 : ℚ) : ℝ) ≤ Real.log (1574 : ℕ)
      ∧ Real.log (1574 : ℕ) ≤ ((14722751/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1575 :
    ((14724021/2000000 : ℚ) : ℝ) ≤ Real.log (1575 : ℕ)
      ∧ Real.log (1575 : ℕ) ≤ ((36810053/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1576 :
    ((18406613/2500000 : ℚ) : ℝ) ≤ Real.log (1576 : ℕ)
      ∧ Real.log (1576 : ℕ) ≤ ((73626453/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1577 :
    ((14726559/2000000 : ℚ) : ℝ) ≤ Real.log (1577 : ℕ)
      ∧ Real.log (1577 : ℕ) ≤ ((18408199/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1578 :
    ((14727827/2000000 : ℚ) : ℝ) ≤ Real.log (1578 : ℕ)
      ∧ Real.log (1578 : ℕ) ≤ ((2301223/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1579 :
    ((7364547/1000000 : ℚ) : ℝ) ≤ Real.log (1579 : ℕ)
      ∧ Real.log (1579 : ℕ) ≤ ((73645471/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1580 :
    ((73651801/10000000 : ℚ) : ℝ) ≤ Real.log (1580 : ℕ)
      ∧ Real.log (1580 : ℕ) ≤ ((36825901/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1581 :
    ((4603633/625000 : ℚ) : ℝ) ≤ Real.log (1581 : ℕ)
      ∧ Real.log (1581 : ℕ) ≤ ((73658129/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1582 :
    ((73664451/10000000 : ℚ) : ℝ) ≤ Real.log (1582 : ℕ)
      ∧ Real.log (1582 : ℕ) ≤ ((18416113/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1583 :
    ((7367077/1000000 : ℚ) : ℝ) ≤ Real.log (1583 : ℕ)
      ∧ Real.log (1583 : ℕ) ≤ ((73670771/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1584 :
    ((14735417/2000000 : ℚ) : ℝ) ≤ Real.log (1584 : ℕ)
      ∧ Real.log (1584 : ℕ) ≤ ((36838543/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1585 :
    ((18420849/2500000 : ℚ) : ℝ) ≤ Real.log (1585 : ℕ)
      ∧ Real.log (1585 : ℕ) ≤ ((73683397/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1586 :
    ((9211213/1250000 : ℚ) : ℝ) ≤ Real.log (1586 : ℕ)
      ∧ Real.log (1586 : ℕ) ≤ ((14737941/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1587 :
    ((73696007/10000000 : ℚ) : ℝ) ≤ Real.log (1587 : ℕ)
      ∧ Real.log (1587 : ℕ) ≤ ((9212001/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1588 :
    ((36851153/5000000 : ℚ) : ℝ) ≤ Real.log (1588 : ℕ)
      ∧ Real.log (1588 : ℕ) ≤ ((73702307/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1589 :
    ((73708601/10000000 : ℚ) : ℝ) ≤ Real.log (1589 : ℕ)
      ∧ Real.log (1589 : ℕ) ≤ ((36854301/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1590 :
    ((18428723/2500000 : ℚ) : ℝ) ≤ Real.log (1590 : ℕ)
      ∧ Real.log (1590 : ℕ) ≤ ((73714893/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1591 :
    ((3686059/500000 : ℚ) : ℝ) ≤ Real.log (1591 : ℕ)
      ∧ Real.log (1591 : ℕ) ≤ ((73721181/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1592 :
    ((73727463/10000000 : ℚ) : ℝ) ≤ Real.log (1592 : ℕ)
      ∧ Real.log (1592 : ℕ) ≤ ((9215933/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1593 :
    ((73733743/10000000 : ℚ) : ℝ) ≤ Real.log (1593 : ℕ)
      ∧ Real.log (1593 : ℕ) ≤ ((4608359/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1594 :
    ((36870009/5000000 : ℚ) : ℝ) ≤ Real.log (1594 : ℕ)
      ∧ Real.log (1594 : ℕ) ≤ ((73740019/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1595 :
    ((7374629/1000000 : ℚ) : ℝ) ≤ Real.log (1595 : ℕ)
      ∧ Real.log (1595 : ℕ) ≤ ((73746291/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1596 :
    ((73752557/10000000 : ℚ) : ℝ) ≤ Real.log (1596 : ℕ)
      ∧ Real.log (1596 : ℕ) ≤ ((36876279/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1597 :
    ((73758821/10000000 : ℚ) : ℝ) ≤ Real.log (1597 : ℕ)
      ∧ Real.log (1597 : ℕ) ≤ ((36879411/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1598 :
    ((73765081/10000000 : ℚ) : ℝ) ≤ Real.log (1598 : ℕ)
      ∧ Real.log (1598 : ℕ) ≤ ((36882541/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1599 :
    ((73771337/10000000 : ℚ) : ℝ) ≤ Real.log (1599 : ℕ)
      ∧ Real.log (1599 : ℕ) ≤ ((36885669/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1600 :
    ((73777589/10000000 : ℚ) : ℝ) ≤ Real.log (1600 : ℕ)
      ∧ Real.log (1600 : ℕ) ≤ ((7377759/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1601 :
    ((73783837/10000000 : ℚ) : ℝ) ≤ Real.log (1601 : ℕ)
      ∧ Real.log (1601 : ℕ) ≤ ((36891919/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1602 :
    ((73790081/10000000 : ℚ) : ℝ) ≤ Real.log (1602 : ℕ)
      ∧ Real.log (1602 : ℕ) ≤ ((36895041/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1603 :
    ((73796321/10000000 : ℚ) : ℝ) ≤ Real.log (1603 : ℕ)
      ∧ Real.log (1603 : ℕ) ≤ ((36898161/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1604 :
    ((73802557/10000000 : ℚ) : ℝ) ≤ Real.log (1604 : ℕ)
      ∧ Real.log (1604 : ℕ) ≤ ((36901279/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1605 :
    ((7380879/1000000 : ℚ) : ℝ) ≤ Real.log (1605 : ℕ)
      ∧ Real.log (1605 : ℕ) ≤ ((73808791/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1606 :
    ((36907509/5000000 : ℚ) : ℝ) ≤ Real.log (1606 : ℕ)
      ∧ Real.log (1606 : ℕ) ≤ ((73815019/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1607 :
    ((73821243/10000000 : ℚ) : ℝ) ≤ Real.log (1607 : ℕ)
      ∧ Real.log (1607 : ℕ) ≤ ((18455311/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1608 :
    ((9228433/1250000 : ℚ) : ℝ) ≤ Real.log (1608 : ℕ)
      ∧ Real.log (1608 : ℕ) ≤ ((14765493/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1609 :
    ((73833681/10000000 : ℚ) : ℝ) ≤ Real.log (1609 : ℕ)
      ∧ Real.log (1609 : ℕ) ≤ ((36916841/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1610 :
    ((36919947/5000000 : ℚ) : ℝ) ≤ Real.log (1610 : ℕ)
      ∧ Real.log (1610 : ℕ) ≤ ((14767979/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1611 :
    ((73846103/10000000 : ℚ) : ℝ) ≤ Real.log (1611 : ℕ)
      ∧ Real.log (1611 : ℕ) ≤ ((9230763/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1612 :
    ((73852309/10000000 : ℚ) : ℝ) ≤ Real.log (1612 : ℕ)
      ∧ Real.log (1612 : ℕ) ≤ ((7385231/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1613 :
    ((7385851/1000000 : ℚ) : ℝ) ≤ Real.log (1613 : ℕ)
      ∧ Real.log (1613 : ℕ) ≤ ((73858511/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1614 :
    ((18466177/2500000 : ℚ) : ℝ) ≤ Real.log (1614 : ℕ)
      ∧ Real.log (1614 : ℕ) ≤ ((73864709/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1615 :
    ((36935451/5000000 : ℚ) : ℝ) ≤ Real.log (1615 : ℕ)
      ∧ Real.log (1615 : ℕ) ≤ ((73870903/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1616 :
    ((18469273/2500000 : ℚ) : ℝ) ≤ Real.log (1616 : ℕ)
      ∧ Real.log (1616 : ℕ) ≤ ((73877093/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1617 :
    ((36941639/5000000 : ℚ) : ℝ) ≤ Real.log (1617 : ℕ)
      ∧ Real.log (1617 : ℕ) ≤ ((73883279/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1618 :
    ((3694473/500000 : ℚ) : ℝ) ≤ Real.log (1618 : ℕ)
      ∧ Real.log (1618 : ℕ) ≤ ((73889461/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1619 :
    ((73895639/10000000 : ℚ) : ℝ) ≤ Real.log (1619 : ℕ)
      ∧ Real.log (1619 : ℕ) ≤ ((1847391/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1620 :
    ((36950907/5000000 : ℚ) : ℝ) ≤ Real.log (1620 : ℕ)
      ∧ Real.log (1620 : ℕ) ≤ ((14780363/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1621 :
    ((14781597/2000000 : ℚ) : ℝ) ≤ Real.log (1621 : ℕ)
      ∧ Real.log (1621 : ℕ) ≤ ((36953993/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1622 :
    ((9239269/1250000 : ℚ) : ℝ) ≤ Real.log (1622 : ℕ)
      ∧ Real.log (1622 : ℕ) ≤ ((73914153/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1623 :
    ((14784063/2000000 : ℚ) : ℝ) ≤ Real.log (1623 : ℕ)
      ∧ Real.log (1623 : ℕ) ≤ ((18480079/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1624 :
    ((2957059/400000 : ℚ) : ℝ) ≤ Real.log (1624 : ℕ)
      ∧ Real.log (1624 : ℕ) ≤ ((18481619/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1625 :
    ((7393263/1000000 : ℚ) : ℝ) ≤ Real.log (1625 : ℕ)
      ∧ Real.log (1625 : ℕ) ≤ ((73932631/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1626 :
    ((36969391/5000000 : ℚ) : ℝ) ≤ Real.log (1626 : ℕ)
      ∧ Real.log (1626 : ℕ) ≤ ((73938783/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1627 :
    ((73944931/10000000 : ℚ) : ℝ) ≤ Real.log (1627 : ℕ)
      ∧ Real.log (1627 : ℕ) ≤ ((18486233/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1628 :
    ((2958043/400000 : ℚ) : ℝ) ≤ Real.log (1628 : ℕ)
      ∧ Real.log (1628 : ℕ) ≤ ((18487769/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1629 :
    ((2311163/312500 : ℚ) : ℝ) ≤ Real.log (1629 : ℕ)
      ∧ Real.log (1629 : ℕ) ≤ ((73957217/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1630 :
    ((9245419/1250000 : ℚ) : ℝ) ≤ Real.log (1630 : ℕ)
      ∧ Real.log (1630 : ℕ) ≤ ((73963353/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1631 :
    ((36984743/5000000 : ℚ) : ℝ) ≤ Real.log (1631 : ℕ)
      ∧ Real.log (1631 : ℕ) ≤ ((73969487/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1632 :
    ((14795123/2000000 : ℚ) : ℝ) ≤ Real.log (1632 : ℕ)
      ∧ Real.log (1632 : ℕ) ≤ ((1155869/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1633 :
    ((3699087/500000 : ℚ) : ℝ) ≤ Real.log (1633 : ℕ)
      ∧ Real.log (1633 : ℕ) ≤ ((73981741/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1634 :
    ((36993931/5000000 : ℚ) : ℝ) ≤ Real.log (1634 : ℕ)
      ∧ Real.log (1634 : ℕ) ≤ ((73987863/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1635 :
    ((3699699/500000 : ℚ) : ℝ) ≤ Real.log (1635 : ℕ)
      ∧ Real.log (1635 : ℕ) ≤ ((73993981/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1636 :
    ((14800019/2000000 : ℚ) : ℝ) ≤ Real.log (1636 : ℕ)
      ∧ Real.log (1636 : ℕ) ≤ ((2312503/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1637 :
    ((14801241/2000000 : ℚ) : ℝ) ≤ Real.log (1637 : ℕ)
      ∧ Real.log (1637 : ℕ) ≤ ((37003103/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1638 :
    ((9251539/1250000 : ℚ) : ℝ) ≤ Real.log (1638 : ℕ)
      ∧ Real.log (1638 : ℕ) ≤ ((74012313/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1639 :
    ((14803683/2000000 : ℚ) : ℝ) ≤ Real.log (1639 : ℕ)
      ∧ Real.log (1639 : ℕ) ≤ ((4626151/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1640 :
    ((14804903/2000000 : ℚ) : ℝ) ≤ Real.log (1640 : ℕ)
      ∧ Real.log (1640 : ℕ) ≤ ((18506129/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1641 :
    ((7403061/1000000 : ℚ) : ℝ) ≤ Real.log (1641 : ℕ)
      ∧ Real.log (1641 : ℕ) ≤ ((74030611/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1642 :
    ((37018351/5000000 : ℚ) : ℝ) ≤ Real.log (1642 : ℕ)
      ∧ Real.log (1642 : ℕ) ≤ ((74036703/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1643 :
    ((74042791/10000000 : ℚ) : ℝ) ≤ Real.log (1643 : ℕ)
      ∧ Real.log (1643 : ℕ) ≤ ((9255349/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1644 :
    ((592391/80000 : ℚ) : ℝ) ≤ Real.log (1644 : ℕ)
      ∧ Real.log (1644 : ℕ) ≤ ((18512219/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1645 :
    ((18513739/2500000 : ℚ) : ℝ) ≤ Real.log (1645 : ℕ)
      ∧ Real.log (1645 : ℕ) ≤ ((74054957/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1646 :
    ((74061033/10000000 : ℚ) : ℝ) ≤ Real.log (1646 : ℕ)
      ∧ Real.log (1646 : ℕ) ≤ ((37030517/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1647 :
    ((74067107/10000000 : ℚ) : ℝ) ≤ Real.log (1647 : ℕ)
      ∧ Real.log (1647 : ℕ) ≤ ((18516777/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1648 :
    ((74073177/10000000 : ℚ) : ℝ) ≤ Real.log (1648 : ℕ)
      ∧ Real.log (1648 : ℕ) ≤ ((37036589/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1649 :
    ((74079243/10000000 : ℚ) : ℝ) ≤ Real.log (1649 : ℕ)
      ∧ Real.log (1649 : ℕ) ≤ ((18519811/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1650 :
    ((14817061/2000000 : ℚ) : ℝ) ≤ Real.log (1650 : ℕ)
      ∧ Real.log (1650 : ℕ) ≤ ((37042653/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1651 :
    ((18522841/2500000 : ℚ) : ℝ) ≤ Real.log (1651 : ℕ)
      ∧ Real.log (1651 : ℕ) ≤ ((14818273/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1652 :
    ((74097419/10000000 : ℚ) : ℝ) ≤ Real.log (1652 : ℕ)
      ∧ Real.log (1652 : ℕ) ≤ ((3704871/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1653 :
    ((7410347/1000000 : ℚ) : ℝ) ≤ Real.log (1653 : ℕ)
      ∧ Real.log (1653 : ℕ) ≤ ((74103471/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1654 :
    ((37054759/5000000 : ℚ) : ℝ) ≤ Real.log (1654 : ℕ)
      ∧ Real.log (1654 : ℕ) ≤ ((74109519/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1655 :
    ((37057781/5000000 : ℚ) : ℝ) ≤ Real.log (1655 : ℕ)
      ∧ Real.log (1655 : ℕ) ≤ ((74115563/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1656 :
    ((74121603/10000000 : ℚ) : ℝ) ≤ Real.log (1656 : ℕ)
      ∧ Real.log (1656 : ℕ) ≤ ((18530401/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1657 :
    ((1853191/250000 : ℚ) : ℝ) ≤ Real.log (1657 : ℕ)
      ∧ Real.log (1657 : ℕ) ≤ ((74127641/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1658 :
    ((74133673/10000000 : ℚ) : ℝ) ≤ Real.log (1658 : ℕ)
      ∧ Real.log (1658 : ℕ) ≤ ((37066837/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1659 :
    ((37069851/5000000 : ℚ) : ℝ) ≤ Real.log (1659 : ℕ)
      ∧ Real.log (1659 : ℕ) ≤ ((74139703/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1660 :
    ((1158527/156250 : ℚ) : ℝ) ≤ Real.log (1660 : ℕ)
      ∧ Real.log (1660 : ℕ) ≤ ((74145729/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1661 :
    ((74151751/10000000 : ℚ) : ℝ) ≤ Real.log (1661 : ℕ)
      ∧ Real.log (1661 : ℕ) ≤ ((9268969/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1662 :
    ((74157769/10000000 : ℚ) : ℝ) ≤ Real.log (1662 : ℕ)
      ∧ Real.log (1662 : ℕ) ≤ ((7415777/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1663 :
    ((9270473/1250000 : ℚ) : ℝ) ≤ Real.log (1663 : ℕ)
      ∧ Real.log (1663 : ℕ) ≤ ((14832757/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1664 :
    ((18542449/2500000 : ℚ) : ℝ) ≤ Real.log (1664 : ℕ)
      ∧ Real.log (1664 : ℕ) ≤ ((74169797/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1665 :
    ((18543951/2500000 : ℚ) : ℝ) ≤ Real.log (1665 : ℕ)
      ∧ Real.log (1665 : ℕ) ≤ ((14835161/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1666 :
    ((4636363/625000 : ℚ) : ℝ) ≤ Real.log (1666 : ℕ)
      ∧ Real.log (1666 : ℕ) ≤ ((74181809/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1667 :
    ((2318369/312500 : ℚ) : ℝ) ≤ Real.log (1667 : ℕ)
      ∧ Real.log (1667 : ℕ) ≤ ((74187809/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1668 :
    ((14838761/2000000 : ℚ) : ℝ) ≤ Real.log (1668 : ℕ)
      ∧ Real.log (1668 : ℕ) ≤ ((37096903/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1669 :
    ((74199799/10000000 : ℚ) : ℝ) ≤ Real.log (1669 : ℕ)
      ∧ Real.log (1669 : ℕ) ≤ ((370999/50000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1670 :
    ((74205789/10000000 : ℚ) : ℝ) ≤ Real.log (1670 : ℕ)
      ∧ Real.log (1670 : ℕ) ≤ ((7420579/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1671 :
    ((2968471/400000 : ℚ) : ℝ) ≤ Real.log (1671 : ℕ)
      ∧ Real.log (1671 : ℕ) ≤ ((1159559/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1672 :
    ((74217757/10000000 : ℚ) : ℝ) ≤ Real.log (1672 : ℕ)
      ∧ Real.log (1672 : ℕ) ≤ ((37108879/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1673 :
    ((74223737/10000000 : ℚ) : ℝ) ≤ Real.log (1673 : ℕ)
      ∧ Real.log (1673 : ℕ) ≤ ((37111869/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1674 :
    ((4639357/625000 : ℚ) : ℝ) ≤ Real.log (1674 : ℕ)
      ∧ Real.log (1674 : ℕ) ≤ ((74229713/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1675 :
    ((18558921/2500000 : ℚ) : ℝ) ≤ Real.log (1675 : ℕ)
      ∧ Real.log (1675 : ℕ) ≤ ((14847137/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1676 :
    ((18560413/2500000 : ℚ) : ℝ) ≤ Real.log (1676 : ℕ)
      ∧ Real.log (1676 : ℕ) ≤ ((74241653/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1677 :
    ((74247617/10000000 : ℚ) : ℝ) ≤ Real.log (1677 : ℕ)
      ∧ Real.log (1677 : ℕ) ≤ ((37123809/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1678 :
    ((37126789/5000000 : ℚ) : ℝ) ≤ Real.log (1678 : ℕ)
      ∧ Real.log (1678 : ℕ) ≤ ((74253579/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1679 :
    ((4641221/625000 : ℚ) : ℝ) ≤ Real.log (1679 : ℕ)
      ∧ Real.log (1679 : ℕ) ≤ ((74259537/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1680 :
    ((7426549/1000000 : ℚ) : ℝ) ≤ Real.log (1680 : ℕ)
      ∧ Real.log (1680 : ℕ) ≤ ((74265491/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1681 :
    ((74271441/10000000 : ℚ) : ℝ) ≤ Real.log (1681 : ℕ)
      ∧ Real.log (1681 : ℕ) ≤ ((37135721/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1682 :
    ((18569347/2500000 : ℚ) : ℝ) ≤ Real.log (1682 : ℕ)
      ∧ Real.log (1682 : ℕ) ≤ ((74277389/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1683 :
    ((74283331/10000000 : ℚ) : ℝ) ≤ Real.log (1683 : ℕ)
      ∧ Real.log (1683 : ℕ) ≤ ((18570833/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1684 :
    ((74289271/10000000 : ℚ) : ℝ) ≤ Real.log (1684 : ℕ)
      ∧ Real.log (1684 : ℕ) ≤ ((9286159/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1685 :
    ((9286901/1250000 : ℚ) : ℝ) ≤ Real.log (1685 : ℕ)
      ∧ Real.log (1685 : ℕ) ≤ ((74295209/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1686 :
    ((74301141/10000000 : ℚ) : ℝ) ≤ Real.log (1686 : ℕ)
      ∧ Real.log (1686 : ℕ) ≤ ((37150571/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1687 :
    ((7430707/1000000 : ℚ) : ℝ) ≤ Real.log (1687 : ℕ)
      ∧ Real.log (1687 : ℕ) ≤ ((74307071/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1688 :
    ((18578249/2500000 : ℚ) : ℝ) ≤ Real.log (1688 : ℕ)
      ∧ Real.log (1688 : ℕ) ≤ ((74312997/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1689 :
    ((74318919/10000000 : ℚ) : ℝ) ≤ Real.log (1689 : ℕ)
      ∧ Real.log (1689 : ℕ) ≤ ((1857973/250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1690 :
    ((37162419/5000000 : ℚ) : ℝ) ≤ Real.log (1690 : ℕ)
      ∧ Real.log (1690 : ℕ) ≤ ((74324839/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1691 :
    ((74330753/10000000 : ℚ) : ℝ) ≤ Real.log (1691 : ℕ)
      ∧ Real.log (1691 : ℕ) ≤ ((37165377/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1692 :
    ((14867333/2000000 : ℚ) : ℝ) ≤ Real.log (1692 : ℕ)
      ∧ Real.log (1692 : ℕ) ≤ ((37168333/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1693 :
    ((74342573/10000000 : ℚ) : ℝ) ≤ Real.log (1693 : ℕ)
      ∧ Real.log (1693 : ℕ) ≤ ((37171287/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1694 :
    ((37174239/5000000 : ℚ) : ℝ) ≤ Real.log (1694 : ℕ)
      ∧ Real.log (1694 : ℕ) ≤ ((74348479/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1695 :
    ((3717719/500000 : ℚ) : ℝ) ≤ Real.log (1695 : ℕ)
      ∧ Real.log (1695 : ℕ) ≤ ((74354381/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1696 :
    ((37180139/5000000 : ℚ) : ℝ) ≤ Real.log (1696 : ℕ)
      ∧ Real.log (1696 : ℕ) ≤ ((74360279/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1697 :
    ((18591543/2500000 : ℚ) : ℝ) ≤ Real.log (1697 : ℕ)
      ∧ Real.log (1697 : ℕ) ≤ ((74366173/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1698 :
    ((74372063/10000000 : ℚ) : ℝ) ≤ Real.log (1698 : ℕ)
      ∧ Real.log (1698 : ℕ) ≤ ((2324127/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1699 :
    ((74377951/10000000 : ℚ) : ℝ) ≤ Real.log (1699 : ℕ)
      ∧ Real.log (1699 : ℕ) ≤ ((2324311/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1700 :
    ((14876767/2000000 : ℚ) : ℝ) ≤ Real.log (1700 : ℕ)
      ∧ Real.log (1700 : ℕ) ≤ ((18595959/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1701 :
    ((14877943/2000000 : ℚ) : ℝ) ≤ Real.log (1701 : ℕ)
      ∧ Real.log (1701 : ℕ) ≤ ((18597429/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1702 :
    ((74395593/10000000 : ℚ) : ℝ) ≤ Real.log (1702 : ℕ)
      ∧ Real.log (1702 : ℕ) ≤ ((37197797/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1703 :
    ((37200733/5000000 : ℚ) : ℝ) ≤ Real.log (1703 : ℕ)
      ∧ Real.log (1703 : ℕ) ≤ ((74401467/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1704 :
    ((74407337/10000000 : ℚ) : ℝ) ≤ Real.log (1704 : ℕ)
      ∧ Real.log (1704 : ℕ) ≤ ((37203669/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1705 :
    ((74413203/10000000 : ℚ) : ℝ) ≤ Real.log (1705 : ℕ)
      ∧ Real.log (1705 : ℕ) ≤ ((18603301/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1706 :
    ((74419067/10000000 : ℚ) : ℝ) ≤ Real.log (1706 : ℕ)
      ∧ Real.log (1706 : ℕ) ≤ ((18604767/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1707 :
    ((74424927/10000000 : ℚ) : ℝ) ≤ Real.log (1707 : ℕ)
      ∧ Real.log (1707 : ℕ) ≤ ((2325779/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1708 :
    ((74430783/10000000 : ℚ) : ℝ) ≤ Real.log (1708 : ℕ)
      ∧ Real.log (1708 : ℕ) ≤ ((1162981/156250 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1709 :
    ((18609159/2500000 : ℚ) : ℝ) ≤ Real.log (1709 : ℕ)
      ∧ Real.log (1709 : ℕ) ≤ ((74436637/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1710 :
    ((37221243/5000000 : ℚ) : ℝ) ≤ Real.log (1710 : ℕ)
      ∧ Real.log (1710 : ℕ) ≤ ((74442487/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1711 :
    ((18612083/2500000 : ℚ) : ℝ) ≤ Real.log (1711 : ℕ)
      ∧ Real.log (1711 : ℕ) ≤ ((74448333/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1712 :
    ((2978167/400000 : ℚ) : ℝ) ≤ Real.log (1712 : ℕ)
      ∧ Real.log (1712 : ℕ) ≤ ((2326693/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1713 :
    ((74460013/10000000 : ℚ) : ℝ) ≤ Real.log (1713 : ℕ)
      ∧ Real.log (1713 : ℕ) ≤ ((4653751/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1714 :
    ((74465849/10000000 : ℚ) : ℝ) ≤ Real.log (1714 : ℕ)
      ∧ Real.log (1714 : ℕ) ≤ ((18616463/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1715 :
    ((74471683/10000000 : ℚ) : ℝ) ≤ Real.log (1715 : ℕ)
      ∧ Real.log (1715 : ℕ) ≤ ((18617921/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1716 :
    ((9309689/1250000 : ℚ) : ℝ) ≤ Real.log (1716 : ℕ)
      ∧ Real.log (1716 : ℕ) ≤ ((74477513/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1717 :
    ((37241669/5000000 : ℚ) : ℝ) ≤ Real.log (1717 : ℕ)
      ∧ Real.log (1717 : ℕ) ≤ ((74483339/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1718 :
    ((74489161/10000000 : ℚ) : ℝ) ≤ Real.log (1718 : ℕ)
      ∧ Real.log (1718 : ℕ) ≤ ((37244581/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1719 :
    ((3724749/500000 : ℚ) : ℝ) ≤ Real.log (1719 : ℕ)
      ∧ Real.log (1719 : ℕ) ≤ ((74494981/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1720 :
    ((14900159/2000000 : ℚ) : ℝ) ≤ Real.log (1720 : ℕ)
      ∧ Real.log (1720 : ℕ) ≤ ((18625199/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1721 :
    ((74506607/10000000 : ℚ) : ℝ) ≤ Real.log (1721 : ℕ)
      ∧ Real.log (1721 : ℕ) ≤ ((4656663/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1722 :
    ((2328513/312500 : ℚ) : ℝ) ≤ Real.log (1722 : ℕ)
      ∧ Real.log (1722 : ℕ) ≤ ((74512417/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1723 :
    ((37259111/5000000 : ℚ) : ℝ) ≤ Real.log (1723 : ℕ)
      ∧ Real.log (1723 : ℕ) ≤ ((74518223/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1724 :
    ((9315503/1250000 : ℚ) : ℝ) ≤ Real.log (1724 : ℕ)
      ∧ Real.log (1724 : ℕ) ≤ ((2980961/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1725 :
    ((74529823/10000000 : ℚ) : ℝ) ≤ Real.log (1725 : ℕ)
      ∧ Real.log (1725 : ℕ) ≤ ((2329057/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1726 :
    ((37267809/5000000 : ℚ) : ℝ) ≤ Real.log (1726 : ℕ)
      ∧ Real.log (1726 : ℕ) ≤ ((74535619/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1727 :
    ((7454141/1000000 : ℚ) : ℝ) ≤ Real.log (1727 : ℕ)
      ∧ Real.log (1727 : ℕ) ≤ ((74541411/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1728 :
    ((74547199/10000000 : ℚ) : ℝ) ≤ Real.log (1728 : ℕ)
      ∧ Real.log (1728 : ℕ) ≤ ((23296/3125 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1729 :
    ((9319123/1250000 : ℚ) : ℝ) ≤ Real.log (1729 : ℕ)
      ∧ Real.log (1729 : ℕ) ≤ ((14910597/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1730 :
    ((37279383/5000000 : ℚ) : ℝ) ≤ Real.log (1730 : ℕ)
      ∧ Real.log (1730 : ℕ) ≤ ((74558767/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1731 :
    ((14912909/2000000 : ℚ) : ℝ) ≤ Real.log (1731 : ℕ)
      ∧ Real.log (1731 : ℕ) ≤ ((37282273/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1732 :
    ((932129/125000 : ℚ) : ℝ) ≤ Real.log (1732 : ℕ)
      ∧ Real.log (1732 : ℕ) ≤ ((74570321/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1733 :
    ((18644023/2500000 : ℚ) : ℝ) ≤ Real.log (1733 : ℕ)
      ∧ Real.log (1733 : ℕ) ≤ ((74576093/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1734 :
    ((74581861/10000000 : ℚ) : ℝ) ≤ Real.log (1734 : ℕ)
      ∧ Real.log (1734 : ℕ) ≤ ((37290931/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1735 :
    ((37293813/5000000 : ℚ) : ℝ) ≤ Real.log (1735 : ℕ)
      ∧ Real.log (1735 : ℕ) ≤ ((74587627/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1736 :
    ((18648347/2500000 : ℚ) : ℝ) ≤ Real.log (1736 : ℕ)
      ∧ Real.log (1736 : ℕ) ≤ ((74593389/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1737 :
    ((74599147/10000000 : ℚ) : ℝ) ≤ Real.log (1737 : ℕ)
      ∧ Real.log (1737 : ℕ) ≤ ((18649787/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1738 :
    ((74604903/10000000 : ℚ) : ℝ) ≤ Real.log (1738 : ℕ)
      ∧ Real.log (1738 : ℕ) ≤ ((9325613/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1739 :
    ((14922131/2000000 : ℚ) : ℝ) ≤ Real.log (1739 : ℕ)
      ∧ Real.log (1739 : ℕ) ≤ ((2331583/312500 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1740 :
    ((74616403/10000000 : ℚ) : ℝ) ≤ Real.log (1740 : ℕ)
      ∧ Real.log (1740 : ℕ) ≤ ((18654101/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1741 :
    ((74622149/10000000 : ℚ) : ℝ) ≤ Real.log (1741 : ℕ)
      ∧ Real.log (1741 : ℕ) ≤ ((1492443/200000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1742 :
    ((74627891/10000000 : ℚ) : ℝ) ≤ Real.log (1742 : ℕ)
      ∧ Real.log (1742 : ℕ) ≤ ((18656973/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1743 :
    ((7463363/1000000 : ℚ) : ℝ) ≤ Real.log (1743 : ℕ)
      ∧ Real.log (1743 : ℕ) ≤ ((74633631/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1744 :
    ((37319683/5000000 : ℚ) : ℝ) ≤ Real.log (1744 : ℕ)
      ∧ Real.log (1744 : ℕ) ≤ ((74639367/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1745 :
    ((37322549/5000000 : ℚ) : ℝ) ≤ Real.log (1745 : ℕ)
      ∧ Real.log (1745 : ℕ) ≤ ((74645099/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1746 :
    ((74650827/10000000 : ℚ) : ℝ) ≤ Real.log (1746 : ℕ)
      ∧ Real.log (1746 : ℕ) ≤ ((18662707/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1747 :
    ((74656553/10000000 : ℚ) : ℝ) ≤ Real.log (1747 : ℕ)
      ∧ Real.log (1747 : ℕ) ≤ ((37328277/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1748 :
    ((2986491/400000 : ℚ) : ℝ) ≤ Real.log (1748 : ℕ)
      ∧ Real.log (1748 : ℕ) ≤ ((18665569/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1749 :
    ((37333997/5000000 : ℚ) : ℝ) ≤ Real.log (1749 : ℕ)
      ∧ Real.log (1749 : ℕ) ≤ ((14933599/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1750 :
    ((7467371/1000000 : ℚ) : ℝ) ≤ Real.log (1750 : ℕ)
      ∧ Real.log (1750 : ℕ) ≤ ((74673711/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1751 :
    ((74679423/10000000 : ℚ) : ℝ) ≤ Real.log (1751 : ℕ)
      ∧ Real.log (1751 : ℕ) ≤ ((583433/78125 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1752 :
    ((18671283/2500000 : ℚ) : ℝ) ≤ Real.log (1752 : ℕ)
      ∧ Real.log (1752 : ℕ) ≤ ((74685133/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1753 :
    ((37345419/5000000 : ℚ) : ℝ) ≤ Real.log (1753 : ℕ)
      ∧ Real.log (1753 : ℕ) ≤ ((74690839/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1754 :
    ((74696541/10000000 : ℚ) : ℝ) ≤ Real.log (1754 : ℕ)
      ∧ Real.log (1754 : ℕ) ≤ ((37348271/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1755 :
    ((74702241/10000000 : ℚ) : ℝ) ≤ Real.log (1755 : ℕ)
      ∧ Real.log (1755 : ℕ) ≤ ((37351121/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1756 :
    ((74707937/10000000 : ℚ) : ℝ) ≤ Real.log (1756 : ℕ)
      ∧ Real.log (1756 : ℕ) ≤ ((37353969/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1757 :
    ((7471363/1000000 : ℚ) : ℝ) ≤ Real.log (1757 : ℕ)
      ∧ Real.log (1757 : ℕ) ≤ ((74713631/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1758 :
    ((1867983/250000 : ℚ) : ℝ) ≤ Real.log (1758 : ℕ)
      ∧ Real.log (1758 : ℕ) ≤ ((74719321/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1759 :
    ((74725007/10000000 : ℚ) : ℝ) ≤ Real.log (1759 : ℕ)
      ∧ Real.log (1759 : ℕ) ≤ ((4670313/625000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1760 :
    ((7473069/1000000 : ℚ) : ℝ) ≤ Real.log (1760 : ℕ)
      ∧ Real.log (1760 : ℕ) ≤ ((74730691/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1761 :
    ((74736371/10000000 : ℚ) : ℝ) ≤ Real.log (1761 : ℕ)
      ∧ Real.log (1761 : ℕ) ≤ ((18684093/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1762 :
    ((2335689/312500 : ℚ) : ℝ) ≤ Real.log (1762 : ℕ)
      ∧ Real.log (1762 : ℕ) ≤ ((74742049/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1763 :
    ((74747721/10000000 : ℚ) : ℝ) ≤ Real.log (1763 : ℕ)
      ∧ Real.log (1763 : ℕ) ≤ ((37373861/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1764 :
    ((4672087/625000 : ℚ) : ℝ) ≤ Real.log (1764 : ℕ)
      ∧ Real.log (1764 : ℕ) ≤ ((74753393/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1765 :
    ((74759059/10000000 : ℚ) : ℝ) ≤ Real.log (1765 : ℕ)
      ∧ Real.log (1765 : ℕ) ≤ ((3737953/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1766 :
    ((74764723/10000000 : ℚ) : ℝ) ≤ Real.log (1766 : ℕ)
      ∧ Real.log (1766 : ℕ) ≤ ((18691181/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1767 :
    ((4673149/625000 : ℚ) : ℝ) ≤ Real.log (1767 : ℕ)
      ∧ Real.log (1767 : ℕ) ≤ ((14954077/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1768 :
    ((37388021/5000000 : ℚ) : ℝ) ≤ Real.log (1768 : ℕ)
      ∧ Real.log (1768 : ℕ) ≤ ((74776043/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1769 :
    ((584232/78125 : ℚ) : ℝ) ≤ Real.log (1769 : ℕ)
      ∧ Real.log (1769 : ℕ) ≤ ((74781697/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1770 :
    ((18696837/2500000 : ℚ) : ℝ) ≤ Real.log (1770 : ℕ)
      ∧ Real.log (1770 : ℕ) ≤ ((74787349/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1771 :
    ((18698249/2500000 : ℚ) : ℝ) ≤ Real.log (1771 : ℕ)
      ∧ Real.log (1771 : ℕ) ≤ ((74792997/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1772 :
    ((74798641/10000000 : ℚ) : ℝ) ≤ Real.log (1772 : ℕ)
      ∧ Real.log (1772 : ℕ) ≤ ((37399321/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1773 :
    ((74804283/10000000 : ℚ) : ℝ) ≤ Real.log (1773 : ℕ)
      ∧ Real.log (1773 : ℕ) ≤ ((18701071/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1774 :
    ((74809921/10000000 : ℚ) : ℝ) ≤ Real.log (1774 : ℕ)
      ∧ Real.log (1774 : ℕ) ≤ ((37404961/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1775 :
    ((74815557/10000000 : ℚ) : ℝ) ≤ Real.log (1775 : ℕ)
      ∧ Real.log (1775 : ℕ) ≤ ((37407779/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1776 :
    ((74821189/10000000 : ℚ) : ℝ) ≤ Real.log (1776 : ℕ)
      ∧ Real.log (1776 : ℕ) ≤ ((7482119/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1777 :
    ((37413409/5000000 : ℚ) : ℝ) ≤ Real.log (1777 : ℕ)
      ∧ Real.log (1777 : ℕ) ≤ ((74826819/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1778 :
    ((18708111/2500000 : ℚ) : ℝ) ≤ Real.log (1778 : ℕ)
      ∧ Real.log (1778 : ℕ) ≤ ((14966489/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1779 :
    ((37419033/5000000 : ℚ) : ℝ) ≤ Real.log (1779 : ℕ)
      ∧ Real.log (1779 : ℕ) ≤ ((74838067/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1780 :
    ((37421843/5000000 : ℚ) : ℝ) ≤ Real.log (1780 : ℕ)
      ∧ Real.log (1780 : ℕ) ≤ ((74843687/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1781 :
    ((37424651/5000000 : ℚ) : ℝ) ≤ Real.log (1781 : ℕ)
      ∧ Real.log (1781 : ℕ) ≤ ((74849303/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1782 :
    ((18713729/2500000 : ℚ) : ℝ) ≤ Real.log (1782 : ℕ)
      ∧ Real.log (1782 : ℕ) ≤ ((74854917/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1783 :
    ((37430263/5000000 : ℚ) : ℝ) ≤ Real.log (1783 : ℕ)
      ∧ Real.log (1783 : ℕ) ≤ ((74860527/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1784 :
    ((74866133/10000000 : ℚ) : ℝ) ≤ Real.log (1784 : ℕ)
      ∧ Real.log (1784 : ℕ) ≤ ((37433067/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1785 :
    ((14974347/2000000 : ℚ) : ℝ) ≤ Real.log (1785 : ℕ)
      ∧ Real.log (1785 : ℕ) ≤ ((37435869/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1786 :
    ((74877337/10000000 : ℚ) : ℝ) ≤ Real.log (1786 : ℕ)
      ∧ Real.log (1786 : ℕ) ≤ ((37438669/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1787 :
    ((14976587/2000000 : ℚ) : ℝ) ≤ Real.log (1787 : ℕ)
      ∧ Real.log (1787 : ℕ) ≤ ((9360367/1250000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1788 :
    ((74888529/10000000 : ℚ) : ℝ) ≤ Real.log (1788 : ℕ)
      ∧ Real.log (1788 : ℕ) ≤ ((7488853/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1789 :
    ((1872353/250000 : ℚ) : ℝ) ≤ Real.log (1789 : ℕ)
      ∧ Real.log (1789 : ℕ) ≤ ((74894121/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1790 :
    ((74899707/10000000 : ℚ) : ℝ) ≤ Real.log (1790 : ℕ)
      ∧ Real.log (1790 : ℕ) ≤ ((7489971/1000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1791 :
    ((37452647/5000000 : ℚ) : ℝ) ≤ Real.log (1791 : ℕ)
      ∧ Real.log (1791 : ℕ) ≤ ((14981059/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1792 :
    ((37455437/5000000 : ℚ) : ℝ) ≤ Real.log (1792 : ℕ)
      ∧ Real.log (1792 : ℕ) ≤ ((74910877/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1793 :
    ((37458227/5000000 : ℚ) : ℝ) ≤ Real.log (1793 : ℕ)
      ∧ Real.log (1793 : ℕ) ≤ ((14983291/2000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1794 :
    ((7492203/1000000 : ℚ) : ℝ) ≤ Real.log (1794 : ℕ)
      ∧ Real.log (1794 : ℕ) ≤ ((74922031/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1795 :
    ((74927603/10000000 : ℚ) : ℝ) ≤ Real.log (1795 : ℕ)
      ∧ Real.log (1795 : ℕ) ≤ ((18731901/2500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1796 :
    ((18733293/2500000 : ℚ) : ℝ) ≤ Real.log (1796 : ℕ)
      ∧ Real.log (1796 : ℕ) ≤ ((74933173/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1797 :
    ((37469369/5000000 : ℚ) : ℝ) ≤ Real.log (1797 : ℕ)
      ∧ Real.log (1797 : ℕ) ≤ ((74938739/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1798 :
    ((37472151/5000000 : ℚ) : ℝ) ≤ Real.log (1798 : ℕ)
      ∧ Real.log (1798 : ℕ) ≤ ((74944303/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1799 :
    ((37474931/5000000 : ℚ) : ℝ) ≤ Real.log (1799 : ℕ)
      ∧ Real.log (1799 : ℕ) ≤ ((74949863/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1800 :
    ((74955419/10000000 : ℚ) : ℝ) ≤ Real.log (1800 : ℕ)
      ∧ Real.log (1800 : ℕ) ≤ ((3747771/500000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1801 :
    ((74960973/10000000 : ℚ) : ℝ) ≤ Real.log (1801 : ℕ)
      ∧ Real.log (1801 : ℕ) ≤ ((37480487/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1802 :
    ((18741631/2500000 : ℚ) : ℝ) ≤ Real.log (1802 : ℕ)
      ∧ Real.log (1802 : ℕ) ≤ ((2998661/400000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1803 :
    ((9371509/1250000 : ℚ) : ℝ) ≤ Real.log (1803 : ℕ)
      ∧ Real.log (1803 : ℕ) ≤ ((74972073/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1804 :
    ((74977617/10000000 : ℚ) : ℝ) ≤ Real.log (1804 : ℕ)
      ∧ Real.log (1804 : ℕ) ≤ ((37488809/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1805 :
    ((37491579/5000000 : ℚ) : ℝ) ≤ Real.log (1805 : ℕ)
      ∧ Real.log (1805 : ℕ) ≤ ((74983159/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1806 :
    ((74988697/10000000 : ℚ) : ℝ) ≤ Real.log (1806 : ℕ)
      ∧ Real.log (1806 : ℕ) ≤ ((37494349/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1807 :
    ((9374279/1250000 : ℚ) : ℝ) ≤ Real.log (1807 : ℕ)
      ∧ Real.log (1807 : ℕ) ≤ ((74994233/10000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1808 :
    ((14999953/2000000 : ℚ) : ℝ) ≤ Real.log (1808 : ℕ)
      ∧ Real.log (1808 : ℕ) ≤ ((37499883/5000000 : ℚ) : ℝ) :=
  log_bracket 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1809 :
    ((37502647/5000000 : ℚ) : ℝ) ≤ Real.log (1809 : ℕ)
      ∧ Real.log (1809 : ℕ) ≤ ((15001059/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1810 :
    ((75010821/10000000 : ℚ) : ℝ) ≤ Real.log (1810 : ℕ)
      ∧ Real.log (1810 : ℕ) ≤ ((37505411/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1811 :
    ((9377043/1250000 : ℚ) : ℝ) ≤ Real.log (1811 : ℕ)
      ∧ Real.log (1811 : ℕ) ≤ ((15003269/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1812 :
    ((9377733/1250000 : ℚ) : ℝ) ≤ Real.log (1812 : ℕ)
      ∧ Real.log (1812 : ℕ) ≤ ((15004373/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1813 :
    ((75027381/10000000 : ℚ) : ℝ) ≤ Real.log (1813 : ℕ)
      ∧ Real.log (1813 : ℕ) ≤ ((9378423/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1814 :
    ((1172389/156250 : ℚ) : ℝ) ≤ Real.log (1814 : ℕ)
      ∧ Real.log (1814 : ℕ) ≤ ((75032897/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1815 :
    ((75038407/10000000 : ℚ) : ℝ) ≤ Real.log (1815 : ℕ)
      ∧ Real.log (1815 : ℕ) ≤ ((9379801/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1816 :
    ((15008783/2000000 : ℚ) : ℝ) ≤ Real.log (1816 : ℕ)
      ∧ Real.log (1816 : ℕ) ≤ ((18760979/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1817 :
    ((3752471/500000 : ℚ) : ℝ) ≤ Real.log (1817 : ℕ)
      ∧ Real.log (1817 : ℕ) ≤ ((75049421/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1818 :
    ((37527461/5000000 : ℚ) : ℝ) ≤ Real.log (1818 : ℕ)
      ∧ Real.log (1818 : ℕ) ≤ ((75054923/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1819 :
    ((75060421/10000000 : ℚ) : ℝ) ≤ Real.log (1819 : ℕ)
      ∧ Real.log (1819 : ℕ) ≤ ((37530211/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1820 :
    ((75065917/10000000 : ℚ) : ℝ) ≤ Real.log (1820 : ℕ)
      ∧ Real.log (1820 : ℕ) ≤ ((37532959/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1821 :
    ((7507141/1000000 : ℚ) : ℝ) ≤ Real.log (1821 : ℕ)
      ∧ Real.log (1821 : ℕ) ≤ ((75071411/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1822 :
    ((750769/100000 : ℚ) : ℝ) ≤ Real.log (1822 : ℕ)
      ∧ Real.log (1822 : ℕ) ≤ ((75076901/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1823 :
    ((75082387/10000000 : ℚ) : ℝ) ≤ Real.log (1823 : ℕ)
      ∧ Real.log (1823 : ℕ) ≤ ((18770597/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1824 :
    ((75087871/10000000 : ℚ) : ℝ) ≤ Real.log (1824 : ℕ)
      ∧ Real.log (1824 : ℕ) ≤ ((586624/78125 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1825 :
    ((9386669/1250000 : ℚ) : ℝ) ≤ Real.log (1825 : ℕ)
      ∧ Real.log (1825 : ℕ) ≤ ((75093353/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1826 :
    ((7509883/1000000 : ℚ) : ℝ) ≤ Real.log (1826 : ℕ)
      ∧ Real.log (1826 : ℕ) ≤ ((75098831/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1827 :
    ((15020861/2000000 : ℚ) : ℝ) ≤ Real.log (1827 : ℕ)
      ∧ Real.log (1827 : ℕ) ≤ ((37552153/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1828 :
    ((75109777/10000000 : ℚ) : ℝ) ≤ Real.log (1828 : ℕ)
      ∧ Real.log (1828 : ℕ) ≤ ((37554889/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1829 :
    ((37557623/5000000 : ℚ) : ℝ) ≤ Real.log (1829 : ℕ)
      ∧ Real.log (1829 : ℕ) ≤ ((75115247/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1830 :
    ((9390089/1250000 : ℚ) : ℝ) ≤ Real.log (1830 : ℕ)
      ∧ Real.log (1830 : ℕ) ≤ ((75120713/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1831 :
    ((3005047/400000 : ℚ) : ℝ) ≤ Real.log (1831 : ℕ)
      ∧ Real.log (1831 : ℕ) ≤ ((2347693/312500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1832 :
    ((15026327/2000000 : ℚ) : ℝ) ≤ Real.log (1832 : ℕ)
      ∧ Real.log (1832 : ℕ) ≤ ((18782909/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1833 :
    ((18784273/2500000 : ℚ) : ℝ) ≤ Real.log (1833 : ℕ)
      ∧ Real.log (1833 : ℕ) ≤ ((75137093/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1834 :
    ((37571273/5000000 : ℚ) : ℝ) ≤ Real.log (1834 : ℕ)
      ∧ Real.log (1834 : ℕ) ≤ ((75142547/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1835 :
    ((75147997/10000000 : ℚ) : ℝ) ≤ Real.log (1835 : ℕ)
      ∧ Real.log (1835 : ℕ) ≤ ((37573999/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1836 :
    ((15030689/2000000 : ℚ) : ℝ) ≤ Real.log (1836 : ℕ)
      ∧ Real.log (1836 : ℕ) ≤ ((37576723/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1837 :
    ((7515889/1000000 : ℚ) : ℝ) ≤ Real.log (1837 : ℕ)
      ∧ Real.log (1837 : ℕ) ≤ ((75158891/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1838 :
    ((18791083/2500000 : ℚ) : ℝ) ≤ Real.log (1838 : ℕ)
      ∧ Real.log (1838 : ℕ) ≤ ((15032867/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1839 :
    ((18792443/2500000 : ℚ) : ℝ) ≤ Real.log (1839 : ℕ)
      ∧ Real.log (1839 : ℕ) ≤ ((75169773/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1840 :
    ((9396901/1250000 : ℚ) : ℝ) ≤ Real.log (1840 : ℕ)
      ∧ Real.log (1840 : ℕ) ≤ ((75175209/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1841 :
    ((75180641/10000000 : ℚ) : ℝ) ≤ Real.log (1841 : ℕ)
      ∧ Real.log (1841 : ℕ) ≤ ((37590321/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1842 :
    ((9398259/1250000 : ℚ) : ℝ) ≤ Real.log (1842 : ℕ)
      ∧ Real.log (1842 : ℕ) ≤ ((75186073/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1843 :
    ((75191499/10000000 : ℚ) : ℝ) ≤ Real.log (1843 : ℕ)
      ∧ Real.log (1843 : ℕ) ≤ ((150383/20000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1844 :
    ((75196923/10000000 : ℚ) : ℝ) ≤ Real.log (1844 : ℕ)
      ∧ Real.log (1844 : ℕ) ≤ ((37598463/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1845 :
    ((15040469/2000000 : ℚ) : ℝ) ≤ Real.log (1845 : ℕ)
      ∧ Real.log (1845 : ℕ) ≤ ((37601173/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1846 :
    ((18801941/2500000 : ℚ) : ℝ) ≤ Real.log (1846 : ℕ)
      ∧ Real.log (1846 : ℕ) ≤ ((15041553/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1847 :
    ((75213179/10000000 : ℚ) : ℝ) ≤ Real.log (1847 : ℕ)
      ∧ Real.log (1847 : ℕ) ≤ ((3760659/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1848 :
    ((2350581/312500 : ℚ) : ℝ) ≤ Real.log (1848 : ℕ)
      ∧ Real.log (1848 : ℕ) ≤ ((75218593/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1849 :
    ((37612001/5000000 : ℚ) : ℝ) ≤ Real.log (1849 : ℕ)
      ∧ Real.log (1849 : ℕ) ≤ ((75224003/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1850 :
    ((75229409/10000000 : ℚ) : ℝ) ≤ Real.log (1850 : ℕ)
      ∧ Real.log (1850 : ℕ) ≤ ((7522941/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1851 :
    ((75234813/10000000 : ℚ) : ℝ) ≤ Real.log (1851 : ℕ)
      ∧ Real.log (1851 : ℕ) ≤ ((37617407/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1852 :
    ((37620107/5000000 : ℚ) : ℝ) ≤ Real.log (1852 : ℕ)
      ∧ Real.log (1852 : ℕ) ≤ ((15048043/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1853 :
    ((18811403/2500000 : ℚ) : ℝ) ≤ Real.log (1853 : ℕ)
      ∧ Real.log (1853 : ℕ) ≤ ((75245613/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1854 :
    ((75251007/10000000 : ℚ) : ℝ) ≤ Real.log (1854 : ℕ)
      ∧ Real.log (1854 : ℕ) ≤ ((1175797/156250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1855 :
    ((75256399/10000000 : ℚ) : ℝ) ≤ Real.log (1855 : ℕ)
      ∧ Real.log (1855 : ℕ) ≤ ((188141/25000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1856 :
    ((75261789/10000000 : ℚ) : ℝ) ≤ Real.log (1856 : ℕ)
      ∧ Real.log (1856 : ℕ) ≤ ((7526179/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1857 :
    ((3010687/400000 : ℚ) : ℝ) ≤ Real.log (1857 : ℕ)
      ∧ Real.log (1857 : ℕ) ≤ ((9408397/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1858 :
    ((75272559/10000000 : ℚ) : ℝ) ≤ Real.log (1858 : ℕ)
      ∧ Real.log (1858 : ℕ) ≤ ((940907/125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1859 :
    ((75277939/10000000 : ℚ) : ℝ) ≤ Real.log (1859 : ℕ)
      ∧ Real.log (1859 : ℕ) ≤ ((3763897/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1860 :
    ((75283317/10000000 : ℚ) : ℝ) ≤ Real.log (1860 : ℕ)
      ∧ Real.log (1860 : ℕ) ≤ ((37641659/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1861 :
    ((18822173/2500000 : ℚ) : ℝ) ≤ Real.log (1861 : ℕ)
      ∧ Real.log (1861 : ℕ) ≤ ((75288693/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1862 :
    ((4705879/625000 : ℚ) : ℝ) ≤ Real.log (1862 : ℕ)
      ∧ Real.log (1862 : ℕ) ≤ ((15058813/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1863 :
    ((75299433/10000000 : ℚ) : ℝ) ≤ Real.log (1863 : ℕ)
      ∧ Real.log (1863 : ℕ) ≤ ((37649717/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1864 :
    ((75304799/10000000 : ℚ) : ℝ) ≤ Real.log (1864 : ℕ)
      ∧ Real.log (1864 : ℕ) ≤ ((94131/12500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1865 :
    ((75310163/10000000 : ℚ) : ℝ) ≤ Real.log (1865 : ℕ)
      ∧ Real.log (1865 : ℕ) ≤ ((18827541/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1866 :
    ((75315523/10000000 : ℚ) : ℝ) ≤ Real.log (1866 : ℕ)
      ∧ Real.log (1866 : ℕ) ≤ ((18828881/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1867 :
    ((75320881/10000000 : ℚ) : ℝ) ≤ Real.log (1867 : ℕ)
      ∧ Real.log (1867 : ℕ) ≤ ((37660441/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1868 :
    ((18831559/2500000 : ℚ) : ℝ) ≤ Real.log (1868 : ℕ)
      ∧ Real.log (1868 : ℕ) ≤ ((75326237/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1869 :
    ((75331587/10000000 : ℚ) : ℝ) ≤ Real.log (1869 : ℕ)
      ∧ Real.log (1869 : ℕ) ≤ ((7533159/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1870 :
    ((9417117/1250000 : ℚ) : ℝ) ≤ Real.log (1870 : ℕ)
      ∧ Real.log (1870 : ℕ) ≤ ((75336939/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1871 :
    ((75342283/10000000 : ℚ) : ℝ) ≤ Real.log (1871 : ℕ)
      ∧ Real.log (1871 : ℕ) ≤ ((18835571/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1872 :
    ((37673813/5000000 : ℚ) : ℝ) ≤ Real.log (1872 : ℕ)
      ∧ Real.log (1872 : ℕ) ≤ ((75347627/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1873 :
    ((37676483/5000000 : ℚ) : ℝ) ≤ Real.log (1873 : ℕ)
      ∧ Real.log (1873 : ℕ) ≤ ((75352969/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1874 :
    ((2354947/312500 : ℚ) : ℝ) ≤ Real.log (1874 : ℕ)
      ∧ Real.log (1874 : ℕ) ≤ ((15071661/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1875 :
    ((75363639/10000000 : ℚ) : ℝ) ≤ Real.log (1875 : ℕ)
      ∧ Real.log (1875 : ℕ) ≤ ((1884091/250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1876 :
    ((75368971/10000000 : ℚ) : ℝ) ≤ Real.log (1876 : ℕ)
      ∧ Real.log (1876 : ℕ) ≤ ((18842243/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1877 :
    ((753743/100000 : ℚ) : ℝ) ≤ Real.log (1877 : ℕ)
      ∧ Real.log (1877 : ℕ) ≤ ((75374301/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1878 :
    ((37689813/5000000 : ℚ) : ℝ) ≤ Real.log (1878 : ℕ)
      ∧ Real.log (1878 : ℕ) ≤ ((75379627/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1879 :
    ((18846237/2500000 : ℚ) : ℝ) ≤ Real.log (1879 : ℕ)
      ∧ Real.log (1879 : ℕ) ≤ ((75384951/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1880 :
    ((7539027/1000000 : ℚ) : ℝ) ≤ Real.log (1880 : ℕ)
      ∧ Real.log (1880 : ℕ) ≤ ((75390271/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1881 :
    ((18848897/2500000 : ℚ) : ℝ) ≤ Real.log (1881 : ℕ)
      ∧ Real.log (1881 : ℕ) ≤ ((75395589/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1882 :
    ((75400903/10000000 : ℚ) : ℝ) ≤ Real.log (1882 : ℕ)
      ∧ Real.log (1882 : ℕ) ≤ ((9425113/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1883 :
    ((15081243/2000000 : ℚ) : ℝ) ≤ Real.log (1883 : ℕ)
      ∧ Real.log (1883 : ℕ) ≤ ((9425777/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1884 :
    ((18852881/2500000 : ℚ) : ℝ) ≤ Real.log (1884 : ℕ)
      ∧ Real.log (1884 : ℕ) ≤ ((3016461/400000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1885 :
    ((75416829/10000000 : ℚ) : ℝ) ≤ Real.log (1885 : ℕ)
      ∧ Real.log (1885 : ℕ) ≤ ((589194/78125 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1886 :
    ((37711067/5000000 : ℚ) : ℝ) ≤ Real.log (1886 : ℕ)
      ∧ Real.log (1886 : ℕ) ≤ ((15084427/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1887 :
    ((15085487/2000000 : ℚ) : ℝ) ≤ Real.log (1887 : ℕ)
      ∧ Real.log (1887 : ℕ) ≤ ((18856859/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1888 :
    ((75432733/10000000 : ℚ) : ℝ) ≤ Real.log (1888 : ℕ)
      ∧ Real.log (1888 : ℕ) ≤ ((37716367/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1889 :
    ((18859507/2500000 : ℚ) : ℝ) ≤ Real.log (1889 : ℕ)
      ∧ Real.log (1889 : ℕ) ≤ ((75438029/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1890 :
    ((75443321/10000000 : ℚ) : ℝ) ≤ Real.log (1890 : ℕ)
      ∧ Real.log (1890 : ℕ) ≤ ((37721661/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1891 :
    ((7544861/1000000 : ℚ) : ℝ) ≤ Real.log (1891 : ℕ)
      ∧ Real.log (1891 : ℕ) ≤ ((75448611/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1892 :
    ((75453897/10000000 : ℚ) : ℝ) ≤ Real.log (1892 : ℕ)
      ∧ Real.log (1892 : ℕ) ≤ ((37726949/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1893 :
    ((75459181/10000000 : ℚ) : ℝ) ≤ Real.log (1893 : ℕ)
      ∧ Real.log (1893 : ℕ) ≤ ((37729591/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1894 :
    ((37732231/5000000 : ℚ) : ℝ) ≤ Real.log (1894 : ℕ)
      ∧ Real.log (1894 : ℕ) ≤ ((75464463/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1895 :
    ((75469741/10000000 : ℚ) : ℝ) ≤ Real.log (1895 : ℕ)
      ∧ Real.log (1895 : ℕ) ≤ ((37734871/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1896 :
    ((9434377/1250000 : ℚ) : ℝ) ≤ Real.log (1896 : ℕ)
      ∧ Real.log (1896 : ℕ) ≤ ((75475017/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1897 :
    ((75480289/10000000 : ℚ) : ℝ) ≤ Real.log (1897 : ℕ)
      ∧ Real.log (1897 : ℕ) ≤ ((7548029/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1898 :
    ((75485559/10000000 : ℚ) : ℝ) ≤ Real.log (1898 : ℕ)
      ∧ Real.log (1898 : ℕ) ≤ ((1887139/250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1899 :
    ((75490827/10000000 : ℚ) : ℝ) ≤ Real.log (1899 : ℕ)
      ∧ Real.log (1899 : ℕ) ≤ ((18872707/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1900 :
    ((75496091/10000000 : ℚ) : ℝ) ≤ Real.log (1900 : ℕ)
      ∧ Real.log (1900 : ℕ) ≤ ((18874023/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1901 :
    ((75501353/10000000 : ℚ) : ℝ) ≤ Real.log (1901 : ℕ)
      ∧ Real.log (1901 : ℕ) ≤ ((37750677/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1902 :
    ((18876653/2500000 : ℚ) : ℝ) ≤ Real.log (1902 : ℕ)
      ∧ Real.log (1902 : ℕ) ≤ ((75506613/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1903 :
    ((18877967/2500000 : ℚ) : ℝ) ≤ Real.log (1903 : ℕ)
      ∧ Real.log (1903 : ℕ) ≤ ((75511869/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1904 :
    ((37758561/5000000 : ℚ) : ℝ) ≤ Real.log (1904 : ℕ)
      ∧ Real.log (1904 : ℕ) ≤ ((75517123/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1905 :
    ((18880593/2500000 : ℚ) : ℝ) ≤ Real.log (1905 : ℕ)
      ∧ Real.log (1905 : ℕ) ≤ ((75522373/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1906 :
    ((3776381/500000 : ℚ) : ℝ) ≤ Real.log (1906 : ℕ)
      ∧ Real.log (1906 : ℕ) ≤ ((75527621/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1907 :
    ((15106573/2000000 : ℚ) : ℝ) ≤ Real.log (1907 : ℕ)
      ∧ Real.log (1907 : ℕ) ≤ ((18883217/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1908 :
    ((18884527/2500000 : ℚ) : ℝ) ≤ Real.log (1908 : ℕ)
      ∧ Real.log (1908 : ℕ) ≤ ((75538109/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1909 :
    ((18885837/2500000 : ℚ) : ℝ) ≤ Real.log (1909 : ℕ)
      ∧ Real.log (1909 : ℕ) ≤ ((75543349/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1910 :
    ((15109717/2000000 : ℚ) : ℝ) ≤ Real.log (1910 : ℕ)
      ∧ Real.log (1910 : ℕ) ≤ ((37774293/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1911 :
    ((75553819/10000000 : ℚ) : ℝ) ≤ Real.log (1911 : ℕ)
      ∧ Real.log (1911 : ℕ) ≤ ((3777691/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1912 :
    ((1511181/200000 : ℚ) : ℝ) ≤ Real.log (1912 : ℕ)
      ∧ Real.log (1912 : ℕ) ≤ ((75559051/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1913 :
    ((75564279/10000000 : ℚ) : ℝ) ≤ Real.log (1913 : ℕ)
      ∧ Real.log (1913 : ℕ) ≤ ((1889107/250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1914 :
    ((15113901/2000000 : ℚ) : ℝ) ≤ Real.log (1914 : ℕ)
      ∧ Real.log (1914 : ℕ) ≤ ((37784753/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1915 :
    ((9446841/1250000 : ℚ) : ℝ) ≤ Real.log (1915 : ℕ)
      ∧ Real.log (1915 : ℕ) ≤ ((75574731/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1916 :
    ((75579949/10000000 : ℚ) : ℝ) ≤ Real.log (1916 : ℕ)
      ∧ Real.log (1916 : ℕ) ≤ ((1511599/200000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1917 :
    ((75585167/10000000 : ℚ) : ℝ) ≤ Real.log (1917 : ℕ)
      ∧ Real.log (1917 : ℕ) ≤ ((4724073/625000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1918 :
    ((37795191/5000000 : ℚ) : ℝ) ≤ Real.log (1918 : ℕ)
      ∧ Real.log (1918 : ℕ) ≤ ((75590383/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1919 :
    ((37797797/5000000 : ℚ) : ℝ) ≤ Real.log (1919 : ℕ)
      ∧ Real.log (1919 : ℕ) ≤ ((15119119/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1920 :
    ((18900201/2500000 : ℚ) : ℝ) ≤ Real.log (1920 : ℕ)
      ∧ Real.log (1920 : ℕ) ≤ ((15120161/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1921 :
    ((75606011/10000000 : ℚ) : ℝ) ≤ Real.log (1921 : ℕ)
      ∧ Real.log (1921 : ℕ) ≤ ((18901503/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1922 :
    ((15122243/2000000 : ℚ) : ℝ) ≤ Real.log (1922 : ℕ)
      ∧ Real.log (1922 : ℕ) ≤ ((4725701/625000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1923 :
    ((75616417/10000000 : ℚ) : ℝ) ≤ Real.log (1923 : ℕ)
      ∧ Real.log (1923 : ℕ) ≤ ((37808209/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1924 :
    ((4726351/625000 : ℚ) : ℝ) ≤ Real.log (1924 : ℕ)
      ∧ Real.log (1924 : ℕ) ≤ ((75621617/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1925 :
    ((18906703/2500000 : ℚ) : ℝ) ≤ Real.log (1925 : ℕ)
      ∧ Real.log (1925 : ℕ) ≤ ((75626813/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1926 :
    ((15126401/2000000 : ℚ) : ℝ) ≤ Real.log (1926 : ℕ)
      ∧ Real.log (1926 : ℕ) ≤ ((37816003/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1927 :
    ((18909299/2500000 : ℚ) : ℝ) ≤ Real.log (1927 : ℕ)
      ∧ Real.log (1927 : ℕ) ≤ ((75637197/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1928 :
    ((4727649/625000 : ℚ) : ℝ) ≤ Real.log (1928 : ℕ)
      ∧ Real.log (1928 : ℕ) ≤ ((15128477/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1929 :
    ((7564757/1000000 : ℚ) : ℝ) ≤ Real.log (1929 : ℕ)
      ∧ Real.log (1929 : ℕ) ≤ ((75647571/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1930 :
    ((4728297/625000 : ℚ) : ℝ) ≤ Real.log (1930 : ℕ)
      ∧ Real.log (1930 : ℕ) ≤ ((75652753/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1931 :
    ((18914483/2500000 : ℚ) : ℝ) ≤ Real.log (1931 : ℕ)
      ∧ Real.log (1931 : ℕ) ≤ ((75657933/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1932 :
    ((7566311/1000000 : ℚ) : ℝ) ≤ Real.log (1932 : ℕ)
      ∧ Real.log (1932 : ℕ) ≤ ((75663111/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1933 :
    ((18917071/2500000 : ℚ) : ℝ) ≤ Real.log (1933 : ℕ)
      ∧ Real.log (1933 : ℕ) ≤ ((15133657/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1934 :
    ((4729591/625000 : ℚ) : ℝ) ≤ Real.log (1934 : ℕ)
      ∧ Real.log (1934 : ℕ) ≤ ((75673457/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1935 :
    ((37839313/5000000 : ℚ) : ℝ) ≤ Real.log (1935 : ℕ)
      ∧ Real.log (1935 : ℕ) ≤ ((75678627/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1936 :
    ((4730237/625000 : ℚ) : ℝ) ≤ Real.log (1936 : ℕ)
      ∧ Real.log (1936 : ℕ) ≤ ((75683793/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1937 :
    ((18922239/2500000 : ℚ) : ℝ) ≤ Real.log (1937 : ℕ)
      ∧ Real.log (1937 : ℕ) ≤ ((75688957/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1938 :
    ((75694117/10000000 : ℚ) : ℝ) ≤ Real.log (1938 : ℕ)
      ∧ Real.log (1938 : ℕ) ≤ ((37847059/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1939 :
    ((18924819/2500000 : ℚ) : ℝ) ≤ Real.log (1939 : ℕ)
      ∧ Real.log (1939 : ℕ) ≤ ((75699277/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1940 :
    ((4731527/625000 : ℚ) : ℝ) ≤ Real.log (1940 : ℕ)
      ∧ Real.log (1940 : ℕ) ≤ ((75704433/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1941 :
    ((15141917/2000000 : ℚ) : ℝ) ≤ Real.log (1941 : ℕ)
      ∧ Real.log (1941 : ℕ) ≤ ((37854793/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1942 :
    ((4732171/625000 : ℚ) : ℝ) ≤ Real.log (1942 : ℕ)
      ∧ Real.log (1942 : ℕ) ≤ ((75714737/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1943 :
    ((18929971/2500000 : ℚ) : ℝ) ≤ Real.log (1943 : ℕ)
      ∧ Real.log (1943 : ℕ) ≤ ((15143977/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1944 :
    ((75725029/10000000 : ℚ) : ℝ) ≤ Real.log (1944 : ℕ)
      ∧ Real.log (1944 : ℕ) ≤ ((7572503/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1945 :
    ((18932543/2500000 : ℚ) : ℝ) ≤ Real.log (1945 : ℕ)
      ∧ Real.log (1945 : ℕ) ≤ ((75730173/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1946 :
    ((4733457/625000 : ℚ) : ℝ) ≤ Real.log (1946 : ℕ)
      ∧ Real.log (1946 : ℕ) ≤ ((75735313/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1947 :
    ((1514809/200000 : ℚ) : ℝ) ≤ Real.log (1947 : ℕ)
      ∧ Real.log (1947 : ℕ) ≤ ((75740451/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1948 :
    ((4734099/625000 : ℚ) : ℝ) ≤ Real.log (1948 : ℕ)
      ∧ Real.log (1948 : ℕ) ≤ ((15149117/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1949 :
    ((15150143/2000000 : ℚ) : ℝ) ≤ Real.log (1949 : ℕ)
      ∧ Real.log (1949 : ℕ) ≤ ((37875359/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1950 :
    ((37877923/5000000 : ℚ) : ℝ) ≤ Real.log (1950 : ℕ)
      ∧ Real.log (1950 : ℕ) ≤ ((75755847/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1951 :
    ((75760973/10000000 : ℚ) : ℝ) ≤ Real.log (1951 : ℕ)
      ∧ Real.log (1951 : ℕ) ≤ ((37880487/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1952 :
    ((75766097/10000000 : ℚ) : ℝ) ≤ Real.log (1952 : ℕ)
      ∧ Real.log (1952 : ℕ) ≤ ((37883049/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1953 :
    ((75771219/10000000 : ℚ) : ℝ) ≤ Real.log (1953 : ℕ)
      ∧ Real.log (1953 : ℕ) ≤ ((3788561/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1954 :
    ((37888169/5000000 : ℚ) : ℝ) ≤ Real.log (1954 : ℕ)
      ∧ Real.log (1954 : ℕ) ≤ ((75776339/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1955 :
    ((37890727/5000000 : ℚ) : ℝ) ≤ Real.log (1955 : ℕ)
      ∧ Real.log (1955 : ℕ) ≤ ((15156291/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1956 :
    ((9473321/1250000 : ℚ) : ℝ) ≤ Real.log (1956 : ℕ)
      ∧ Real.log (1956 : ℕ) ≤ ((75786569/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1957 :
    ((75791679/10000000 : ℚ) : ℝ) ≤ Real.log (1957 : ℕ)
      ∧ Real.log (1957 : ℕ) ≤ ((236849/31250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1958 :
    ((18949197/2500000 : ℚ) : ℝ) ≤ Real.log (1958 : ℕ)
      ∧ Real.log (1958 : ℕ) ≤ ((75796789/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1959 :
    ((37900947/5000000 : ℚ) : ℝ) ≤ Real.log (1959 : ℕ)
      ∧ Real.log (1959 : ℕ) ≤ ((15160379/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1960 :
    ((75806997/10000000 : ℚ) : ℝ) ≤ Real.log (1960 : ℕ)
      ∧ Real.log (1960 : ℕ) ≤ ((37903499/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1961 :
    ((37906049/5000000 : ℚ) : ℝ) ≤ Real.log (1961 : ℕ)
      ∧ Real.log (1961 : ℕ) ≤ ((75812099/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1962 :
    ((18954299/2500000 : ℚ) : ℝ) ≤ Real.log (1962 : ℕ)
      ∧ Real.log (1962 : ℕ) ≤ ((75817197/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1963 :
    ((75822291/10000000 : ℚ) : ℝ) ≤ Real.log (1963 : ℕ)
      ∧ Real.log (1963 : ℕ) ≤ ((18955573/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1964 :
    ((9478423/1250000 : ℚ) : ℝ) ≤ Real.log (1964 : ℕ)
      ∧ Real.log (1964 : ℕ) ≤ ((15165477/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1965 :
    ((3033299/400000 : ℚ) : ℝ) ≤ Real.log (1965 : ℕ)
      ∧ Real.log (1965 : ℕ) ≤ ((18958119/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1966 :
    ((37918781/5000000 : ℚ) : ℝ) ≤ Real.log (1966 : ℕ)
      ∧ Real.log (1966 : ℕ) ≤ ((15167513/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1967 :
    ((9480331/1250000 : ℚ) : ℝ) ≤ Real.log (1967 : ℕ)
      ∧ Real.log (1967 : ℕ) ≤ ((75842649/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1968 :
    ((7584773/1000000 : ℚ) : ℝ) ≤ Real.log (1968 : ℕ)
      ∧ Real.log (1968 : ℕ) ≤ ((75847731/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1969 :
    ((7585281/1000000 : ℚ) : ℝ) ≤ Real.log (1969 : ℕ)
      ∧ Real.log (1969 : ℕ) ≤ ((75852811/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1970 :
    ((2370559/312500 : ℚ) : ℝ) ≤ Real.log (1970 : ℕ)
      ∧ Real.log (1970 : ℕ) ≤ ((75857889/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1971 :
    ((75862963/10000000 : ℚ) : ℝ) ≤ Real.log (1971 : ℕ)
      ∧ Real.log (1971 : ℕ) ≤ ((18965741/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1972 :
    ((15173607/2000000 : ℚ) : ℝ) ≤ Real.log (1972 : ℕ)
      ∧ Real.log (1972 : ℕ) ≤ ((18967009/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1973 :
    ((15174621/2000000 : ℚ) : ℝ) ≤ Real.log (1973 : ℕ)
      ∧ Real.log (1973 : ℕ) ≤ ((37936553/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1974 :
    ((18969543/2500000 : ℚ) : ℝ) ≤ Real.log (1974 : ℕ)
      ∧ Real.log (1974 : ℕ) ≤ ((75878173/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1975 :
    ((18970809/2500000 : ℚ) : ℝ) ≤ Real.log (1975 : ℕ)
      ∧ Real.log (1975 : ℕ) ≤ ((75883237/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1976 :
    ((37944149/5000000 : ℚ) : ℝ) ≤ Real.log (1976 : ℕ)
      ∧ Real.log (1976 : ℕ) ≤ ((75888299/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1977 :
    ((37946679/5000000 : ℚ) : ℝ) ≤ Real.log (1977 : ℕ)
      ∧ Real.log (1977 : ℕ) ≤ ((75893359/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1978 :
    ((15179683/2000000 : ℚ) : ℝ) ≤ Real.log (1978 : ℕ)
      ∧ Real.log (1978 : ℕ) ≤ ((4743651/625000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1979 :
    ((75903469/10000000 : ℚ) : ℝ) ≤ Real.log (1979 : ℕ)
      ∧ Real.log (1979 : ℕ) ≤ ((7590347/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1980 :
    ((75908521/10000000 : ℚ) : ℝ) ≤ Real.log (1980 : ℕ)
      ∧ Real.log (1980 : ℕ) ≤ ((37954261/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1981 :
    ((7591357/1000000 : ℚ) : ℝ) ≤ Real.log (1981 : ℕ)
      ∧ Real.log (1981 : ℕ) ≤ ((75913571/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1982 :
    ((75918617/10000000 : ℚ) : ℝ) ≤ Real.log (1982 : ℕ)
      ∧ Real.log (1982 : ℕ) ≤ ((37959309/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1983 :
    ((75923661/10000000 : ℚ) : ℝ) ≤ Real.log (1983 : ℕ)
      ∧ Real.log (1983 : ℕ) ≤ ((37961831/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1984 :
    ((37964351/5000000 : ℚ) : ℝ) ≤ Real.log (1984 : ℕ)
      ∧ Real.log (1984 : ℕ) ≤ ((75928703/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1985 :
    ((75933741/10000000 : ℚ) : ℝ) ≤ Real.log (1985 : ℕ)
      ∧ Real.log (1985 : ℕ) ≤ ((37966871/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1986 :
    ((37969389/5000000 : ℚ) : ℝ) ≤ Real.log (1986 : ℕ)
      ∧ Real.log (1986 : ℕ) ≤ ((75938779/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1987 :
    ((18985953/2500000 : ℚ) : ℝ) ≤ Real.log (1987 : ℕ)
      ∧ Real.log (1987 : ℕ) ≤ ((75943813/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1988 :
    ((75948843/10000000 : ℚ) : ℝ) ≤ Real.log (1988 : ℕ)
      ∧ Real.log (1988 : ℕ) ≤ ((18987211/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1989 :
    ((4747117/625000 : ℚ) : ℝ) ≤ Real.log (1989 : ℕ)
      ∧ Real.log (1989 : ℕ) ≤ ((75953873/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1990 :
    ((75958899/10000000 : ℚ) : ℝ) ≤ Real.log (1990 : ℕ)
      ∧ Real.log (1990 : ℕ) ≤ ((759589/100000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1991 :
    ((75963923/10000000 : ℚ) : ℝ) ≤ Real.log (1991 : ℕ)
      ∧ Real.log (1991 : ℕ) ≤ ((18990981/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1992 :
    ((4748059/625000 : ℚ) : ℝ) ≤ Real.log (1992 : ℕ)
      ∧ Real.log (1992 : ℕ) ≤ ((15193789/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1993 :
    ((75973963/10000000 : ℚ) : ℝ) ≤ Real.log (1993 : ℕ)
      ∧ Real.log (1993 : ℕ) ≤ ((18993491/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1994 :
    ((75978979/10000000 : ℚ) : ℝ) ≤ Real.log (1994 : ℕ)
      ∧ Real.log (1994 : ℕ) ≤ ((3798949/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1995 :
    ((75983993/10000000 : ℚ) : ℝ) ≤ Real.log (1995 : ℕ)
      ∧ Real.log (1995 : ℕ) ≤ ((37991997/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1996 :
    ((18997251/2500000 : ℚ) : ℝ) ≤ Real.log (1996 : ℕ)
      ∧ Real.log (1996 : ℕ) ≤ ((15197801/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1997 :
    ((75994013/10000000 : ℚ) : ℝ) ≤ Real.log (1997 : ℕ)
      ∧ Real.log (1997 : ℕ) ≤ ((37997007/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1998 :
    ((75999019/10000000 : ℚ) : ℝ) ≤ Real.log (1998 : ℕ)
      ∧ Real.log (1998 : ℕ) ≤ ((3799951/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_1999 :
    ((76004023/10000000 : ℚ) : ℝ) ≤ Real.log (1999 : ℕ)
      ∧ Real.log (1999 : ℕ) ≤ ((9500503/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2000 :
    ((1187641/156250 : ℚ) : ℝ) ≤ Real.log (2000 : ℕ)
      ∧ Real.log (2000 : ℕ) ≤ ((3040361/400000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_br_2000
end AxiomAudit
