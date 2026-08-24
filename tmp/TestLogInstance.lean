import RequestProject.DVPLogBracket

open CriticalLinePhasor.DVP

/-- Test instance: `log 2` bracket via the packaged certificate. -/
theorem test_log_br_2 :
    ((6931471/10000000 : ℚ) : ℝ) ≤ Real.log (2 : ℕ)
      ∧ Real.log (2 : ℕ) ≤ ((433217/625000 : ℚ) : ℝ) :=
  log_bracket 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

#print axioms test_log_br_2
