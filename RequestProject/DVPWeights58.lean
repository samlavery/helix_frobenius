import RequestProject.DVPLogBracket

/-!
# The algebraic weight brackets for the `t = 58` segment certificate

Seven-decimal rational brackets `qlo ≤ n^{−k/10} ≤ qhi` through
`rpow_neg_rat_bracket` — pure kernel arithmetic (`q^10·n^k` against `1`),
no transcendental content.  Covers every weight the six σ-interval
assemblies consume: the head terms `n = 2..10`, the Abel endpoints
`n = 11, 100`, and the Euler–Maclaurin cost exponents at `n = 100`.
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem wbr_2_5 :
    ((7071067/10000000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1767767/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_2_7 :
    ((3077861/5000000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((6155723/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_2_9 :
    ((5358867/10000000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1339717/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_2_11 :
    ((1166291/2500000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((933033/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_2_14 :
    ((3789291/10000000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((947323/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_2_17 :
    ((3077861/10000000 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((2 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1538931/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_7 :
    ((463463/1000000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((4634631/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_9 :
    ((372041/1000000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((3720411/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_11 :
    ((93329/312500 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2986529/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_14 :
    ((107399/500000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2147981/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_17 :
    ((386219/2500000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1544877/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_3_20 :
    ((1111111/10000000 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((3 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((138889/1250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_4_7 :
    ((3789291/10000000 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((947323/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_4_9 :
    ((574349/2000000 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1435873/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_4_11 :
    ((272047/1250000 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2176377/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_4_14 :
    ((44871/312500 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1435873/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_4_17 :
    ((473661/5000000 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((947323/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_4_20 :
    ((1/16 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((4 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((625001/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_5_7 :
    ((3241313/10000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1620657/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_5_9 :
    ((2349237/10000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1174619/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_5_11 :
    ((1702679/10000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((42567/250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_5_14 :
    ((1050611/10000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((262653/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_5_17 :
    ((324131/5000000 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((648263/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_5_20 :
    ((1/25 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((5 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((400001/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_5 :
    ((2041241/5000000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((4082483/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_7 :
    ((2852949/10000000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((57059/200000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_9 :
    ((996859/5000000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1993719/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_11 :
    ((87079/625000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((278653/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_14 :
    ((203483/2500000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((813933/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_6_17 :
    ((475491/10000000 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((6 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((118873/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_7 :
    ((320141/1250000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2561129/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_9 :
    ((216931/1250000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1735449/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_11 :
    ((587979/5000000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1175959/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_14 :
    ((655937/10000000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((327969/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_17 :
    ((2927/80000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((91469/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_7_20 :
    ((204081/10000000 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((7 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((102041/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_7 :
    ((1166291/5000000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2332583/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_9 :
    ((153893/1000000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1538931/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_11 :
    ((203063/2000000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((253829/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_14 :
    ((272047/5000000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((108819/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_17 :
    ((72893/2500000 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((291573/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_8_20 :
    ((1/64 : ℚ) : ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((8 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((156251/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_5 :
    ((3333333/10000000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1666667/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_7 :
    ((107399/500000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((2147981/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_9 :
    ((276829/2000000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((692073/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_11 :
    ((178387/2000000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((27873/312500 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_14 :
    ((461381/10000000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((230691/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_9_17 :
    ((29833/1250000 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((9 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((47733/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_5 :
    ((3162277/10000000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1581139/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_7 :
    ((997631/5000000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1995263/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_9 :
    ((50357/400000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((629463/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_11 :
    ((99291/1250000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((794329/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_14 :
    ((398107/10000000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((99527/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_10_17 :
    ((99763/5000000 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((10 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((199527/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_11_5 :
    ((3015113/10000000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((11 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1507557/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_11_7 :
    ((1866487/10000000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((11 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((233311/1250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_11_9 :
    ((1155437/10000000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((11 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((577719/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_11_11 :
    ((357633/5000000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((11 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((715267/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_11_14 :
    ((348377/10000000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((11 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((174189/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_11_17 :
    ((2121/125000 : ℚ) : ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((11 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((169681/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_5 :
    ((999999/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((5 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_7 :
    ((398107/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((99527/2500000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_9 :
    ((158489/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((15849/1000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_11 :
    ((12619/2000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((7887/1250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_14 :
    ((1981/1250000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((14 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((15849/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_15 :
    ((9999/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((15 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/1000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_17 :
    ((3981/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1991/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_19 :
    ((99/625000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((317/2000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_20 :
    ((999/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((20 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_21 :
    ((63/1000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((21 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((631/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_24 :
    ((79/5000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((24 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((159/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_25 :
    ((99/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((25 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/100000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_27 :
    ((39/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((27 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/250000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_29 :
    ((3/2000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((29 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/625000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_31 :
    ((3/5000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((31 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((7/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_34 :
    ((1/10000000 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((34 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/5000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem wbr_100_37 :
    ((0 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))
      ∧ ((100 : ℕ) : ℝ) ^ (-(((37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))) ≤ ((1/10000000 : ℚ) : ℝ) :=
  rpow_neg_rat_bracket (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.wbr_2_5
#print axioms CriticalLinePhasor.DVP.wbr_100_37
end AxiomAudit
