import RequestProject.DVPLogBracket

/-!
# Natural-log brackets 2001-4000 (ultra-deep thin-gap support)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_2001 :
    ((760140233/100000000 : ℚ) : ℝ) ≤ Real.log (2001 : ℕ)
      ∧ Real.log (2001 : ℕ) ≤ ((380070117/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2002 :
    ((380095097/50000000 : ℚ) : ℝ) ≤ Real.log (2002 : ℕ)
      ∧ Real.log (2002 : ℕ) ≤ ((760190197/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2003 :
    ((760240133/100000000 : ℚ) : ℝ) ≤ Real.log (2003 : ℕ)
      ∧ Real.log (2003 : ℕ) ≤ ((380120067/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2004 :
    ((152058009/20000000 : ℚ) : ℝ) ≤ Real.log (2004 : ℕ)
      ∧ Real.log (2004 : ℕ) ≤ ((2969883/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2005 :
    ((190084983/25000000 : ℚ) : ℝ) ≤ Real.log (2005 : ℕ)
      ∧ Real.log (2005 : ℕ) ≤ ((152067987/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2006 :
    ((190097449/25000000 : ℚ) : ℝ) ≤ Real.log (2006 : ℕ)
      ∧ Real.log (2006 : ℕ) ≤ ((760389797/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2007 :
    ((380219817/50000000 : ℚ) : ℝ) ≤ Real.log (2007 : ℕ)
      ∧ Real.log (2007 : ℕ) ≤ ((152087927/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2008 :
    ((760489447/100000000 : ℚ) : ℝ) ≤ Real.log (2008 : ℕ)
      ∧ Real.log (2008 : ℕ) ≤ ((15209789/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2009 :
    ((190134809/25000000 : ℚ) : ℝ) ≤ Real.log (2009 : ℕ)
      ∧ Real.log (2009 : ℕ) ≤ ((760539237/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2010 :
    ((760588999/100000000 : ℚ) : ℝ) ≤ Real.log (2010 : ℕ)
      ∧ Real.log (2010 : ℕ) ≤ ((380294501/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2011 :
    ((760638737/100000000 : ℚ) : ℝ) ≤ Real.log (2011 : ℕ)
      ∧ Real.log (2011 : ℕ) ≤ ((38031937/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2012 :
    ((190172113/25000000 : ℚ) : ℝ) ≤ Real.log (2012 : ℕ)
      ∧ Real.log (2012 : ℕ) ≤ ((152137691/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2013 :
    ((380369071/50000000 : ℚ) : ℝ) ≤ Real.log (2013 : ℕ)
      ∧ Real.log (2013 : ℕ) ≤ ((760738143/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2014 :
    ((760787807/100000000 : ℚ) : ℝ) ≤ Real.log (2014 : ℕ)
      ∧ Real.log (2014 : ℕ) ≤ ((23774619/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2015 :
    ((760837447/100000000 : ℚ) : ℝ) ≤ Real.log (2015 : ℕ)
      ∧ Real.log (2015 : ℕ) ≤ ((95104681/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2016 :
    ((380443531/50000000 : ℚ) : ℝ) ≤ Real.log (2016 : ℕ)
      ∧ Real.log (2016 : ℕ) ≤ ((760887063/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2017 :
    ((760936653/100000000 : ℚ) : ℝ) ≤ Real.log (2017 : ℕ)
      ∧ Real.log (2017 : ℕ) ≤ ((380468327/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2018 :
    ((760986219/100000000 : ℚ) : ℝ) ≤ Real.log (2018 : ℕ)
      ∧ Real.log (2018 : ℕ) ≤ ((380493111/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2019 :
    ((761035761/100000000 : ℚ) : ℝ) ≤ Real.log (2019 : ℕ)
      ∧ Real.log (2019 : ℕ) ≤ ((380517881/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2020 :
    ((380542639/50000000 : ℚ) : ℝ) ≤ Real.log (2020 : ℕ)
      ∧ Real.log (2020 : ℕ) ≤ ((761085281/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2021 :
    ((761134771/100000000 : ℚ) : ℝ) ≤ Real.log (2021 : ℕ)
      ∧ Real.log (2021 : ℕ) ≤ ((190283693/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2022 :
    ((380592119/50000000 : ℚ) : ℝ) ≤ Real.log (2022 : ℕ)
      ∧ Real.log (2022 : ℕ) ≤ ((761184241/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2023 :
    ((761233683/100000000 : ℚ) : ℝ) ≤ Real.log (2023 : ℕ)
      ∧ Real.log (2023 : ℕ) ≤ ((190308421/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2024 :
    ((380641551/50000000 : ℚ) : ℝ) ≤ Real.log (2024 : ℕ)
      ∧ Real.log (2024 : ℕ) ≤ ((152256621/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2025 :
    ((47583281/6250000 : ℚ) : ℝ) ≤ Real.log (2025 : ℕ)
      ∧ Real.log (2025 : ℕ) ≤ ((761332499/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2026 :
    ((190345467/25000000 : ℚ) : ℝ) ≤ Real.log (2026 : ℕ)
      ∧ Real.log (2026 : ℕ) ≤ ((761381869/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2027 :
    ((380715607/50000000 : ℚ) : ℝ) ≤ Real.log (2027 : ℕ)
      ∧ Real.log (2027 : ℕ) ≤ ((152286243/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2028 :
    ((95185067/12500000 : ℚ) : ℝ) ≤ Real.log (2028 : ℕ)
      ∧ Real.log (2028 : ℕ) ≤ ((761480537/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2029 :
    ((95191229/12500000 : ℚ) : ℝ) ≤ Real.log (2029 : ℕ)
      ∧ Real.log (2029 : ℕ) ≤ ((152305967/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2030 :
    ((761579107/100000000 : ℚ) : ℝ) ≤ Real.log (2030 : ℕ)
      ∧ Real.log (2030 : ℕ) ≤ ((190394777/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2031 :
    ((152325671/20000000 : ℚ) : ℝ) ≤ Real.log (2031 : ℕ)
      ∧ Real.log (2031 : ℕ) ≤ ((380814179/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2032 :
    ((38083879/5000000 : ℚ) : ℝ) ≤ Real.log (2032 : ℕ)
      ∧ Real.log (2032 : ℕ) ≤ ((761677581/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2033 :
    ((761726781/100000000 : ℚ) : ℝ) ≤ Real.log (2033 : ℕ)
      ∧ Real.log (2033 : ℕ) ≤ ((380863391/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2034 :
    ((761775957/100000000 : ℚ) : ℝ) ≤ Real.log (2034 : ℕ)
      ∧ Real.log (2034 : ℕ) ≤ ((380887979/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2035 :
    ((761825109/100000000 : ℚ) : ℝ) ≤ Real.log (2035 : ℕ)
      ∧ Real.log (2035 : ℕ) ≤ ((76182511/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2036 :
    ((761874237/100000000 : ℚ) : ℝ) ≤ Real.log (2036 : ℕ)
      ∧ Real.log (2036 : ℕ) ≤ ((380937119/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2037 :
    ((761923341/100000000 : ℚ) : ℝ) ≤ Real.log (2037 : ℕ)
      ∧ Real.log (2037 : ℕ) ≤ ((380961671/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2038 :
    ((761972421/100000000 : ℚ) : ℝ) ≤ Real.log (2038 : ℕ)
      ∧ Real.log (2038 : ℕ) ≤ ((380986211/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2039 :
    ((190505369/25000000 : ℚ) : ℝ) ≤ Real.log (2039 : ℕ)
      ∧ Real.log (2039 : ℕ) ≤ ((762021479/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2040 :
    ((190517627/25000000 : ℚ) : ℝ) ≤ Real.log (2040 : ℕ)
      ∧ Real.log (2040 : ℕ) ≤ ((762070509/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2041 :
    ((190529879/25000000 : ℚ) : ℝ) ≤ Real.log (2041 : ℕ)
      ∧ Real.log (2041 : ℕ) ≤ ((762119517/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2042 :
    ((762168499/100000000 : ℚ) : ℝ) ≤ Real.log (2042 : ℕ)
      ∧ Real.log (2042 : ℕ) ≤ ((1524337/200000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2043 :
    ((762217459/100000000 : ℚ) : ℝ) ≤ Real.log (2043 : ℕ)
      ∧ Real.log (2043 : ℕ) ≤ ((38110873/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2044 :
    ((381133197/50000000 : ℚ) : ℝ) ≤ Real.log (2044 : ℕ)
      ∧ Real.log (2044 : ℕ) ≤ ((762266397/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2045 :
    ((381157653/50000000 : ℚ) : ℝ) ≤ Real.log (2045 : ℕ)
      ∧ Real.log (2045 : ℕ) ≤ ((762315307/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2046 :
    ((381182097/50000000 : ℚ) : ℝ) ≤ Real.log (2046 : ℕ)
      ∧ Real.log (2046 : ℕ) ≤ ((152472839/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2047 :
    ((381206529/50000000 : ℚ) : ℝ) ≤ Real.log (2047 : ℕ)
      ∧ Real.log (2047 : ℕ) ≤ ((762413059/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2048 :
    ((381230949/50000000 : ℚ) : ℝ) ≤ Real.log (2048 : ℕ)
      ∧ Real.log (2048 : ℕ) ≤ ((762461899/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2049 :
    ((381255357/50000000 : ℚ) : ℝ) ≤ Real.log (2049 : ℕ)
      ∧ Real.log (2049 : ℕ) ≤ ((152502143/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2050 :
    ((762559507/100000000 : ℚ) : ℝ) ≤ Real.log (2050 : ℕ)
      ∧ Real.log (2050 : ℕ) ≤ ((190639877/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2051 :
    ((30504331/4000000 : ℚ) : ℝ) ≤ Real.log (2051 : ℕ)
      ∧ Real.log (2051 : ℕ) ≤ ((190652069/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2052 :
    ((38132851/5000000 : ℚ) : ℝ) ≤ Real.log (2052 : ℕ)
      ∧ Real.log (2052 : ℕ) ≤ ((762657021/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2053 :
    ((762705741/100000000 : ℚ) : ℝ) ≤ Real.log (2053 : ℕ)
      ∧ Real.log (2053 : ℕ) ≤ ((381352871/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2054 :
    ((381377219/50000000 : ℚ) : ℝ) ≤ Real.log (2054 : ℕ)
      ∧ Real.log (2054 : ℕ) ≤ ((762754441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2055 :
    ((95350389/12500000 : ℚ) : ℝ) ≤ Real.log (2055 : ℕ)
      ∧ Real.log (2055 : ℕ) ≤ ((762803113/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2056 :
    ((381425881/50000000 : ℚ) : ℝ) ≤ Real.log (2056 : ℕ)
      ∧ Real.log (2056 : ℕ) ≤ ((762851763/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2057 :
    ((762900387/100000000 : ℚ) : ℝ) ≤ Real.log (2057 : ℕ)
      ∧ Real.log (2057 : ℕ) ≤ ((76290039/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2058 :
    ((762948991/100000000 : ℚ) : ℝ) ≤ Real.log (2058 : ℕ)
      ∧ Real.log (2058 : ℕ) ≤ ((5960539/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2059 :
    ((76299757/10000000 : ℚ) : ℝ) ≤ Real.log (2059 : ℕ)
      ∧ Real.log (2059 : ℕ) ≤ ((762997571/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2060 :
    ((381523063/50000000 : ℚ) : ℝ) ≤ Real.log (2060 : ℕ)
      ∧ Real.log (2060 : ℕ) ≤ ((763046127/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2061 :
    ((763094657/100000000 : ℚ) : ℝ) ≤ Real.log (2061 : ℕ)
      ∧ Real.log (2061 : ℕ) ≤ ((38154733/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2062 :
    ((381571583/50000000 : ℚ) : ℝ) ≤ Real.log (2062 : ℕ)
      ∧ Real.log (2062 : ℕ) ≤ ((763143167/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2063 :
    ((763191651/100000000 : ℚ) : ℝ) ≤ Real.log (2063 : ℕ)
      ∧ Real.log (2063 : ℕ) ≤ ((190797913/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2064 :
    ((47702507/6250000 : ℚ) : ℝ) ≤ Real.log (2064 : ℕ)
      ∧ Real.log (2064 : ℕ) ≤ ((763240113/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2065 :
    ((15265771/2000000 : ℚ) : ℝ) ≤ Real.log (2065 : ℕ)
      ∧ Real.log (2065 : ℕ) ≤ ((763288551/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2066 :
    ((763336963/100000000 : ℚ) : ℝ) ≤ Real.log (2066 : ℕ)
      ∧ Real.log (2066 : ℕ) ≤ ((381668483/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2067 :
    ((381692677/50000000 : ℚ) : ℝ) ≤ Real.log (2067 : ℕ)
      ∧ Real.log (2067 : ℕ) ≤ ((763385357/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2068 :
    ((763433723/100000000 : ℚ) : ℝ) ≤ Real.log (2068 : ℕ)
      ∧ Real.log (2068 : ℕ) ≤ ((190858431/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2069 :
    ((763482067/100000000 : ℚ) : ℝ) ≤ Real.log (2069 : ℕ)
      ∧ Real.log (2069 : ℕ) ≤ ((190870517/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2070 :
    ((190882597/25000000 : ℚ) : ℝ) ≤ Real.log (2070 : ℕ)
      ∧ Real.log (2070 : ℕ) ≤ ((763530389/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2071 :
    ((381789343/50000000 : ℚ) : ℝ) ≤ Real.log (2071 : ℕ)
      ∧ Real.log (2071 : ℕ) ≤ ((763578687/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2072 :
    ((9545337/1250000 : ℚ) : ℝ) ≤ Real.log (2072 : ℕ)
      ∧ Real.log (2072 : ℕ) ≤ ((763626961/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2073 :
    ((763675211/100000000 : ℚ) : ℝ) ≤ Real.log (2073 : ℕ)
      ∧ Real.log (2073 : ℕ) ≤ ((190918803/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2074 :
    ((381861719/50000000 : ℚ) : ℝ) ≤ Real.log (2074 : ℕ)
      ∧ Real.log (2074 : ℕ) ≤ ((763723439/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2075 :
    ((763771643/100000000 : ℚ) : ℝ) ≤ Real.log (2075 : ℕ)
      ∧ Real.log (2075 : ℕ) ≤ ((190942911/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2076 :
    ((47738739/6250000 : ℚ) : ℝ) ≤ Real.log (2076 : ℕ)
      ∧ Real.log (2076 : ℕ) ≤ ((30552793/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2077 :
    ((381933991/50000000 : ℚ) : ℝ) ≤ Real.log (2077 : ℕ)
      ∧ Real.log (2077 : ℕ) ≤ ((763867983/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2078 :
    ((763916117/100000000 : ℚ) : ℝ) ≤ Real.log (2078 : ℕ)
      ∧ Real.log (2078 : ℕ) ≤ ((381958059/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2079 :
    ((190991057/25000000 : ℚ) : ℝ) ≤ Real.log (2079 : ℕ)
      ∧ Real.log (2079 : ℕ) ≤ ((763964229/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2080 :
    ((764012317/100000000 : ℚ) : ℝ) ≤ Real.log (2080 : ℕ)
      ∧ Real.log (2080 : ℕ) ≤ ((382006159/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2081 :
    ((382030191/50000000 : ℚ) : ℝ) ≤ Real.log (2081 : ℕ)
      ∧ Real.log (2081 : ℕ) ≤ ((764060383/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2082 :
    ((95513553/12500000 : ℚ) : ℝ) ≤ Real.log (2082 : ℕ)
      ∧ Real.log (2082 : ℕ) ≤ ((30564337/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2083 :
    ((191039111/25000000 : ℚ) : ℝ) ≤ Real.log (2083 : ℕ)
      ∧ Real.log (2083 : ℕ) ≤ ((152831289/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2084 :
    ((19105111/2500000 : ℚ) : ℝ) ≤ Real.log (2084 : ℕ)
      ∧ Real.log (2084 : ℕ) ≤ ((764204441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2085 :
    ((764252413/100000000 : ℚ) : ℝ) ≤ Real.log (2085 : ℕ)
      ∧ Real.log (2085 : ℕ) ≤ ((382126207/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2086 :
    ((764300363/100000000 : ℚ) : ℝ) ≤ Real.log (2086 : ℕ)
      ∧ Real.log (2086 : ℕ) ≤ ((191075091/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2087 :
    ((76434829/10000000 : ℚ) : ℝ) ≤ Real.log (2087 : ℕ)
      ∧ Real.log (2087 : ℕ) ≤ ((764348291/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2088 :
    ((382198097/50000000 : ℚ) : ℝ) ≤ Real.log (2088 : ℕ)
      ∧ Real.log (2088 : ℕ) ≤ ((152879239/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2089 :
    ((191111019/25000000 : ℚ) : ℝ) ≤ Real.log (2089 : ℕ)
      ∧ Real.log (2089 : ℕ) ≤ ((764444077/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2090 :
    ((382245967/50000000 : ℚ) : ℝ) ≤ Real.log (2090 : ℕ)
      ∧ Real.log (2090 : ℕ) ≤ ((152898387/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2091 :
    ((764539769/100000000 : ℚ) : ℝ) ≤ Real.log (2091 : ℕ)
      ∧ Real.log (2091 : ℕ) ≤ ((76453977/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2092 :
    ((382293791/50000000 : ℚ) : ℝ) ≤ Real.log (2092 : ℕ)
      ∧ Real.log (2092 : ℕ) ≤ ((764587583/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2093 :
    ((191158843/25000000 : ℚ) : ℝ) ≤ Real.log (2093 : ℕ)
      ∧ Real.log (2093 : ℕ) ≤ ((764635373/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2094 :
    ((764683139/100000000 : ℚ) : ℝ) ≤ Real.log (2094 : ℕ)
      ∧ Real.log (2094 : ℕ) ≤ ((38234157/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2095 :
    ((764730883/100000000 : ℚ) : ℝ) ≤ Real.log (2095 : ℕ)
      ∧ Real.log (2095 : ℕ) ≤ ((191182721/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2096 :
    ((191194651/25000000 : ℚ) : ℝ) ≤ Real.log (2096 : ℕ)
      ∧ Real.log (2096 : ℕ) ≤ ((152955721/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2097 :
    ((382413151/50000000 : ℚ) : ℝ) ≤ Real.log (2097 : ℕ)
      ∧ Real.log (2097 : ℕ) ≤ ((152965261/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2098 :
    ((382436989/50000000 : ℚ) : ℝ) ≤ Real.log (2098 : ℕ)
      ∧ Real.log (2098 : ℕ) ≤ ((764873979/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2099 :
    ((76492163/10000000 : ℚ) : ℝ) ≤ Real.log (2099 : ℕ)
      ∧ Real.log (2099 : ℕ) ≤ ((764921633/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2100 :
    ((382484631/50000000 : ℚ) : ℝ) ≤ Real.log (2100 : ℕ)
      ∧ Real.log (2100 : ℕ) ≤ ((764969263/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2101 :
    ((765016869/100000000 : ℚ) : ℝ) ≤ Real.log (2101 : ℕ)
      ∧ Real.log (2101 : ℕ) ≤ ((95627109/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2102 :
    ((153012891/20000000 : ℚ) : ℝ) ≤ Real.log (2102 : ℕ)
      ∧ Real.log (2102 : ℕ) ≤ ((95633057/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2103 :
    ((765112017/100000000 : ℚ) : ℝ) ≤ Real.log (2103 : ℕ)
      ∧ Real.log (2103 : ℕ) ≤ ((382556009/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2104 :
    ((765159557/100000000 : ℚ) : ℝ) ≤ Real.log (2104 : ℕ)
      ∧ Real.log (2104 : ℕ) ≤ ((382579779/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2105 :
    ((382603537/50000000 : ℚ) : ℝ) ≤ Real.log (2105 : ℕ)
      ∧ Real.log (2105 : ℕ) ≤ ((30608283/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2106 :
    ((765254569/100000000 : ℚ) : ℝ) ≤ Real.log (2106 : ℕ)
      ∧ Real.log (2106 : ℕ) ≤ ((76525457/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2107 :
    ((765302041/100000000 : ℚ) : ℝ) ≤ Real.log (2107 : ℕ)
      ∧ Real.log (2107 : ℕ) ≤ ((382651021/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2108 :
    ((765349489/100000000 : ℚ) : ℝ) ≤ Real.log (2108 : ℕ)
      ∧ Real.log (2108 : ℕ) ≤ ((191337373/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2109 :
    ((765396917/100000000 : ℚ) : ℝ) ≤ Real.log (2109 : ℕ)
      ∧ Real.log (2109 : ℕ) ≤ ((19134923/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2110 :
    ((382722161/50000000 : ℚ) : ℝ) ≤ Real.log (2110 : ℕ)
      ∧ Real.log (2110 : ℕ) ≤ ((765444323/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2111 :
    ((95686463/12500000 : ℚ) : ℝ) ≤ Real.log (2111 : ℕ)
      ∧ Real.log (2111 : ℕ) ≤ ((153098341/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2112 :
    ((95692383/12500000 : ℚ) : ℝ) ≤ Real.log (2112 : ℕ)
      ∧ Real.log (2112 : ℕ) ≤ ((153107813/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2113 :
    ((765586401/100000000 : ℚ) : ℝ) ≤ Real.log (2113 : ℕ)
      ∧ Real.log (2113 : ℕ) ≤ ((382793201/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2114 :
    ((191408429/25000000 : ℚ) : ℝ) ≤ Real.log (2114 : ℕ)
      ∧ Real.log (2114 : ℕ) ≤ ((765633717/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2115 :
    ((765681009/100000000 : ℚ) : ℝ) ≤ Real.log (2115 : ℕ)
      ∧ Real.log (2115 : ℕ) ≤ ((76568101/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2116 :
    ((765728279/100000000 : ℚ) : ℝ) ≤ Real.log (2116 : ℕ)
      ∧ Real.log (2116 : ℕ) ≤ ((19143207/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2117 :
    ((765775527/100000000 : ℚ) : ℝ) ≤ Real.log (2117 : ℕ)
      ∧ Real.log (2117 : ℕ) ≤ ((95721941/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2118 :
    ((23931961/3125000 : ℚ) : ℝ) ≤ Real.log (2118 : ℕ)
      ∧ Real.log (2118 : ℕ) ≤ ((765822753/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2119 :
    ((153173991/20000000 : ℚ) : ℝ) ≤ Real.log (2119 : ℕ)
      ∧ Real.log (2119 : ℕ) ≤ ((191467489/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2120 :
    ((47869821/6250000 : ℚ) : ℝ) ≤ Real.log (2120 : ℕ)
      ∧ Real.log (2120 : ℕ) ≤ ((765917137/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2121 :
    ((153192859/20000000 : ℚ) : ℝ) ≤ Real.log (2121 : ℕ)
      ∧ Real.log (2121 : ℕ) ≤ ((95745537/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2122 :
    ((766011431/100000000 : ℚ) : ℝ) ≤ Real.log (2122 : ℕ)
      ∧ Real.log (2122 : ℕ) ≤ ((95751429/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2123 :
    ((383029273/50000000 : ℚ) : ℝ) ≤ Real.log (2123 : ℕ)
      ∧ Real.log (2123 : ℕ) ≤ ((766058547/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2124 :
    ((383052819/50000000 : ℚ) : ℝ) ≤ Real.log (2124 : ℕ)
      ∧ Real.log (2124 : ℕ) ≤ ((766105639/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2125 :
    ((191538177/25000000 : ℚ) : ℝ) ≤ Real.log (2125 : ℕ)
      ∧ Real.log (2125 : ℕ) ≤ ((766152709/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2126 :
    ((153239951/20000000 : ℚ) : ℝ) ≤ Real.log (2126 : ℕ)
      ∧ Real.log (2126 : ℕ) ≤ ((191549939/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2127 :
    ((766246781/100000000 : ℚ) : ℝ) ≤ Real.log (2127 : ℕ)
      ∧ Real.log (2127 : ℕ) ≤ ((383123391/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2128 :
    ((95786723/12500000 : ℚ) : ℝ) ≤ Real.log (2128 : ℕ)
      ∧ Real.log (2128 : ℕ) ≤ ((766293787/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2129 :
    ((383170383/50000000 : ℚ) : ℝ) ≤ Real.log (2129 : ℕ)
      ∧ Real.log (2129 : ℕ) ≤ ((766340767/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2130 :
    ((30655509/4000000 : ℚ) : ℝ) ≤ Real.log (2130 : ℕ)
      ∧ Real.log (2130 : ℕ) ≤ ((383193863/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2131 :
    ((766434663/100000000 : ℚ) : ℝ) ≤ Real.log (2131 : ℕ)
      ∧ Real.log (2131 : ℕ) ≤ ((95804333/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2132 :
    ((383240789/50000000 : ℚ) : ℝ) ≤ Real.log (2132 : ℕ)
      ∧ Real.log (2132 : ℕ) ≤ ((766481579/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2133 :
    ((766528471/100000000 : ℚ) : ℝ) ≤ Real.log (2133 : ℕ)
      ∧ Real.log (2133 : ℕ) ≤ ((95816059/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2134 :
    ((766575343/100000000 : ℚ) : ℝ) ≤ Real.log (2134 : ℕ)
      ∧ Real.log (2134 : ℕ) ≤ ((47910959/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2135 :
    ((47913887/6250000 : ℚ) : ℝ) ≤ Real.log (2135 : ℕ)
      ∧ Real.log (2135 : ℕ) ≤ ((766622193/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2136 :
    ((766669019/100000000 : ℚ) : ℝ) ≤ Real.log (2136 : ℕ)
      ∧ Real.log (2136 : ℕ) ≤ ((383334511/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2137 :
    ((30668633/4000000 : ℚ) : ℝ) ≤ Real.log (2137 : ℕ)
      ∧ Real.log (2137 : ℕ) ≤ ((383357913/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2138 :
    ((766762609/100000000 : ℚ) : ℝ) ≤ Real.log (2138 : ℕ)
      ∧ Real.log (2138 : ℕ) ≤ ((76676261/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2139 :
    ((76680937/10000000 : ℚ) : ℝ) ≤ Real.log (2139 : ℕ)
      ∧ Real.log (2139 : ℕ) ≤ ((766809371/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2140 :
    ((76685611/10000000 : ℚ) : ℝ) ≤ Real.log (2140 : ℕ)
      ∧ Real.log (2140 : ℕ) ≤ ((766856111/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2141 :
    ((191725707/25000000 : ℚ) : ℝ) ≤ Real.log (2141 : ℕ)
      ∧ Real.log (2141 : ℕ) ≤ ((766902829/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2142 :
    ((30677981/4000000 : ℚ) : ℝ) ≤ Real.log (2142 : ℕ)
      ∧ Real.log (2142 : ℕ) ≤ ((383474763/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2143 :
    ((766996199/100000000 : ℚ) : ℝ) ≤ Real.log (2143 : ℕ)
      ∧ Real.log (2143 : ℕ) ≤ ((3834981/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2144 :
    ((191760713/25000000 : ℚ) : ℝ) ≤ Real.log (2144 : ℕ)
      ∧ Real.log (2144 : ℕ) ≤ ((767042853/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2145 :
    ((767089483/100000000 : ℚ) : ℝ) ≤ Real.log (2145 : ℕ)
      ∧ Real.log (2145 : ℕ) ≤ ((191772371/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2146 :
    ((191784023/25000000 : ℚ) : ℝ) ≤ Real.log (2146 : ℕ)
      ∧ Real.log (2146 : ℕ) ≤ ((767136093/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2147 :
    ((767182679/100000000 : ℚ) : ℝ) ≤ Real.log (2147 : ℕ)
      ∧ Real.log (2147 : ℕ) ≤ ((19179567/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2148 :
    ((153445849/20000000 : ℚ) : ℝ) ≤ Real.log (2148 : ℕ)
      ∧ Real.log (2148 : ℕ) ≤ ((383614623/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2149 :
    ((767275789/100000000 : ℚ) : ℝ) ≤ Real.log (2149 : ℕ)
      ∧ Real.log (2149 : ℕ) ≤ ((76727579/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2150 :
    ((95915289/12500000 : ℚ) : ℝ) ≤ Real.log (2150 : ℕ)
      ∧ Real.log (2150 : ℕ) ≤ ((767322313/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2151 :
    ((191842203/25000000 : ℚ) : ℝ) ≤ Real.log (2151 : ℕ)
      ∧ Real.log (2151 : ℕ) ≤ ((767368813/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2152 :
    ((191853823/25000000 : ℚ) : ℝ) ≤ Real.log (2152 : ℕ)
      ∧ Real.log (2152 : ℕ) ≤ ((767415293/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2153 :
    ((767461749/100000000 : ℚ) : ℝ) ≤ Real.log (2153 : ℕ)
      ∧ Real.log (2153 : ℕ) ≤ ((3069847/400000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2154 :
    ((153501637/20000000 : ℚ) : ℝ) ≤ Real.log (2154 : ℕ)
      ∧ Real.log (2154 : ℕ) ≤ ((383754093/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2155 :
    ((3837773/500000 : ℚ) : ℝ) ≤ Real.log (2155 : ℕ)
      ∧ Real.log (2155 : ℕ) ≤ ((767554601/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2156 :
    ((767600993/100000000 : ℚ) : ℝ) ≤ Real.log (2156 : ℕ)
      ∧ Real.log (2156 : ℕ) ≤ ((383800497/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2157 :
    ((191911841/25000000 : ℚ) : ℝ) ≤ Real.log (2157 : ℕ)
      ∧ Real.log (2157 : ℕ) ≤ ((153529473/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2158 :
    ((383846857/50000000 : ℚ) : ℝ) ≤ Real.log (2158 : ℕ)
      ∧ Real.log (2158 : ℕ) ≤ ((153538743/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2159 :
    ((383870021/50000000 : ℚ) : ℝ) ≤ Real.log (2159 : ℕ)
      ∧ Real.log (2159 : ℕ) ≤ ((153548009/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2160 :
    ((767786349/100000000 : ℚ) : ℝ) ≤ Real.log (2160 : ℕ)
      ∧ Real.log (2160 : ℕ) ≤ ((47986647/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2161 :
    ((153566527/20000000 : ℚ) : ℝ) ≤ Real.log (2161 : ℕ)
      ∧ Real.log (2161 : ℕ) ≤ ((191958159/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2162 :
    ((767878899/100000000 : ℚ) : ℝ) ≤ Real.log (2162 : ℕ)
      ∧ Real.log (2162 : ℕ) ≤ ((7678789/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2163 :
    ((383962571/50000000 : ℚ) : ℝ) ≤ Real.log (2163 : ℕ)
      ∧ Real.log (2163 : ℕ) ≤ ((767925143/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2164 :
    ((383985681/50000000 : ℚ) : ℝ) ≤ Real.log (2164 : ℕ)
      ∧ Real.log (2164 : ℕ) ≤ ((153594273/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2165 :
    ((768017563/100000000 : ℚ) : ℝ) ≤ Real.log (2165 : ℕ)
      ∧ Real.log (2165 : ℕ) ≤ ((384008783/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2166 :
    ((384031871/50000000 : ℚ) : ℝ) ≤ Real.log (2166 : ℕ)
      ∧ Real.log (2166 : ℕ) ≤ ((768063743/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2167 :
    ((7681099/1000000 : ℚ) : ℝ) ≤ Real.log (2167 : ℕ)
      ∧ Real.log (2167 : ℕ) ≤ ((768109901/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2168 :
    ((192039009/25000000 : ℚ) : ℝ) ≤ Real.log (2168 : ℕ)
      ∧ Real.log (2168 : ℕ) ≤ ((768156037/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2169 :
    ((768202151/100000000 : ℚ) : ℝ) ≤ Real.log (2169 : ℕ)
      ∧ Real.log (2169 : ℕ) ≤ ((96025269/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2170 :
    ((192062061/25000000 : ℚ) : ℝ) ≤ Real.log (2170 : ℕ)
      ∧ Real.log (2170 : ℕ) ≤ ((153649649/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2171 :
    ((153658863/20000000 : ℚ) : ℝ) ≤ Real.log (2171 : ℕ)
      ∧ Real.log (2171 : ℕ) ≤ ((384147159/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2172 :
    ((48021273/6250000 : ℚ) : ℝ) ≤ Real.log (2172 : ℕ)
      ∧ Real.log (2172 : ℕ) ≤ ((768340369/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2173 :
    ((768386397/100000000 : ℚ) : ℝ) ≤ Real.log (2173 : ℕ)
      ∧ Real.log (2173 : ℕ) ≤ ((960483/125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2174 :
    ((384216203/50000000 : ℚ) : ℝ) ≤ Real.log (2174 : ℕ)
      ∧ Real.log (2174 : ℕ) ≤ ((768432407/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2175 :
    ((384239197/50000000 : ℚ) : ℝ) ≤ Real.log (2175 : ℕ)
      ∧ Real.log (2175 : ℕ) ≤ ((153695679/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2176 :
    ((19213109/2500000 : ℚ) : ℝ) ≤ Real.log (2176 : ℕ)
      ∧ Real.log (2176 : ℕ) ≤ ((768524361/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2177 :
    ((384285153/50000000 : ℚ) : ℝ) ≤ Real.log (2177 : ℕ)
      ∧ Real.log (2177 : ℕ) ≤ ((768570307/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2178 :
    ((76861623/10000000 : ℚ) : ℝ) ≤ Real.log (2178 : ℕ)
      ∧ Real.log (2178 : ℕ) ≤ ((768616231/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2179 :
    ((768662133/100000000 : ℚ) : ℝ) ≤ Real.log (2179 : ℕ)
      ∧ Real.log (2179 : ℕ) ≤ ((384331067/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2180 :
    ((153741603/20000000 : ℚ) : ℝ) ≤ Real.log (2180 : ℕ)
      ∧ Real.log (2180 : ℕ) ≤ ((48044251/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2181 :
    ((192188469/25000000 : ℚ) : ℝ) ≤ Real.log (2181 : ℕ)
      ∧ Real.log (2181 : ℕ) ≤ ((768753877/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2182 :
    ((192199929/25000000 : ℚ) : ℝ) ≤ Real.log (2182 : ℕ)
      ∧ Real.log (2182 : ℕ) ≤ ((768799717/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2183 :
    ((153769107/20000000 : ℚ) : ℝ) ≤ Real.log (2183 : ℕ)
      ∧ Real.log (2183 : ℕ) ≤ ((24026423/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2184 :
    ((768891333/100000000 : ℚ) : ℝ) ≤ Real.log (2184 : ℕ)
      ∧ Real.log (2184 : ℕ) ≤ ((384445667/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2185 :
    ((76893711/10000000 : ℚ) : ℝ) ≤ Real.log (2185 : ℕ)
      ∧ Real.log (2185 : ℕ) ≤ ((768937111/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2186 :
    ((384491433/50000000 : ℚ) : ℝ) ≤ Real.log (2186 : ℕ)
      ∧ Real.log (2186 : ℕ) ≤ ((768982867/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2187 :
    ((384514301/50000000 : ℚ) : ℝ) ≤ Real.log (2187 : ℕ)
      ∧ Real.log (2187 : ℕ) ≤ ((769028603/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2188 :
    ((192268579/25000000 : ℚ) : ℝ) ≤ Real.log (2188 : ℕ)
      ∧ Real.log (2188 : ℕ) ≤ ((769074317/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2189 :
    ((769120009/100000000 : ℚ) : ℝ) ≤ Real.log (2189 : ℕ)
      ∧ Real.log (2189 : ℕ) ≤ ((76912001/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2190 :
    ((384582841/50000000 : ℚ) : ℝ) ≤ Real.log (2190 : ℕ)
      ∧ Real.log (2190 : ℕ) ≤ ((769165683/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2191 :
    ((192302833/25000000 : ℚ) : ℝ) ≤ Real.log (2191 : ℕ)
      ∧ Real.log (2191 : ℕ) ≤ ((153842267/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2192 :
    ((192314241/25000000 : ℚ) : ℝ) ≤ Real.log (2192 : ℕ)
      ∧ Real.log (2192 : ℕ) ≤ ((153851393/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2193 :
    ((384651287/50000000 : ℚ) : ℝ) ≤ Real.log (2193 : ℕ)
      ∧ Real.log (2193 : ℕ) ≤ ((30772103/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2194 :
    ((192337041/25000000 : ℚ) : ℝ) ≤ Real.log (2194 : ℕ)
      ∧ Real.log (2194 : ℕ) ≤ ((153869633/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2195 :
    ((192348433/25000000 : ℚ) : ℝ) ≤ Real.log (2195 : ℕ)
      ∧ Real.log (2195 : ℕ) ≤ ((769393733/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2196 :
    ((9617991/1250000 : ℚ) : ℝ) ≤ Real.log (2196 : ℕ)
      ∧ Real.log (2196 : ℕ) ≤ ((769439281/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2197 :
    ((769484807/100000000 : ℚ) : ℝ) ≤ Real.log (2197 : ℕ)
      ∧ Real.log (2197 : ℕ) ≤ ((96185601/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2198 :
    ((769530313/100000000 : ℚ) : ℝ) ≤ Real.log (2198 : ℕ)
      ∧ Real.log (2198 : ℕ) ≤ ((384765157/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2199 :
    ((384787899/50000000 : ℚ) : ℝ) ≤ Real.log (2199 : ℕ)
      ∧ Real.log (2199 : ℕ) ≤ ((769575801/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2200 :
    ((769621263/100000000 : ℚ) : ℝ) ≤ Real.log (2200 : ℕ)
      ∧ Real.log (2200 : ℕ) ≤ ((48101329/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2201 :
    ((192416677/25000000 : ℚ) : ℝ) ≤ Real.log (2201 : ℕ)
      ∧ Real.log (2201 : ℕ) ≤ ((769666709/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2202 :
    ((769712131/100000000 : ℚ) : ℝ) ≤ Real.log (2202 : ℕ)
      ∧ Real.log (2202 : ℕ) ≤ ((192428033/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2203 :
    ((384878767/50000000 : ℚ) : ℝ) ≤ Real.log (2203 : ℕ)
      ∧ Real.log (2203 : ℕ) ≤ ((153951507/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2204 :
    ((192450729/25000000 : ℚ) : ℝ) ≤ Real.log (2204 : ℕ)
      ∧ Real.log (2204 : ℕ) ≤ ((769802919/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2205 :
    ((384924139/50000000 : ℚ) : ℝ) ≤ Real.log (2205 : ℕ)
      ∧ Real.log (2205 : ℕ) ≤ ((769848279/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2206 :
    ((384946809/50000000 : ℚ) : ℝ) ≤ Real.log (2206 : ℕ)
      ∧ Real.log (2206 : ℕ) ≤ ((769893621/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2207 :
    ((38496947/5000000 : ℚ) : ℝ) ≤ Real.log (2207 : ℕ)
      ∧ Real.log (2207 : ℕ) ≤ ((769938941/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2208 :
    ((9624803/1250000 : ℚ) : ℝ) ≤ Real.log (2208 : ℕ)
      ∧ Real.log (2208 : ℕ) ≤ ((769984241/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2209 :
    ((9625369/1250000 : ℚ) : ℝ) ≤ Real.log (2209 : ℕ)
      ∧ Real.log (2209 : ℕ) ≤ ((770029521/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2210 :
    ((770074779/100000000 : ℚ) : ℝ) ≤ Real.log (2210 : ℕ)
      ∧ Real.log (2210 : ℕ) ≤ ((38503739/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2211 :
    ((385060009/50000000 : ℚ) : ℝ) ≤ Real.log (2211 : ℕ)
      ∧ Real.log (2211 : ℕ) ≤ ((770120019/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2212 :
    ((192541309/25000000 : ℚ) : ℝ) ≤ Real.log (2212 : ℕ)
      ∧ Real.log (2212 : ℕ) ≤ ((770165237/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2213 :
    ((770210433/100000000 : ℚ) : ℝ) ≤ Real.log (2213 : ℕ)
      ∧ Real.log (2213 : ℕ) ≤ ((192552609/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2214 :
    ((770255611/100000000 : ℚ) : ℝ) ≤ Real.log (2214 : ℕ)
      ∧ Real.log (2214 : ℕ) ≤ ((192563903/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2215 :
    ((24071899/3125000 : ℚ) : ℝ) ≤ Real.log (2215 : ℕ)
      ∧ Real.log (2215 : ℕ) ≤ ((770300769/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2216 :
    ((48146619/6250000 : ℚ) : ℝ) ≤ Real.log (2216 : ℕ)
      ∧ Real.log (2216 : ℕ) ≤ ((154069181/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2217 :
    ((770391019/100000000 : ℚ) : ℝ) ≤ Real.log (2217 : ℕ)
      ∧ Real.log (2217 : ℕ) ≤ ((385195511/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2218 :
    ((192609029/25000000 : ℚ) : ℝ) ≤ Real.log (2218 : ℕ)
      ∧ Real.log (2218 : ℕ) ≤ ((770436117/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2219 :
    ((96310149/12500000 : ℚ) : ℝ) ≤ Real.log (2219 : ℕ)
      ∧ Real.log (2219 : ℕ) ≤ ((770481193/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2220 :
    ((770526247/100000000 : ℚ) : ℝ) ≤ Real.log (2220 : ℕ)
      ∧ Real.log (2220 : ℕ) ≤ ((96315781/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2221 :
    ((385285641/50000000 : ℚ) : ℝ) ≤ Real.log (2221 : ℕ)
      ∧ Real.log (2221 : ℕ) ≤ ((770571283/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2222 :
    ((96327037/12500000 : ℚ) : ℝ) ≤ Real.log (2222 : ℕ)
      ∧ Real.log (2222 : ℕ) ≤ ((770616299/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2223 :
    ((770661291/100000000 : ℚ) : ℝ) ≤ Real.log (2223 : ℕ)
      ∧ Real.log (2223 : ℕ) ≤ ((192665323/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2224 :
    ((154141253/20000000 : ℚ) : ℝ) ≤ Real.log (2224 : ℕ)
      ∧ Real.log (2224 : ℕ) ≤ ((385353133/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2225 :
    ((770751219/100000000 : ℚ) : ℝ) ≤ Real.log (2225 : ℕ)
      ∧ Real.log (2225 : ℕ) ≤ ((38537561/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2226 :
    ((770796153/100000000 : ℚ) : ℝ) ≤ Real.log (2226 : ℕ)
      ∧ Real.log (2226 : ℕ) ≤ ((385398077/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2227 :
    ((385420533/50000000 : ℚ) : ℝ) ≤ Real.log (2227 : ℕ)
      ∧ Real.log (2227 : ℕ) ≤ ((770841067/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2228 :
    ((19272149/2500000 : ℚ) : ℝ) ≤ Real.log (2228 : ℕ)
      ∧ Real.log (2228 : ℕ) ≤ ((770885961/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2229 :
    ((770930833/100000000 : ℚ) : ℝ) ≤ Real.log (2229 : ℕ)
      ∧ Real.log (2229 : ℕ) ≤ ((385465417/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2230 :
    ((385487843/50000000 : ℚ) : ℝ) ≤ Real.log (2230 : ℕ)
      ∧ Real.log (2230 : ℕ) ≤ ((770975687/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2231 :
    ((771020519/100000000 : ℚ) : ℝ) ≤ Real.log (2231 : ℕ)
      ∧ Real.log (2231 : ℕ) ≤ ((19275513/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2232 :
    ((192766333/25000000 : ℚ) : ℝ) ≤ Real.log (2232 : ℕ)
      ∧ Real.log (2232 : ℕ) ≤ ((771065333/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2233 :
    ((6168881/800000 : ℚ) : ℝ) ≤ Real.log (2233 : ℕ)
      ∧ Real.log (2233 : ℕ) ≤ ((385555063/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2234 :
    ((48197181/6250000 : ℚ) : ℝ) ≤ Real.log (2234 : ℕ)
      ∧ Real.log (2234 : ℕ) ≤ ((771154899/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2235 :
    ((15423993/2000000 : ℚ) : ℝ) ≤ Real.log (2235 : ℕ)
      ∧ Real.log (2235 : ℕ) ≤ ((771199651/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2236 :
    ((771244383/100000000 : ℚ) : ℝ) ≤ Real.log (2236 : ℕ)
      ∧ Real.log (2236 : ℕ) ≤ ((24101387/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2237 :
    ((96411137/12500000 : ℚ) : ℝ) ≤ Real.log (2237 : ℕ)
      ∧ Real.log (2237 : ℕ) ≤ ((771289097/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2238 :
    ((192833447/25000000 : ℚ) : ℝ) ≤ Real.log (2238 : ℕ)
      ∧ Real.log (2238 : ℕ) ≤ ((771333789/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2239 :
    ((771378461/100000000 : ℚ) : ℝ) ≤ Real.log (2239 : ℕ)
      ∧ Real.log (2239 : ℕ) ≤ ((385689231/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2240 :
    ((385711557/50000000 : ℚ) : ℝ) ≤ Real.log (2240 : ℕ)
      ∧ Real.log (2240 : ℕ) ≤ ((154284623/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2241 :
    ((771467747/100000000 : ℚ) : ℝ) ≤ Real.log (2241 : ℕ)
      ∧ Real.log (2241 : ℕ) ≤ ((192866937/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2242 :
    ((19287809/2500000 : ℚ) : ℝ) ≤ Real.log (2242 : ℕ)
      ∧ Real.log (2242 : ℕ) ≤ ((771512361/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2243 :
    ((771556953/100000000 : ℚ) : ℝ) ≤ Real.log (2243 : ℕ)
      ∧ Real.log (2243 : ℕ) ≤ ((385778477/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2244 :
    ((385800763/50000000 : ℚ) : ℝ) ≤ Real.log (2244 : ℕ)
      ∧ Real.log (2244 : ℕ) ≤ ((771601527/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2245 :
    ((771646079/100000000 : ℚ) : ℝ) ≤ Real.log (2245 : ℕ)
      ∧ Real.log (2245 : ℕ) ≤ ((385823041/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2246 :
    ((771690613/100000000 : ℚ) : ℝ) ≤ Real.log (2246 : ℕ)
      ∧ Real.log (2246 : ℕ) ≤ ((385845307/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2247 :
    ((771735127/100000000 : ℚ) : ℝ) ≤ Real.log (2247 : ℕ)
      ∧ Real.log (2247 : ℕ) ≤ ((96466891/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2248 :
    ((771779621/100000000 : ℚ) : ℝ) ≤ Real.log (2248 : ℕ)
      ∧ Real.log (2248 : ℕ) ≤ ((385889811/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2249 :
    ((154364819/20000000 : ℚ) : ℝ) ≤ Real.log (2249 : ℕ)
      ∧ Real.log (2249 : ℕ) ≤ ((24119503/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2250 :
    ((771868549/100000000 : ℚ) : ℝ) ≤ Real.log (2250 : ℕ)
      ∧ Real.log (2250 : ℕ) ≤ ((15437371/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2251 :
    ((96489123/12500000 : ℚ) : ℝ) ≤ Real.log (2251 : ℕ)
      ∧ Real.log (2251 : ℕ) ≤ ((154382597/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2252 :
    ((385978699/50000000 : ℚ) : ℝ) ≤ Real.log (2252 : ℕ)
      ∧ Real.log (2252 : ℕ) ≤ ((771957399/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2253 :
    ((772001793/100000000 : ℚ) : ℝ) ≤ Real.log (2253 : ℕ)
      ∧ Real.log (2253 : ℕ) ≤ ((193000449/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2254 :
    ((772046169/100000000 : ℚ) : ℝ) ≤ Real.log (2254 : ℕ)
      ∧ Real.log (2254 : ℕ) ≤ ((77204617/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2255 :
    ((30883621/4000000 : ℚ) : ℝ) ≤ Real.log (2255 : ℕ)
      ∧ Real.log (2255 : ℕ) ≤ ((386045263/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2256 :
    ((772134861/100000000 : ℚ) : ℝ) ≤ Real.log (2256 : ℕ)
      ∧ Real.log (2256 : ℕ) ≤ ((386067431/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2257 :
    ((772179177/100000000 : ℚ) : ℝ) ≤ Real.log (2257 : ℕ)
      ∧ Real.log (2257 : ℕ) ≤ ((386089589/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2258 :
    ((386111737/50000000 : ℚ) : ℝ) ≤ Real.log (2258 : ℕ)
      ∧ Real.log (2258 : ℕ) ≤ ((30888939/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2259 :
    ((772267751/100000000 : ℚ) : ℝ) ≤ Real.log (2259 : ℕ)
      ∧ Real.log (2259 : ℕ) ≤ ((96533469/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2260 :
    ((772312009/100000000 : ℚ) : ℝ) ≤ Real.log (2260 : ℕ)
      ∧ Real.log (2260 : ℕ) ≤ ((77231201/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2261 :
    ((772356247/100000000 : ℚ) : ℝ) ≤ Real.log (2261 : ℕ)
      ∧ Real.log (2261 : ℕ) ≤ ((96544531/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2262 :
    ((154480093/20000000 : ℚ) : ℝ) ≤ Real.log (2262 : ℕ)
      ∧ Real.log (2262 : ℕ) ≤ ((386200233/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2263 :
    ((96555583/12500000 : ℚ) : ℝ) ≤ Real.log (2263 : ℕ)
      ∧ Real.log (2263 : ℕ) ≤ ((154488933/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2264 :
    ((772488843/100000000 : ℚ) : ℝ) ≤ Real.log (2264 : ℕ)
      ∧ Real.log (2264 : ℕ) ≤ ((193122211/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2265 :
    ((772533003/100000000 : ℚ) : ℝ) ≤ Real.log (2265 : ℕ)
      ∧ Real.log (2265 : ℕ) ≤ ((193133251/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2266 :
    ((96572143/12500000 : ℚ) : ℝ) ≤ Real.log (2266 : ℕ)
      ∧ Real.log (2266 : ℕ) ≤ ((154515429/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2267 :
    ((154524253/20000000 : ℚ) : ℝ) ≤ Real.log (2267 : ℕ)
      ∧ Real.log (2267 : ℕ) ≤ ((386310633/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2268 :
    ((386332683/50000000 : ℚ) : ℝ) ≤ Real.log (2268 : ℕ)
      ∧ Real.log (2268 : ℕ) ≤ ((772665367/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2269 :
    ((96588681/12500000 : ℚ) : ℝ) ≤ Real.log (2269 : ℕ)
      ∧ Real.log (2269 : ℕ) ≤ ((772709449/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2270 :
    ((77275351/10000000 : ℚ) : ℝ) ≤ Real.log (2270 : ℕ)
      ∧ Real.log (2270 : ℕ) ≤ ((772753513/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2271 :
    ((386398777/50000000 : ℚ) : ℝ) ≤ Real.log (2271 : ℕ)
      ∧ Real.log (2271 : ℕ) ≤ ((154559511/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2272 :
    ((96605197/12500000 : ℚ) : ℝ) ≤ Real.log (2272 : ℕ)
      ∧ Real.log (2272 : ℕ) ≤ ((772841579/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2273 :
    ((386442791/50000000 : ℚ) : ℝ) ≤ Real.log (2273 : ℕ)
      ∧ Real.log (2273 : ℕ) ≤ ((772885583/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2274 :
    ((772929567/100000000 : ℚ) : ℝ) ≤ Real.log (2274 : ℕ)
      ∧ Real.log (2274 : ℕ) ≤ ((24154049/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2275 :
    ((772973533/100000000 : ℚ) : ℝ) ≤ Real.log (2275 : ℕ)
      ∧ Real.log (2275 : ℕ) ≤ ((386486767/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2276 :
    ((773017479/100000000 : ℚ) : ℝ) ≤ Real.log (2276 : ℕ)
      ∧ Real.log (2276 : ℕ) ≤ ((19325437/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2277 :
    ((386530703/50000000 : ℚ) : ℝ) ≤ Real.log (2277 : ℕ)
      ∧ Real.log (2277 : ℕ) ≤ ((773061407/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2278 :
    ((386552657/50000000 : ℚ) : ℝ) ≤ Real.log (2278 : ℕ)
      ∧ Real.log (2278 : ℕ) ≤ ((154621063/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2279 :
    ((386574601/50000000 : ℚ) : ℝ) ≤ Real.log (2279 : ℕ)
      ∧ Real.log (2279 : ℕ) ≤ ((773149203/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2280 :
    ((48324567/6250000 : ℚ) : ℝ) ≤ Real.log (2280 : ℕ)
      ∧ Real.log (2280 : ℕ) ≤ ((773193073/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2281 :
    ((386618461/50000000 : ℚ) : ℝ) ≤ Real.log (2281 : ℕ)
      ∧ Real.log (2281 : ℕ) ≤ ((773236923/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2282 :
    ((48330047/6250000 : ℚ) : ℝ) ≤ Real.log (2282 : ℕ)
      ∧ Real.log (2282 : ℕ) ≤ ((154656151/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2283 :
    ((193331141/25000000 : ℚ) : ℝ) ≤ Real.log (2283 : ℕ)
      ∧ Real.log (2283 : ℕ) ≤ ((154664913/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2284 :
    ((773368357/100000000 : ℚ) : ℝ) ≤ Real.log (2284 : ℕ)
      ∧ Real.log (2284 : ℕ) ≤ ((386684179/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2285 :
    ((77341213/10000000 : ℚ) : ℝ) ≤ Real.log (2285 : ℕ)
      ∧ Real.log (2285 : ℕ) ≤ ((773412131/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2286 :
    ((193363971/25000000 : ℚ) : ℝ) ≤ Real.log (2286 : ℕ)
      ∧ Real.log (2286 : ℕ) ≤ ((154691177/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2287 :
    ((773499619/100000000 : ℚ) : ℝ) ≤ Real.log (2287 : ℕ)
      ∧ Real.log (2287 : ℕ) ≤ ((38674981/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2288 :
    ((154708667/20000000 : ℚ) : ℝ) ≤ Real.log (2288 : ℕ)
      ∧ Real.log (2288 : ℕ) ≤ ((96692917/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2289 :
    ((77358703/10000000 : ℚ) : ℝ) ≤ Real.log (2289 : ℕ)
      ∧ Real.log (2289 : ℕ) ≤ ((773587033/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2290 :
    ((773630709/100000000 : ℚ) : ℝ) ≤ Real.log (2290 : ℕ)
      ∧ Real.log (2290 : ℕ) ≤ ((77363071/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2291 :
    ((6044331/781250 : ℚ) : ℝ) ≤ Real.log (2291 : ℕ)
      ∧ Real.log (2291 : ℕ) ≤ ((773674369/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2292 :
    ((773718007/100000000 : ℚ) : ℝ) ≤ Real.log (2292 : ℕ)
      ∧ Real.log (2292 : ℕ) ≤ ((96714751/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2293 :
    ((193440407/25000000 : ℚ) : ℝ) ≤ Real.log (2293 : ℕ)
      ∧ Real.log (2293 : ℕ) ≤ ((773761629/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2294 :
    ((773805229/100000000 : ℚ) : ℝ) ≤ Real.log (2294 : ℕ)
      ∧ Real.log (2294 : ℕ) ≤ ((77380523/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2295 :
    ((193462203/25000000 : ℚ) : ℝ) ≤ Real.log (2295 : ℕ)
      ∧ Real.log (2295 : ℕ) ≤ ((773848813/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2296 :
    ((6191139/800000 : ℚ) : ℝ) ≤ Real.log (2296 : ℕ)
      ∧ Real.log (2296 : ℕ) ≤ ((96736547/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2297 :
    ((9674199/1250000 : ℚ) : ℝ) ≤ Real.log (2297 : ℕ)
      ∧ Real.log (2297 : ℕ) ≤ ((773935921/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2298 :
    ((154795889/20000000 : ℚ) : ℝ) ≤ Real.log (2298 : ℕ)
      ∧ Real.log (2298 : ℕ) ≤ ((386989723/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2299 :
    ((96752869/12500000 : ℚ) : ℝ) ≤ Real.log (2299 : ℕ)
      ∧ Real.log (2299 : ℕ) ≤ ((774022953/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2300 :
    ((19351661/2500000 : ℚ) : ℝ) ≤ Real.log (2300 : ℕ)
      ∧ Real.log (2300 : ℕ) ≤ ((774066441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2301 :
    ((193527477/25000000 : ℚ) : ℝ) ≤ Real.log (2301 : ℕ)
      ∧ Real.log (2301 : ℕ) ≤ ((774109911/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2302 :
    ((387076679/50000000 : ℚ) : ℝ) ≤ Real.log (2302 : ℕ)
      ∧ Real.log (2302 : ℕ) ≤ ((774153359/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2303 :
    ((193549197/25000000 : ℚ) : ℝ) ≤ Real.log (2303 : ℕ)
      ∧ Real.log (2303 : ℕ) ≤ ((774196791/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2304 :
    ((387120101/50000000 : ℚ) : ℝ) ≤ Real.log (2304 : ℕ)
      ∧ Real.log (2304 : ℕ) ≤ ((774240203/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2305 :
    ((154856719/20000000 : ℚ) : ℝ) ≤ Real.log (2305 : ℕ)
      ∧ Real.log (2305 : ℕ) ≤ ((193570899/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2306 :
    ((77432697/10000000 : ℚ) : ℝ) ≤ Real.log (2306 : ℕ)
      ∧ Real.log (2306 : ℕ) ≤ ((774326971/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2307 :
    ((30974813/4000000 : ℚ) : ℝ) ≤ Real.log (2307 : ℕ)
      ∧ Real.log (2307 : ℕ) ≤ ((387185163/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2308 :
    ((387206831/50000000 : ℚ) : ℝ) ≤ Real.log (2308 : ℕ)
      ∧ Real.log (2308 : ℕ) ≤ ((774413663/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2309 :
    ((38722849/5000000 : ℚ) : ℝ) ≤ Real.log (2309 : ℕ)
      ∧ Real.log (2309 : ℕ) ≤ ((774456981/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2310 :
    ((19362507/2500000 : ℚ) : ℝ) ≤ Real.log (2310 : ℕ)
      ∧ Real.log (2310 : ℕ) ≤ ((774500281/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2311 :
    ((19363589/2500000 : ℚ) : ℝ) ≤ Real.log (2311 : ℕ)
      ∧ Real.log (2311 : ℕ) ≤ ((774543563/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2312 :
    ((774586821/100000000 : ℚ) : ℝ) ≤ Real.log (2312 : ℕ)
      ∧ Real.log (2312 : ℕ) ≤ ((96823353/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2313 :
    ((387315033/50000000 : ℚ) : ℝ) ≤ Real.log (2313 : ℕ)
      ∧ Real.log (2313 : ℕ) ≤ ((774630067/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2314 :
    ((77467329/10000000 : ℚ) : ℝ) ≤ Real.log (2314 : ℕ)
      ∧ Real.log (2314 : ℕ) ≤ ((774673291/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2315 :
    ((48419781/6250000 : ℚ) : ℝ) ≤ Real.log (2315 : ℕ)
      ∧ Real.log (2315 : ℕ) ≤ ((774716497/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2316 :
    ((774759683/100000000 : ℚ) : ℝ) ≤ Real.log (2316 : ℕ)
      ∧ Real.log (2316 : ℕ) ≤ ((193689921/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2317 :
    ((193700713/25000000 : ℚ) : ℝ) ≤ Real.log (2317 : ℕ)
      ∧ Real.log (2317 : ℕ) ≤ ((774802853/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2318 :
    ((387423001/50000000 : ℚ) : ℝ) ≤ Real.log (2318 : ℕ)
      ∧ Real.log (2318 : ℕ) ≤ ((774846003/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2319 :
    ((774889133/100000000 : ℚ) : ℝ) ≤ Real.log (2319 : ℕ)
      ∧ Real.log (2319 : ℕ) ≤ ((387444567/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2320 :
    ((387466123/50000000 : ℚ) : ℝ) ≤ Real.log (2320 : ℕ)
      ∧ Real.log (2320 : ℕ) ≤ ((774932247/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2321 :
    ((38748767/5000000 : ℚ) : ℝ) ≤ Real.log (2321 : ℕ)
      ∧ Real.log (2321 : ℕ) ≤ ((774975341/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2322 :
    ((48438651/6250000 : ℚ) : ℝ) ≤ Real.log (2322 : ℕ)
      ∧ Real.log (2322 : ℕ) ≤ ((775018417/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2323 :
    ((775061473/100000000 : ℚ) : ℝ) ≤ Real.log (2323 : ℕ)
      ∧ Real.log (2323 : ℕ) ≤ ((387530737/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2324 :
    ((775104511/100000000 : ℚ) : ℝ) ≤ Real.log (2324 : ℕ)
      ∧ Real.log (2324 : ℕ) ≤ ((3027752/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2325 :
    ((775147531/100000000 : ℚ) : ℝ) ≤ Real.log (2325 : ℕ)
      ∧ Real.log (2325 : ℕ) ≤ ((193786883/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2326 :
    ((775190533/100000000 : ℚ) : ℝ) ≤ Real.log (2326 : ℕ)
      ∧ Real.log (2326 : ℕ) ≤ ((387595267/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2327 :
    ((193808379/25000000 : ℚ) : ℝ) ≤ Real.log (2327 : ℕ)
      ∧ Real.log (2327 : ℕ) ≤ ((775233517/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2328 :
    ((2422739/312500 : ℚ) : ℝ) ≤ Real.log (2328 : ℕ)
      ∧ Real.log (2328 : ℕ) ≤ ((775276481/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2329 :
    ((31012777/4000000 : ℚ) : ℝ) ≤ Real.log (2329 : ℕ)
      ∧ Real.log (2329 : ℕ) ≤ ((193829857/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2330 :
    ((387681177/50000000 : ℚ) : ℝ) ≤ Real.log (2330 : ℕ)
      ∧ Real.log (2330 : ℕ) ≤ ((155072471/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2331 :
    ((775405263/100000000 : ℚ) : ℝ) ≤ Real.log (2331 : ℕ)
      ∧ Real.log (2331 : ℕ) ≤ ((48462829/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2332 :
    ((387724077/50000000 : ℚ) : ℝ) ≤ Real.log (2332 : ℕ)
      ∧ Real.log (2332 : ℕ) ≤ ((155089631/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2333 :
    ((775491027/100000000 : ℚ) : ℝ) ≤ Real.log (2333 : ℕ)
      ∧ Real.log (2333 : ℕ) ≤ ((193872757/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2334 :
    ((775533881/100000000 : ℚ) : ℝ) ≤ Real.log (2334 : ℕ)
      ∧ Real.log (2334 : ℕ) ≤ ((387766941/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2335 :
    ((193894179/25000000 : ℚ) : ℝ) ≤ Real.log (2335 : ℕ)
      ∧ Real.log (2335 : ℕ) ≤ ((775576719/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2336 :
    ((387809767/50000000 : ℚ) : ℝ) ≤ Real.log (2336 : ℕ)
      ∧ Real.log (2336 : ℕ) ≤ ((155123907/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2337 :
    ((775662333/100000000 : ℚ) : ℝ) ≤ Real.log (2337 : ℕ)
      ∧ Real.log (2337 : ℕ) ≤ ((387831167/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2338 :
    ((387852557/50000000 : ℚ) : ℝ) ≤ Real.log (2338 : ℕ)
      ∧ Real.log (2338 : ℕ) ≤ ((155141023/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2339 :
    ((193936969/25000000 : ℚ) : ℝ) ≤ Real.log (2339 : ℕ)
      ∧ Real.log (2339 : ℕ) ≤ ((775747877/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2340 :
    ((38789531/5000000 : ℚ) : ℝ) ≤ Real.log (2340 : ℕ)
      ∧ Real.log (2340 : ℕ) ≤ ((775790621/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2341 :
    ((387916673/50000000 : ℚ) : ℝ) ≤ Real.log (2341 : ℕ)
      ∧ Real.log (2341 : ℕ) ≤ ((775833347/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2342 :
    ((387938027/50000000 : ℚ) : ℝ) ≤ Real.log (2342 : ℕ)
      ∧ Real.log (2342 : ℕ) ≤ ((155175211/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2343 :
    ((775918743/100000000 : ℚ) : ℝ) ≤ Real.log (2343 : ℕ)
      ∧ Real.log (2343 : ℕ) ≤ ((96989843/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2344 :
    ((155192283/20000000 : ℚ) : ℝ) ≤ Real.log (2344 : ℕ)
      ∧ Real.log (2344 : ℕ) ≤ ((96995177/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2345 :
    ((194001017/25000000 : ℚ) : ℝ) ≤ Real.log (2345 : ℕ)
      ∧ Real.log (2345 : ℕ) ≤ ((776004069/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2346 :
    ((388023351/50000000 : ℚ) : ℝ) ≤ Real.log (2346 : ℕ)
      ∧ Real.log (2346 : ℕ) ≤ ((776046703/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2347 :
    ((776089319/100000000 : ℚ) : ℝ) ≤ Real.log (2347 : ℕ)
      ∧ Real.log (2347 : ℕ) ≤ ((19402233/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2348 :
    ((388065959/50000000 : ℚ) : ℝ) ≤ Real.log (2348 : ℕ)
      ∧ Real.log (2348 : ℕ) ≤ ((776131919/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2349 :
    ((388087249/50000000 : ℚ) : ℝ) ≤ Real.log (2349 : ℕ)
      ∧ Real.log (2349 : ℕ) ≤ ((776174499/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2350 :
    ((38810853/5000000 : ℚ) : ℝ) ≤ Real.log (2350 : ℕ)
      ∧ Real.log (2350 : ℕ) ≤ ((776217061/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2351 :
    ((194064901/25000000 : ℚ) : ℝ) ≤ Real.log (2351 : ℕ)
      ∧ Real.log (2351 : ℕ) ≤ ((155251921/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2352 :
    ((77630213/10000000 : ℚ) : ℝ) ≤ Real.log (2352 : ℕ)
      ∧ Real.log (2352 : ℕ) ≤ ((776302131/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2353 :
    ((388172319/50000000 : ℚ) : ℝ) ≤ Real.log (2353 : ℕ)
      ∧ Real.log (2353 : ℕ) ≤ ((776344639/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2354 :
    ((97048391/12500000 : ℚ) : ℝ) ≤ Real.log (2354 : ℕ)
      ∧ Real.log (2354 : ℕ) ≤ ((776387129/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2355 :
    ((970537/125000 : ℚ) : ℝ) ≤ Real.log (2355 : ℕ)
      ∧ Real.log (2355 : ℕ) ≤ ((776429601/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2356 :
    ((388236027/50000000 : ℚ) : ℝ) ≤ Real.log (2356 : ℕ)
      ∧ Real.log (2356 : ℕ) ≤ ((155294411/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2357 :
    ((77651449/10000000 : ℚ) : ℝ) ≤ Real.log (2357 : ℕ)
      ∧ Real.log (2357 : ℕ) ≤ ((776514491/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2358 :
    ((194139227/25000000 : ℚ) : ℝ) ≤ Real.log (2358 : ℕ)
      ∧ Real.log (2358 : ℕ) ≤ ((776556909/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2359 :
    ((776599307/100000000 : ℚ) : ℝ) ≤ Real.log (2359 : ℕ)
      ∧ Real.log (2359 : ℕ) ≤ ((194149827/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2360 :
    ((776641689/100000000 : ℚ) : ℝ) ≤ Real.log (2360 : ℕ)
      ∧ Real.log (2360 : ℕ) ≤ ((77664169/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2361 :
    ((776684053/100000000 : ℚ) : ℝ) ≤ Real.log (2361 : ℕ)
      ∧ Real.log (2361 : ℕ) ≤ ((388342027/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2362 :
    ((776726399/100000000 : ℚ) : ℝ) ≤ Real.log (2362 : ℕ)
      ∧ Real.log (2362 : ℕ) ≤ ((242727/31250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2363 :
    ((776768727/100000000 : ℚ) : ℝ) ≤ Real.log (2363 : ℕ)
      ∧ Real.log (2363 : ℕ) ≤ ((97096091/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2364 :
    ((776811037/100000000 : ℚ) : ℝ) ≤ Real.log (2364 : ℕ)
      ∧ Real.log (2364 : ℕ) ≤ ((388405519/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2365 :
    ((77685333/10000000 : ℚ) : ℝ) ≤ Real.log (2365 : ℕ)
      ∧ Real.log (2365 : ℕ) ≤ ((776853331/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2366 :
    ((194223901/25000000 : ℚ) : ℝ) ≤ Real.log (2366 : ℕ)
      ∧ Real.log (2366 : ℕ) ≤ ((155379121/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2367 :
    ((38846893/5000000 : ℚ) : ℝ) ≤ Real.log (2367 : ℕ)
      ∧ Real.log (2367 : ℕ) ≤ ((776937861/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2368 :
    ((776980099/100000000 : ℚ) : ℝ) ≤ Real.log (2368 : ℕ)
      ∧ Real.log (2368 : ℕ) ≤ ((7769801/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2369 :
    ((9712779/1250000 : ℚ) : ℝ) ≤ Real.log (2369 : ℕ)
      ∧ Real.log (2369 : ℕ) ≤ ((777022321/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2370 :
    ((777064523/100000000 : ℚ) : ℝ) ≤ Real.log (2370 : ℕ)
      ∧ Real.log (2370 : ℕ) ≤ ((194266131/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2371 :
    ((194276677/25000000 : ℚ) : ℝ) ≤ Real.log (2371 : ℕ)
      ∧ Real.log (2371 : ℕ) ≤ ((777106709/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2372 :
    ((6217191/800000 : ℚ) : ℝ) ≤ Real.log (2372 : ℕ)
      ∧ Real.log (2372 : ℕ) ≤ ((388574439/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2373 :
    ((31087641/4000000 : ℚ) : ℝ) ≤ Real.log (2373 : ℕ)
      ∧ Real.log (2373 : ℕ) ≤ ((388595513/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2374 :
    ((777233157/100000000 : ℚ) : ℝ) ≤ Real.log (2374 : ℕ)
      ∧ Real.log (2374 : ℕ) ≤ ((388616579/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2375 :
    ((777275271/100000000 : ℚ) : ℝ) ≤ Real.log (2375 : ℕ)
      ∧ Real.log (2375 : ℕ) ≤ ((97159409/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2376 :
    ((97164671/12500000 : ℚ) : ℝ) ≤ Real.log (2376 : ℕ)
      ∧ Real.log (2376 : ℕ) ≤ ((777317369/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2377 :
    ((388679723/50000000 : ℚ) : ℝ) ≤ Real.log (2377 : ℕ)
      ∧ Real.log (2377 : ℕ) ≤ ((777359447/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2378 :
    ((777401507/100000000 : ℚ) : ℝ) ≤ Real.log (2378 : ℕ)
      ∧ Real.log (2378 : ℕ) ≤ ((194350377/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2379 :
    ((15548871/2000000 : ℚ) : ℝ) ≤ Real.log (2379 : ℕ)
      ∧ Real.log (2379 : ℕ) ≤ ((777443553/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2380 :
    ((97185697/12500000 : ℚ) : ℝ) ≤ Real.log (2380 : ℕ)
      ∧ Real.log (2380 : ℕ) ≤ ((777485577/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2381 :
    ((24297737/3125000 : ℚ) : ℝ) ≤ Real.log (2381 : ℕ)
      ∧ Real.log (2381 : ℕ) ≤ ((155505517/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2382 :
    ((777569573/100000000 : ℚ) : ℝ) ≤ Real.log (2382 : ℕ)
      ∧ Real.log (2382 : ℕ) ≤ ((97196197/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2383 :
    ((777611547/100000000 : ℚ) : ℝ) ≤ Real.log (2383 : ℕ)
      ∧ Real.log (2383 : ℕ) ≤ ((194402887/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2384 :
    ((388826751/50000000 : ℚ) : ℝ) ≤ Real.log (2384 : ℕ)
      ∧ Real.log (2384 : ℕ) ≤ ((777653503/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2385 :
    ((9721193/1250000 : ℚ) : ℝ) ≤ Real.log (2385 : ℕ)
      ∧ Real.log (2385 : ℕ) ≤ ((777695441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2386 :
    ((9721717/1250000 : ℚ) : ℝ) ≤ Real.log (2386 : ℕ)
      ∧ Real.log (2386 : ℕ) ≤ ((777737361/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2387 :
    ((388889631/50000000 : ℚ) : ℝ) ≤ Real.log (2387 : ℕ)
      ∧ Real.log (2387 : ℕ) ≤ ((777779263/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2388 :
    ((777821147/100000000 : ℚ) : ℝ) ≤ Real.log (2388 : ℕ)
      ∧ Real.log (2388 : ℕ) ≤ ((194455287/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2389 :
    ((388931507/50000000 : ℚ) : ℝ) ≤ Real.log (2389 : ℕ)
      ∧ Real.log (2389 : ℕ) ≤ ((155572603/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2390 :
    ((24309527/3125000 : ℚ) : ℝ) ≤ Real.log (2390 : ℕ)
      ∧ Real.log (2390 : ℕ) ≤ ((155580973/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2391 :
    ((97243337/12500000 : ℚ) : ℝ) ≤ Real.log (2391 : ℕ)
      ∧ Real.log (2391 : ℕ) ≤ ((777946697/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2392 :
    ((777988511/100000000 : ℚ) : ℝ) ≤ Real.log (2392 : ℕ)
      ∧ Real.log (2392 : ℕ) ≤ ((24312141/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2393 :
    ((194507577/25000000 : ℚ) : ℝ) ≤ Real.log (2393 : ℕ)
      ∧ Real.log (2393 : ℕ) ≤ ((778030309/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2394 :
    ((97259011/12500000 : ℚ) : ℝ) ≤ Real.log (2394 : ℕ)
      ∧ Real.log (2394 : ℕ) ≤ ((778072089/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2395 :
    ((778113849/100000000 : ℚ) : ℝ) ≤ Real.log (2395 : ℕ)
      ∧ Real.log (2395 : ℕ) ≤ ((194528463/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2396 :
    ((155631119/20000000 : ℚ) : ℝ) ≤ Real.log (2396 : ℕ)
      ∧ Real.log (2396 : ℕ) ≤ ((194538899/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2397 :
    ((778197323/100000000 : ℚ) : ℝ) ≤ Real.log (2397 : ℕ)
      ∧ Real.log (2397 : ℕ) ≤ ((194549331/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2398 :
    ((778239033/100000000 : ℚ) : ℝ) ≤ Real.log (2398 : ℕ)
      ∧ Real.log (2398 : ℕ) ≤ ((389119517/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2399 :
    ((389140363/50000000 : ℚ) : ℝ) ≤ Real.log (2399 : ℕ)
      ∧ Real.log (2399 : ℕ) ≤ ((778280727/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2400 :
    ((778322401/100000000 : ℚ) : ℝ) ≤ Real.log (2400 : ℕ)
      ∧ Real.log (2400 : ℕ) ≤ ((389161201/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2401 :
    ((778364059/100000000 : ℚ) : ℝ) ≤ Real.log (2401 : ℕ)
      ∧ Real.log (2401 : ℕ) ≤ ((38918203/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2402 :
    ((7784057/1000000 : ℚ) : ℝ) ≤ Real.log (2402 : ℕ)
      ∧ Real.log (2402 : ℕ) ≤ ((778405701/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2403 :
    ((778447323/100000000 : ℚ) : ℝ) ≤ Real.log (2403 : ℕ)
      ∧ Real.log (2403 : ℕ) ≤ ((194611831/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2404 :
    ((778488929/100000000 : ℚ) : ℝ) ≤ Real.log (2404 : ℕ)
      ∧ Real.log (2404 : ℕ) ≤ ((77848893/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2405 :
    ((389265259/50000000 : ℚ) : ℝ) ≤ Real.log (2405 : ℕ)
      ∧ Real.log (2405 : ℕ) ≤ ((778530519/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2406 :
    ((778572089/100000000 : ℚ) : ℝ) ≤ Real.log (2406 : ℕ)
      ∧ Real.log (2406 : ℕ) ≤ ((77857209/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2407 :
    ((778613643/100000000 : ℚ) : ℝ) ≤ Real.log (2407 : ℕ)
      ∧ Real.log (2407 : ℕ) ≤ ((194653411/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2408 :
    ((38932759/5000000 : ℚ) : ℝ) ≤ Real.log (2408 : ℕ)
      ∧ Real.log (2408 : ℕ) ≤ ((778655181/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2409 :
    ((7786967/1000000 : ℚ) : ℝ) ≤ Real.log (2409 : ℕ)
      ∧ Real.log (2409 : ℕ) ≤ ((778696701/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2410 :
    ((389369101/50000000 : ℚ) : ℝ) ≤ Real.log (2410 : ℕ)
      ∧ Real.log (2410 : ℕ) ≤ ((778738203/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2411 :
    ((778779687/100000000 : ℚ) : ℝ) ≤ Real.log (2411 : ℕ)
      ∧ Real.log (2411 : ℕ) ≤ ((97347461/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2412 :
    ((155764231/20000000 : ℚ) : ℝ) ≤ Real.log (2412 : ℕ)
      ∧ Real.log (2412 : ℕ) ≤ ((194705289/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2413 :
    ((389431303/50000000 : ℚ) : ℝ) ≤ Real.log (2413 : ℕ)
      ∧ Real.log (2413 : ℕ) ≤ ((778862607/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2414 :
    ((19472601/2500000 : ℚ) : ℝ) ≤ Real.log (2414 : ℕ)
      ∧ Real.log (2414 : ℕ) ≤ ((778904041/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2415 :
    ((48684091/6250000 : ℚ) : ℝ) ≤ Real.log (2415 : ℕ)
      ∧ Real.log (2415 : ℕ) ≤ ((778945457/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2416 :
    ((155797371/20000000 : ℚ) : ℝ) ≤ Real.log (2416 : ℕ)
      ∧ Real.log (2416 : ℕ) ≤ ((97373357/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2417 :
    ((389514119/50000000 : ℚ) : ℝ) ≤ Real.log (2417 : ℕ)
      ∧ Real.log (2417 : ℕ) ≤ ((779028239/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2418 :
    ((779069603/100000000 : ℚ) : ℝ) ≤ Real.log (2418 : ℕ)
      ∧ Real.log (2418 : ℕ) ≤ ((194767401/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2419 :
    ((779110951/100000000 : ℚ) : ℝ) ≤ Real.log (2419 : ℕ)
      ∧ Real.log (2419 : ℕ) ≤ ((97388869/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2420 :
    ((779152281/100000000 : ℚ) : ℝ) ≤ Real.log (2420 : ℕ)
      ∧ Real.log (2420 : ℕ) ≤ ((389576141/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2421 :
    ((155838719/20000000 : ℚ) : ℝ) ≤ Real.log (2421 : ℕ)
      ∧ Real.log (2421 : ℕ) ≤ ((194798399/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2422 :
    ((194808723/25000000 : ℚ) : ℝ) ≤ Real.log (2422 : ℕ)
      ∧ Real.log (2422 : ℕ) ≤ ((779234893/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2423 :
    ((194819043/25000000 : ℚ) : ℝ) ≤ Real.log (2423 : ℕ)
      ∧ Real.log (2423 : ℕ) ≤ ((779276173/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2424 :
    ((389658717/50000000 : ℚ) : ℝ) ≤ Real.log (2424 : ℕ)
      ∧ Real.log (2424 : ℕ) ≤ ((155863487/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2425 :
    ((19483967/2500000 : ℚ) : ℝ) ≤ Real.log (2425 : ℕ)
      ∧ Real.log (2425 : ℕ) ≤ ((779358681/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2426 :
    ((194849977/25000000 : ℚ) : ℝ) ≤ Real.log (2426 : ℕ)
      ∧ Real.log (2426 : ℕ) ≤ ((779399909/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2427 :
    ((4871507/625000 : ℚ) : ℝ) ≤ Real.log (2427 : ℕ)
      ∧ Real.log (2427 : ℕ) ≤ ((779441121/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2428 :
    ((155896463/20000000 : ℚ) : ℝ) ≤ Real.log (2428 : ℕ)
      ∧ Real.log (2428 : ℕ) ≤ ((194870579/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2429 :
    ((194880873/25000000 : ℚ) : ℝ) ≤ Real.log (2429 : ℕ)
      ∧ Real.log (2429 : ℕ) ≤ ((779523493/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2430 :
    ((779564653/100000000 : ℚ) : ℝ) ≤ Real.log (2430 : ℕ)
      ∧ Real.log (2430 : ℕ) ≤ ((389782327/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2431 :
    ((779605797/100000000 : ℚ) : ℝ) ≤ Real.log (2431 : ℕ)
      ∧ Real.log (2431 : ℕ) ≤ ((389802899/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2432 :
    ((194911731/25000000 : ℚ) : ℝ) ≤ Real.log (2432 : ℕ)
      ∧ Real.log (2432 : ℕ) ≤ ((31185877/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2433 :
    ((389844017/50000000 : ℚ) : ℝ) ≤ Real.log (2433 : ℕ)
      ∧ Real.log (2433 : ℕ) ≤ ((155937607/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2434 :
    ((779729127/100000000 : ℚ) : ℝ) ≤ Real.log (2434 : ℕ)
      ∧ Real.log (2434 : ℕ) ≤ ((97466141/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2435 :
    ((779770203/100000000 : ℚ) : ℝ) ≤ Real.log (2435 : ℕ)
      ∧ Real.log (2435 : ℕ) ≤ ((194942551/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2436 :
    ((389905631/50000000 : ℚ) : ℝ) ≤ Real.log (2436 : ℕ)
      ∧ Real.log (2436 : ℕ) ≤ ((779811263/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2437 :
    ((155970461/20000000 : ℚ) : ℝ) ≤ Real.log (2437 : ℕ)
      ∧ Real.log (2437 : ℕ) ≤ ((389926153/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2438 :
    ((77989333/10000000 : ℚ) : ℝ) ≤ Real.log (2438 : ℕ)
      ∧ Real.log (2438 : ℕ) ≤ ((779893333/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2439 :
    ((779934339/100000000 : ℚ) : ℝ) ≤ Real.log (2439 : ℕ)
      ∧ Real.log (2439 : ℕ) ≤ ((38996717/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2440 :
    ((779975331/100000000 : ℚ) : ℝ) ≤ Real.log (2440 : ℕ)
      ∧ Real.log (2440 : ℕ) ≤ ((194993833/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2441 :
    ((390008153/50000000 : ℚ) : ℝ) ≤ Real.log (2441 : ℕ)
      ∧ Real.log (2441 : ℕ) ≤ ((780016309/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2442 :
    ((156011453/20000000 : ℚ) : ℝ) ≤ Real.log (2442 : ℕ)
      ∧ Real.log (2442 : ℕ) ≤ ((390028633/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2443 :
    ((780098207/100000000 : ℚ) : ℝ) ≤ Real.log (2443 : ℕ)
      ∧ Real.log (2443 : ℕ) ≤ ((24378069/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2444 :
    ((780139131/100000000 : ℚ) : ℝ) ≤ Real.log (2444 : ℕ)
      ∧ Real.log (2444 : ℕ) ≤ ((390069567/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2445 :
    ((19504501/2500000 : ℚ) : ℝ) ≤ Real.log (2445 : ℕ)
      ∧ Real.log (2445 : ℕ) ≤ ((780180041/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2446 :
    ((780220931/100000000 : ℚ) : ℝ) ≤ Real.log (2446 : ℕ)
      ∧ Real.log (2446 : ℕ) ≤ ((195055233/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2447 :
    ((390130903/50000000 : ℚ) : ℝ) ≤ Real.log (2447 : ℕ)
      ∧ Real.log (2447 : ℕ) ≤ ((780261807/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2448 :
    ((97537833/12500000 : ℚ) : ℝ) ≤ Real.log (2448 : ℕ)
      ∧ Real.log (2448 : ℕ) ≤ ((156060533/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2449 :
    ((156068701/20000000 : ℚ) : ℝ) ≤ Real.log (2449 : ℕ)
      ∧ Real.log (2449 : ℕ) ≤ ((390171753/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2450 :
    ((78038433/10000000 : ℚ) : ℝ) ≤ Real.log (2450 : ℕ)
      ∧ Real.log (2450 : ℕ) ≤ ((780384331/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2451 :
    ((390212569/50000000 : ℚ) : ℝ) ≤ Real.log (2451 : ℕ)
      ∧ Real.log (2451 : ℕ) ≤ ((780425139/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2452 :
    ((780465929/100000000 : ℚ) : ℝ) ≤ Real.log (2452 : ℕ)
      ∧ Real.log (2452 : ℕ) ≤ ((78046593/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2453 :
    ((48781669/6250000 : ℚ) : ℝ) ≤ Real.log (2453 : ℕ)
      ∧ Real.log (2453 : ℕ) ≤ ((156101341/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2454 :
    ((390273731/50000000 : ℚ) : ℝ) ≤ Real.log (2454 : ℕ)
      ∧ Real.log (2454 : ℕ) ≤ ((780547463/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2455 :
    ((780588203/100000000 : ℚ) : ℝ) ≤ Real.log (2455 : ℕ)
      ∧ Real.log (2455 : ℕ) ≤ ((390294103/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2456 :
    ((12197327/1562500 : ℚ) : ℝ) ≤ Real.log (2456 : ℕ)
      ∧ Real.log (2456 : ℕ) ≤ ((780628929/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2457 :
    ((780669637/100000000 : ℚ) : ℝ) ≤ Real.log (2457 : ℕ)
      ∧ Real.log (2457 : ℕ) ≤ ((390334819/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2458 :
    ((97588791/12500000 : ℚ) : ℝ) ≤ Real.log (2458 : ℕ)
      ∧ Real.log (2458 : ℕ) ≤ ((780710331/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2459 :
    ((195187751/25000000 : ℚ) : ℝ) ≤ Real.log (2459 : ℕ)
      ∧ Real.log (2459 : ℕ) ≤ ((156150201/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2460 :
    ((390395831/50000000 : ℚ) : ℝ) ≤ Real.log (2460 : ℕ)
      ∧ Real.log (2460 : ℕ) ≤ ((780791663/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2461 :
    ((48802019/6250000 : ℚ) : ℝ) ≤ Real.log (2461 : ℕ)
      ∧ Real.log (2461 : ℕ) ≤ ((780832307/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2462 :
    ((78087293/10000000 : ℚ) : ℝ) ≤ Real.log (2462 : ℕ)
      ∧ Real.log (2462 : ℕ) ≤ ((780872931/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2463 :
    ((780913539/100000000 : ℚ) : ℝ) ≤ Real.log (2463 : ℕ)
      ∧ Real.log (2463 : ℕ) ≤ ((39045677/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2464 :
    ((195238533/25000000 : ℚ) : ℝ) ≤ Real.log (2464 : ℕ)
      ∧ Real.log (2464 : ℕ) ≤ ((780954133/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2465 :
    ((195248677/25000000 : ℚ) : ℝ) ≤ Real.log (2465 : ℕ)
      ∧ Real.log (2465 : ℕ) ≤ ((780994709/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2466 :
    ((195258817/25000000 : ℚ) : ℝ) ≤ Real.log (2466 : ℕ)
      ∧ Real.log (2466 : ℕ) ≤ ((781035269/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2467 :
    ((781075811/100000000 : ℚ) : ℝ) ≤ Real.log (2467 : ℕ)
      ∧ Real.log (2467 : ℕ) ≤ ((195268953/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2468 :
    ((390558169/50000000 : ℚ) : ℝ) ≤ Real.log (2468 : ℕ)
      ∧ Real.log (2468 : ℕ) ≤ ((781116339/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2469 :
    ((48822303/6250000 : ℚ) : ℝ) ≤ Real.log (2469 : ℕ)
      ∧ Real.log (2469 : ℕ) ≤ ((781156849/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2470 :
    ((781197341/100000000 : ℚ) : ℝ) ≤ Real.log (2470 : ℕ)
      ∧ Real.log (2470 : ℕ) ≤ ((24412417/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2471 :
    ((39061891/5000000 : ℚ) : ℝ) ≤ Real.log (2471 : ℕ)
      ∧ Real.log (2471 : ℕ) ≤ ((781237821/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2472 :
    ((781278281/100000000 : ℚ) : ℝ) ≤ Real.log (2472 : ℕ)
      ∧ Real.log (2472 : ℕ) ≤ ((390639141/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2473 :
    ((390659363/50000000 : ℚ) : ℝ) ≤ Real.log (2473 : ℕ)
      ∧ Real.log (2473 : ℕ) ≤ ((781318727/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2474 :
    ((156271831/20000000 : ℚ) : ℝ) ≤ Real.log (2474 : ℕ)
      ∧ Real.log (2474 : ℕ) ≤ ((195339789/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2475 :
    ((781399567/100000000 : ℚ) : ℝ) ≤ Real.log (2475 : ℕ)
      ∧ Real.log (2475 : ℕ) ≤ ((48837473/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2476 :
    ((781439963/100000000 : ℚ) : ℝ) ≤ Real.log (2476 : ℕ)
      ∧ Real.log (2476 : ℕ) ≤ ((195359991/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2477 :
    ((390740171/50000000 : ℚ) : ℝ) ≤ Real.log (2477 : ℕ)
      ∧ Real.log (2477 : ℕ) ≤ ((781480343/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2478 :
    ((390760353/50000000 : ℚ) : ℝ) ≤ Real.log (2478 : ℕ)
      ∧ Real.log (2478 : ℕ) ≤ ((781520707/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2479 :
    ((781561053/100000000 : ℚ) : ℝ) ≤ Real.log (2479 : ℕ)
      ∧ Real.log (2479 : ℕ) ≤ ((390780527/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2480 :
    ((781601383/100000000 : ℚ) : ℝ) ≤ Real.log (2480 : ℕ)
      ∧ Real.log (2480 : ℕ) ≤ ((97700173/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2481 :
    ((390820849/50000000 : ℚ) : ℝ) ≤ Real.log (2481 : ℕ)
      ∧ Real.log (2481 : ℕ) ≤ ((781641699/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2482 :
    ((195420499/25000000 : ℚ) : ℝ) ≤ Real.log (2482 : ℕ)
      ∧ Real.log (2482 : ℕ) ≤ ((781681997/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2483 :
    ((390861139/50000000 : ℚ) : ℝ) ≤ Real.log (2483 : ℕ)
      ∧ Real.log (2483 : ℕ) ≤ ((781722279/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2484 :
    ((48860159/6250000 : ℚ) : ℝ) ≤ Real.log (2484 : ℕ)
      ∧ Real.log (2484 : ℕ) ≤ ((156352509/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2485 :
    ((781802793/100000000 : ℚ) : ℝ) ≤ Real.log (2485 : ℕ)
      ∧ Real.log (2485 : ℕ) ≤ ((390901397/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2486 :
    ((781843027/100000000 : ℚ) : ℝ) ≤ Real.log (2486 : ℕ)
      ∧ Real.log (2486 : ℕ) ≤ ((195460757/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2487 :
    ((195470811/25000000 : ℚ) : ℝ) ≤ Real.log (2487 : ℕ)
      ∧ Real.log (2487 : ℕ) ≤ ((156376649/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2488 :
    ((156384689/20000000 : ℚ) : ℝ) ≤ Real.log (2488 : ℕ)
      ∧ Real.log (2488 : ℕ) ≤ ((390961723/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2489 :
    ((78196363/10000000 : ℚ) : ℝ) ≤ Real.log (2489 : ℕ)
      ∧ Real.log (2489 : ℕ) ≤ ((781963631/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2490 :
    ((391001899/50000000 : ℚ) : ℝ) ≤ Real.log (2490 : ℕ)
      ∧ Real.log (2490 : ℕ) ≤ ((782003799/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2491 :
    ((782043951/100000000 : ℚ) : ℝ) ≤ Real.log (2491 : ℕ)
      ∧ Real.log (2491 : ℕ) ≤ ((48877747/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2492 :
    ((391042043/50000000 : ℚ) : ℝ) ≤ Real.log (2492 : ℕ)
      ∧ Real.log (2492 : ℕ) ≤ ((782084089/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2493 :
    ((48882763/6250000 : ℚ) : ℝ) ≤ Real.log (2493 : ℕ)
      ∧ Real.log (2493 : ℕ) ≤ ((782124209/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2494 :
    ((97770539/12500000 : ℚ) : ℝ) ≤ Real.log (2494 : ℕ)
      ∧ Real.log (2494 : ℕ) ≤ ((782164313/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2495 :
    ((1955511/250000 : ℚ) : ℝ) ≤ Real.log (2495 : ℕ)
      ∧ Real.log (2495 : ℕ) ≤ ((782204401/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2496 :
    ((97780559/12500000 : ℚ) : ℝ) ≤ Real.log (2496 : ℕ)
      ∧ Real.log (2496 : ℕ) ≤ ((782244473/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2497 :
    ((48892783/6250000 : ℚ) : ℝ) ≤ Real.log (2497 : ℕ)
      ∧ Real.log (2497 : ℕ) ≤ ((782284531/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2498 :
    ((782324569/100000000 : ℚ) : ℝ) ≤ Real.log (2498 : ℕ)
      ∧ Real.log (2498 : ℕ) ≤ ((78232457/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2499 :
    ((782364593/100000000 : ℚ) : ℝ) ≤ Real.log (2499 : ℕ)
      ∧ Real.log (2499 : ℕ) ≤ ((391182297/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2500 :
    ((782404601/100000000 : ℚ) : ℝ) ≤ Real.log (2500 : ℕ)
      ∧ Real.log (2500 : ℕ) ≤ ((391202301/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2501 :
    ((782444593/100000000 : ℚ) : ℝ) ≤ Real.log (2501 : ℕ)
      ∧ Real.log (2501 : ℕ) ≤ ((391222297/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2502 :
    ((782484569/100000000 : ℚ) : ℝ) ≤ Real.log (2502 : ℕ)
      ∧ Real.log (2502 : ℕ) ≤ ((78248457/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2503 :
    ((782524529/100000000 : ℚ) : ℝ) ≤ Real.log (2503 : ℕ)
      ∧ Real.log (2503 : ℕ) ≤ ((78252453/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2504 :
    ((782564473/100000000 : ℚ) : ℝ) ≤ Real.log (2504 : ℕ)
      ∧ Real.log (2504 : ℕ) ≤ ((391282237/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2505 :
    ((782604401/100000000 : ℚ) : ℝ) ≤ Real.log (2505 : ℕ)
      ∧ Real.log (2505 : ℕ) ≤ ((391302201/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2506 :
    ((782644313/100000000 : ℚ) : ℝ) ≤ Real.log (2506 : ℕ)
      ∧ Real.log (2506 : ℕ) ≤ ((391322157/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2507 :
    ((782684209/100000000 : ℚ) : ℝ) ≤ Real.log (2507 : ℕ)
      ∧ Real.log (2507 : ℕ) ≤ ((78268421/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2508 :
    ((78272409/10000000 : ℚ) : ℝ) ≤ Real.log (2508 : ℕ)
      ∧ Real.log (2508 : ℕ) ≤ ((782724091/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2509 :
    ((391381977/50000000 : ℚ) : ℝ) ≤ Real.log (2509 : ℕ)
      ∧ Real.log (2509 : ℕ) ≤ ((156552791/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2510 :
    ((782803803/100000000 : ℚ) : ℝ) ≤ Real.log (2510 : ℕ)
      ∧ Real.log (2510 : ℕ) ≤ ((195700951/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2511 :
    ((156568727/20000000 : ℚ) : ℝ) ≤ Real.log (2511 : ℕ)
      ∧ Real.log (2511 : ℕ) ≤ ((195710909/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2512 :
    ((195720863/25000000 : ℚ) : ℝ) ≤ Real.log (2512 : ℕ)
      ∧ Real.log (2512 : ℕ) ≤ ((782883453/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2513 :
    ((782923253/100000000 : ℚ) : ℝ) ≤ Real.log (2513 : ℕ)
      ∧ Real.log (2513 : ℕ) ≤ ((391461627/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2514 :
    ((391481519/50000000 : ℚ) : ℝ) ≤ Real.log (2514 : ℕ)
      ∧ Real.log (2514 : ℕ) ≤ ((782963039/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2515 :
    ((97875351/12500000 : ℚ) : ℝ) ≤ Real.log (2515 : ℕ)
      ∧ Real.log (2515 : ℕ) ≤ ((783002809/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2516 :
    ((783042561/100000000 : ℚ) : ℝ) ≤ Real.log (2516 : ℕ)
      ∧ Real.log (2516 : ℕ) ≤ ((391521281/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2517 :
    ((783082299/100000000 : ℚ) : ℝ) ≤ Real.log (2517 : ℕ)
      ∧ Real.log (2517 : ℕ) ≤ ((7830823/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2518 :
    ((783122021/100000000 : ℚ) : ℝ) ≤ Real.log (2518 : ℕ)
      ∧ Real.log (2518 : ℕ) ≤ ((391561011/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2519 :
    ((783161727/100000000 : ℚ) : ℝ) ≤ Real.log (2519 : ℕ)
      ∧ Real.log (2519 : ℕ) ≤ ((6118451/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2520 :
    ((391600709/50000000 : ℚ) : ℝ) ≤ Real.log (2520 : ℕ)
      ∧ Real.log (2520 : ℕ) ≤ ((783201419/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2521 :
    ((195810273/25000000 : ℚ) : ℝ) ≤ Real.log (2521 : ℕ)
      ∧ Real.log (2521 : ℕ) ≤ ((783241093/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2522 :
    ((783280751/100000000 : ℚ) : ℝ) ≤ Real.log (2522 : ℕ)
      ∧ Real.log (2522 : ℕ) ≤ ((48955047/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2523 :
    ((391660197/50000000 : ℚ) : ℝ) ≤ Real.log (2523 : ℕ)
      ∧ Real.log (2523 : ℕ) ≤ ((156664079/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2524 :
    ((391680011/50000000 : ℚ) : ℝ) ≤ Real.log (2524 : ℕ)
      ∧ Real.log (2524 : ℕ) ≤ ((783360023/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2525 :
    ((391699817/50000000 : ℚ) : ℝ) ≤ Real.log (2525 : ℕ)
      ∧ Real.log (2525 : ℕ) ≤ ((156679927/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2526 :
    ((78343923/10000000 : ℚ) : ℝ) ≤ Real.log (2526 : ℕ)
      ∧ Real.log (2526 : ℕ) ≤ ((783439231/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2527 :
    ((78347881/10000000 : ℚ) : ℝ) ≤ Real.log (2527 : ℕ)
      ∧ Real.log (2527 : ℕ) ≤ ((783478811/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2528 :
    ((6268147/800000 : ℚ) : ℝ) ≤ Real.log (2528 : ℕ)
      ∧ Real.log (2528 : ℕ) ≤ ((97939797/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2529 :
    ((195889481/25000000 : ℚ) : ℝ) ≤ Real.log (2529 : ℕ)
      ∧ Real.log (2529 : ℕ) ≤ ((31342317/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2530 :
    ((391798729/50000000 : ℚ) : ℝ) ≤ Real.log (2530 : ℕ)
      ∧ Real.log (2530 : ℕ) ≤ ((783597459/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2531 :
    ((48977311/6250000 : ℚ) : ℝ) ≤ Real.log (2531 : ℕ)
      ∧ Real.log (2531 : ℕ) ≤ ((783636977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2532 :
    ((391838239/50000000 : ℚ) : ℝ) ≤ Real.log (2532 : ℕ)
      ∧ Real.log (2532 : ℕ) ≤ ((783676479/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2533 :
    ((195928991/25000000 : ℚ) : ℝ) ≤ Real.log (2533 : ℕ)
      ∧ Real.log (2533 : ℕ) ≤ ((783715967/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2534 :
    ((195938859/25000000 : ℚ) : ℝ) ≤ Real.log (2534 : ℕ)
      ∧ Real.log (2534 : ℕ) ≤ ((783755437/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2535 :
    ((783794891/100000000 : ℚ) : ℝ) ≤ Real.log (2535 : ℕ)
      ∧ Real.log (2535 : ℕ) ≤ ((195948723/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2536 :
    ((783834331/100000000 : ℚ) : ℝ) ≤ Real.log (2536 : ℕ)
      ∧ Real.log (2536 : ℕ) ≤ ((195958583/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2537 :
    ((391936877/50000000 : ℚ) : ℝ) ≤ Real.log (2537 : ℕ)
      ∧ Real.log (2537 : ℕ) ≤ ((783873757/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2538 :
    ((195978291/25000000 : ℚ) : ℝ) ≤ Real.log (2538 : ℕ)
      ∧ Real.log (2538 : ℕ) ≤ ((156782633/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2539 :
    ((391976279/50000000 : ℚ) : ℝ) ≤ Real.log (2539 : ℕ)
      ∧ Real.log (2539 : ℕ) ≤ ((783952559/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2540 :
    ((156798387/20000000 : ℚ) : ℝ) ≤ Real.log (2540 : ℕ)
      ∧ Real.log (2540 : ℕ) ≤ ((391995969/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2541 :
    ((392015649/50000000 : ℚ) : ℝ) ≤ Real.log (2541 : ℕ)
      ∧ Real.log (2541 : ℕ) ≤ ((784031299/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2542 :
    ((156814129/20000000 : ℚ) : ℝ) ≤ Real.log (2542 : ℕ)
      ∧ Real.log (2542 : ℕ) ≤ ((392035323/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2543 :
    ((98013747/12500000 : ℚ) : ℝ) ≤ Real.log (2543 : ℕ)
      ∧ Real.log (2543 : ℕ) ≤ ((784109977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2544 :
    ((196037323/25000000 : ℚ) : ℝ) ≤ Real.log (2544 : ℕ)
      ∧ Real.log (2544 : ℕ) ≤ ((784149293/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2545 :
    ((49011787/6250000 : ℚ) : ℝ) ≤ Real.log (2545 : ℕ)
      ∧ Real.log (2545 : ℕ) ≤ ((784188593/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2546 :
    ((784227877/100000000 : ℚ) : ℝ) ≤ Real.log (2546 : ℕ)
      ∧ Real.log (2546 : ℕ) ≤ ((392113939/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2547 :
    ((784267147/100000000 : ℚ) : ℝ) ≤ Real.log (2547 : ℕ)
      ∧ Real.log (2547 : ℕ) ≤ ((196066787/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2548 :
    ((784306401/100000000 : ℚ) : ℝ) ≤ Real.log (2548 : ℕ)
      ∧ Real.log (2548 : ℕ) ≤ ((392153201/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2549 :
    ((19608641/2500000 : ℚ) : ℝ) ≤ Real.log (2549 : ℕ)
      ∧ Real.log (2549 : ℕ) ≤ ((784345641/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2550 :
    ((784384863/100000000 : ℚ) : ℝ) ≤ Real.log (2550 : ℕ)
      ∧ Real.log (2550 : ℕ) ≤ ((24512027/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2551 :
    ((784424071/100000000 : ℚ) : ℝ) ≤ Real.log (2551 : ℕ)
      ∧ Real.log (2551 : ℕ) ≤ ((98053009/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2552 :
    ((24514477/3125000 : ℚ) : ℝ) ≤ Real.log (2552 : ℕ)
      ∧ Real.log (2552 : ℕ) ≤ ((156892653/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2553 :
    ((784502441/100000000 : ℚ) : ℝ) ≤ Real.log (2553 : ℕ)
      ∧ Real.log (2553 : ℕ) ≤ ((392251221/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2554 :
    ((784541603/100000000 : ℚ) : ℝ) ≤ Real.log (2554 : ℕ)
      ∧ Real.log (2554 : ℕ) ≤ ((196135401/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2555 :
    ((3138323/400000 : ℚ) : ℝ) ≤ Real.log (2555 : ℕ)
      ∧ Real.log (2555 : ℕ) ≤ ((784580751/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2556 :
    ((784619881/100000000 : ℚ) : ℝ) ≤ Real.log (2556 : ℕ)
      ∧ Real.log (2556 : ℕ) ≤ ((392309941/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2557 :
    ((784658997/100000000 : ℚ) : ℝ) ≤ Real.log (2557 : ℕ)
      ∧ Real.log (2557 : ℕ) ≤ ((392329499/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2558 :
    ((392349049/50000000 : ℚ) : ℝ) ≤ Real.log (2558 : ℕ)
      ∧ Real.log (2558 : ℕ) ≤ ((784698099/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2559 :
    ((784737183/100000000 : ℚ) : ℝ) ≤ Real.log (2559 : ℕ)
      ∧ Real.log (2559 : ℕ) ≤ ((24523037/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2560 :
    ((784776253/100000000 : ℚ) : ℝ) ≤ Real.log (2560 : ℕ)
      ∧ Real.log (2560 : ℕ) ≤ ((392388127/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2561 :
    ((196203827/25000000 : ℚ) : ℝ) ≤ Real.log (2561 : ℕ)
      ∧ Real.log (2561 : ℕ) ≤ ((784815309/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2562 :
    ((196213587/25000000 : ℚ) : ℝ) ≤ Real.log (2562 : ℕ)
      ∧ Real.log (2562 : ℕ) ≤ ((784854349/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2563 :
    ((196223343/25000000 : ℚ) : ℝ) ≤ Real.log (2563 : ℕ)
      ∧ Real.log (2563 : ℕ) ≤ ((784893373/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2564 :
    ((784932381/100000000 : ℚ) : ℝ) ≤ Real.log (2564 : ℕ)
      ∧ Real.log (2564 : ℕ) ≤ ((392466191/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2565 :
    ((6279771/800000 : ℚ) : ℝ) ≤ Real.log (2565 : ℕ)
      ∧ Real.log (2565 : ℕ) ≤ ((49060711/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2566 :
    ((392505177/50000000 : ℚ) : ℝ) ≤ Real.log (2566 : ℕ)
      ∧ Real.log (2566 : ℕ) ≤ ((157002071/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2567 :
    ((392524659/50000000 : ℚ) : ℝ) ≤ Real.log (2567 : ℕ)
      ∧ Real.log (2567 : ℕ) ≤ ((785049319/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2568 :
    ((392544133/50000000 : ℚ) : ℝ) ≤ Real.log (2568 : ℕ)
      ∧ Real.log (2568 : ℕ) ≤ ((785088267/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2569 :
    ((785127199/100000000 : ℚ) : ℝ) ≤ Real.log (2569 : ℕ)
      ∧ Real.log (2569 : ℕ) ≤ ((981409/125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2570 :
    ((785166117/100000000 : ℚ) : ℝ) ≤ Real.log (2570 : ℕ)
      ∧ Real.log (2570 : ℕ) ≤ ((392583059/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2571 :
    ((39260251/5000000 : ℚ) : ℝ) ≤ Real.log (2571 : ℕ)
      ∧ Real.log (2571 : ℕ) ≤ ((785205021/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2572 :
    ((196310977/25000000 : ℚ) : ℝ) ≤ Real.log (2572 : ℕ)
      ∧ Real.log (2572 : ℕ) ≤ ((785243909/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2573 :
    ((785282781/100000000 : ℚ) : ℝ) ≤ Real.log (2573 : ℕ)
      ∧ Real.log (2573 : ℕ) ≤ ((392641391/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2574 :
    ((392660819/50000000 : ℚ) : ℝ) ≤ Real.log (2574 : ℕ)
      ∧ Real.log (2574 : ℕ) ≤ ((785321639/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2575 :
    ((785360481/100000000 : ℚ) : ℝ) ≤ Real.log (2575 : ℕ)
      ∧ Real.log (2575 : ℕ) ≤ ((392680241/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2576 :
    ((196349827/25000000 : ℚ) : ℝ) ≤ Real.log (2576 : ℕ)
      ∧ Real.log (2576 : ℕ) ≤ ((785399309/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2577 :
    ((785438121/100000000 : ℚ) : ℝ) ≤ Real.log (2577 : ℕ)
      ∧ Real.log (2577 : ℕ) ≤ ((392719061/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2578 :
    ((392738459/50000000 : ℚ) : ℝ) ≤ Real.log (2578 : ℕ)
      ∧ Real.log (2578 : ℕ) ≤ ((785476919/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2579 :
    ((7855157/1000000 : ℚ) : ℝ) ≤ Real.log (2579 : ℕ)
      ∧ Real.log (2579 : ℕ) ≤ ((785515701/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2580 :
    ((785554467/100000000 : ℚ) : ℝ) ≤ Real.log (2580 : ℕ)
      ∧ Real.log (2580 : ℕ) ≤ ((196388617/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2581 :
    ((392796609/50000000 : ℚ) : ℝ) ≤ Real.log (2581 : ℕ)
      ∧ Real.log (2581 : ℕ) ≤ ((785593221/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2582 :
    ((785631957/100000000 : ℚ) : ℝ) ≤ Real.log (2582 : ℕ)
      ∧ Real.log (2582 : ℕ) ≤ ((392815979/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2583 :
    ((785670679/100000000 : ℚ) : ℝ) ≤ Real.log (2583 : ℕ)
      ∧ Real.log (2583 : ℕ) ≤ ((19641767/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2584 :
    ((392854693/50000000 : ℚ) : ℝ) ≤ Real.log (2584 : ℕ)
      ∧ Real.log (2584 : ℕ) ≤ ((785709387/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2585 :
    ((392874039/50000000 : ℚ) : ℝ) ≤ Real.log (2585 : ℕ)
      ∧ Real.log (2585 : ℕ) ≤ ((785748079/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2586 :
    ((157157351/20000000 : ℚ) : ℝ) ≤ Real.log (2586 : ℕ)
      ∧ Real.log (2586 : ℕ) ≤ ((196446689/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2587 :
    ((392912709/50000000 : ℚ) : ℝ) ≤ Real.log (2587 : ℕ)
      ∧ Real.log (2587 : ℕ) ≤ ((785825419/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2588 :
    ((157172813/20000000 : ℚ) : ℝ) ≤ Real.log (2588 : ℕ)
      ∧ Real.log (2588 : ℕ) ≤ ((392932033/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2589 :
    ((98237837/12500000 : ℚ) : ℝ) ≤ Real.log (2589 : ℕ)
      ∧ Real.log (2589 : ℕ) ≤ ((785902699/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2590 :
    ((157188263/20000000 : ℚ) : ℝ) ≤ Real.log (2590 : ℕ)
      ∧ Real.log (2590 : ℕ) ≤ ((196485329/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2591 :
    ((392989959/50000000 : ℚ) : ℝ) ≤ Real.log (2591 : ℕ)
      ∧ Real.log (2591 : ℕ) ≤ ((785979919/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2592 :
    ((157203701/20000000 : ℚ) : ℝ) ≤ Real.log (2592 : ℕ)
      ∧ Real.log (2592 : ℕ) ≤ ((393009253/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2593 :
    ((393028539/50000000 : ℚ) : ℝ) ≤ Real.log (2593 : ℕ)
      ∧ Real.log (2593 : ℕ) ≤ ((786057079/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2594 :
    ((196523909/25000000 : ℚ) : ℝ) ≤ Real.log (2594 : ℕ)
      ∧ Real.log (2594 : ℕ) ≤ ((786095637/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2595 :
    ((786134179/100000000 : ℚ) : ℝ) ≤ Real.log (2595 : ℕ)
      ∧ Real.log (2595 : ℕ) ≤ ((39306709/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2596 :
    ((786172707/100000000 : ℚ) : ℝ) ≤ Real.log (2596 : ℕ)
      ∧ Real.log (2596 : ℕ) ≤ ((196543177/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2597 :
    ((786211221/100000000 : ℚ) : ℝ) ≤ Real.log (2597 : ℕ)
      ∧ Real.log (2597 : ℕ) ≤ ((393105611/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2598 :
    ((786249719/100000000 : ℚ) : ℝ) ≤ Real.log (2598 : ℕ)
      ∧ Real.log (2598 : ℕ) ≤ ((19656243/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2599 :
    ((786288203/100000000 : ℚ) : ℝ) ≤ Real.log (2599 : ℕ)
      ∧ Real.log (2599 : ℕ) ≤ ((196572051/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2600 :
    ((49145417/6250000 : ℚ) : ℝ) ≤ Real.log (2600 : ℕ)
      ∧ Real.log (2600 : ℕ) ≤ ((786326673/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2601 :
    ((393182563/50000000 : ℚ) : ℝ) ≤ Real.log (2601 : ℕ)
      ∧ Real.log (2601 : ℕ) ≤ ((786365127/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2602 :
    ((157280713/20000000 : ℚ) : ℝ) ≤ Real.log (2602 : ℕ)
      ∧ Real.log (2602 : ℕ) ≤ ((393201783/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2603 :
    ((78644199/10000000 : ℚ) : ℝ) ≤ Real.log (2603 : ℕ)
      ∧ Real.log (2603 : ℕ) ≤ ((786441991/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2604 :
    ((1966201/250000 : ℚ) : ℝ) ≤ Real.log (2604 : ℕ)
      ∧ Real.log (2604 : ℕ) ≤ ((786480401/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2605 :
    ((157303759/20000000 : ℚ) : ℝ) ≤ Real.log (2605 : ℕ)
      ∧ Real.log (2605 : ℕ) ≤ ((196629699/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2606 :
    ((31462287/4000000 : ℚ) : ℝ) ≤ Real.log (2606 : ℕ)
      ∧ Real.log (2606 : ℕ) ≤ ((98319647/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2607 :
    ((786595541/100000000 : ℚ) : ℝ) ≤ Real.log (2607 : ℕ)
      ∧ Real.log (2607 : ℕ) ≤ ((393297771/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2608 :
    ((196658473/25000000 : ℚ) : ℝ) ≤ Real.log (2608 : ℕ)
      ∧ Real.log (2608 : ℕ) ≤ ((786633893/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2609 :
    ((196668057/25000000 : ℚ) : ℝ) ≤ Real.log (2609 : ℕ)
      ∧ Real.log (2609 : ℕ) ≤ ((786672229/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2610 :
    ((786710549/100000000 : ℚ) : ℝ) ≤ Real.log (2610 : ℕ)
      ∧ Real.log (2610 : ℕ) ≤ ((98338819/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2611 :
    ((98343607/12500000 : ℚ) : ℝ) ≤ Real.log (2611 : ℕ)
      ∧ Real.log (2611 : ℕ) ≤ ((786748857/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2612 :
    ((196696787/25000000 : ℚ) : ℝ) ≤ Real.log (2612 : ℕ)
      ∧ Real.log (2612 : ℕ) ≤ ((786787151/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2613 :
    ((393412713/50000000 : ℚ) : ℝ) ≤ Real.log (2613 : ℕ)
      ∧ Real.log (2613 : ℕ) ≤ ((786825427/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2614 :
    ((786863689/100000000 : ℚ) : ℝ) ≤ Real.log (2614 : ℕ)
      ∧ Real.log (2614 : ℕ) ≤ ((78686369/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2615 :
    ((786901937/100000000 : ℚ) : ℝ) ≤ Real.log (2615 : ℕ)
      ∧ Real.log (2615 : ℕ) ≤ ((393450969/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2616 :
    ((786940171/100000000 : ℚ) : ℝ) ≤ Real.log (2616 : ℕ)
      ∧ Real.log (2616 : ℕ) ≤ ((196735043/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2617 :
    ((78697839/10000000 : ℚ) : ℝ) ≤ Real.log (2617 : ℕ)
      ∧ Real.log (2617 : ℕ) ≤ ((786978391/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2618 :
    ((393508297/50000000 : ℚ) : ℝ) ≤ Real.log (2618 : ℕ)
      ∧ Real.log (2618 : ℕ) ≤ ((157403319/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2619 :
    ((12297731/1562500 : ℚ) : ℝ) ≤ Real.log (2619 : ℕ)
      ∧ Real.log (2619 : ℕ) ≤ ((157410957/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2620 :
    ((787092959/100000000 : ℚ) : ℝ) ≤ Real.log (2620 : ℕ)
      ∧ Real.log (2620 : ℕ) ≤ ((4919331/625000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2621 :
    ((9839139/1250000 : ℚ) : ℝ) ≤ Real.log (2621 : ℕ)
      ∧ Real.log (2621 : ℕ) ≤ ((787131121/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2622 :
    ((393584633/50000000 : ℚ) : ℝ) ≤ Real.log (2622 : ℕ)
      ∧ Real.log (2622 : ℕ) ≤ ((787169267/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2623 :
    ((196801849/25000000 : ℚ) : ℝ) ≤ Real.log (2623 : ℕ)
      ∧ Real.log (2623 : ℕ) ≤ ((787207399/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2624 :
    ((393622757/50000000 : ℚ) : ℝ) ≤ Real.log (2624 : ℕ)
      ∧ Real.log (2624 : ℕ) ≤ ((787245517/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2625 :
    ((787283617/100000000 : ℚ) : ℝ) ≤ Real.log (2625 : ℕ)
      ∧ Real.log (2625 : ℕ) ≤ ((393641809/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2626 :
    ((157464341/20000000 : ℚ) : ℝ) ≤ Real.log (2626 : ℕ)
      ∧ Real.log (2626 : ℕ) ≤ ((393660853/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2627 :
    ((787359777/100000000 : ℚ) : ℝ) ≤ Real.log (2627 : ℕ)
      ∧ Real.log (2627 : ℕ) ≤ ((39367989/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2628 :
    ((196849459/25000000 : ℚ) : ℝ) ≤ Real.log (2628 : ℕ)
      ∧ Real.log (2628 : ℕ) ≤ ((787397839/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2629 :
    ((393717941/50000000 : ℚ) : ℝ) ≤ Real.log (2629 : ℕ)
      ∧ Real.log (2629 : ℕ) ≤ ((787435883/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2630 :
    ((98434239/12500000 : ℚ) : ℝ) ≤ Real.log (2630 : ℕ)
      ∧ Real.log (2630 : ℕ) ≤ ((787473913/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2631 :
    ((98438991/12500000 : ℚ) : ℝ) ≤ Real.log (2631 : ℕ)
      ∧ Real.log (2631 : ℕ) ≤ ((787511929/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2632 :
    ((787549929/100000000 : ℚ) : ℝ) ≤ Real.log (2632 : ℕ)
      ∧ Real.log (2632 : ℕ) ≤ ((78754993/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2633 :
    ((157517583/20000000 : ℚ) : ℝ) ≤ Real.log (2633 : ℕ)
      ∧ Real.log (2633 : ℕ) ≤ ((196896979/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2634 :
    ((24613309/3125000 : ℚ) : ℝ) ≤ Real.log (2634 : ℕ)
      ∧ Real.log (2634 : ℕ) ≤ ((787625889/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2635 :
    ((393831923/50000000 : ℚ) : ℝ) ≤ Real.log (2635 : ℕ)
      ∧ Real.log (2635 : ℕ) ≤ ((787663847/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2636 :
    ((787701789/100000000 : ℚ) : ℝ) ≤ Real.log (2636 : ℕ)
      ∧ Real.log (2636 : ℕ) ≤ ((78770179/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2637 :
    ((393869859/50000000 : ℚ) : ℝ) ≤ Real.log (2637 : ℕ)
      ∧ Real.log (2637 : ℕ) ≤ ((787739719/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2638 :
    ((787777633/100000000 : ℚ) : ℝ) ≤ Real.log (2638 : ℕ)
      ∧ Real.log (2638 : ℕ) ≤ ((393888817/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2639 :
    ((787815533/100000000 : ℚ) : ℝ) ≤ Real.log (2639 : ℕ)
      ∧ Real.log (2639 : ℕ) ≤ ((393907767/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2640 :
    ((787853419/100000000 : ℚ) : ℝ) ≤ Real.log (2640 : ℕ)
      ∧ Real.log (2640 : ℕ) ≤ ((39392671/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2641 :
    ((787891291/100000000 : ℚ) : ℝ) ≤ Real.log (2641 : ℕ)
      ∧ Real.log (2641 : ℕ) ≤ ((196972823/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2642 :
    ((196982287/25000000 : ℚ) : ℝ) ≤ Real.log (2642 : ℕ)
      ∧ Real.log (2642 : ℕ) ≤ ((787929149/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2643 :
    ((787966991/100000000 : ℚ) : ℝ) ≤ Real.log (2643 : ℕ)
      ∧ Real.log (2643 : ℕ) ≤ ((49247937/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2644 :
    ((39400241/5000000 : ℚ) : ℝ) ≤ Real.log (2644 : ℕ)
      ∧ Real.log (2644 : ℕ) ≤ ((788004821/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2645 :
    ((394021317/50000000 : ℚ) : ℝ) ≤ Real.log (2645 : ℕ)
      ∧ Real.log (2645 : ℕ) ≤ ((157608527/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2646 :
    ((394040217/50000000 : ℚ) : ℝ) ≤ Real.log (2646 : ℕ)
      ∧ Real.log (2646 : ℕ) ≤ ((157616087/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2647 :
    ((39405911/5000000 : ℚ) : ℝ) ≤ Real.log (2647 : ℕ)
      ∧ Real.log (2647 : ℕ) ≤ ((788118221/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2648 :
    ((788155991/100000000 : ℚ) : ℝ) ≤ Real.log (2648 : ℕ)
      ∧ Real.log (2648 : ℕ) ≤ ((98519499/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2649 :
    ((197048437/25000000 : ℚ) : ℝ) ≤ Real.log (2649 : ℕ)
      ∧ Real.log (2649 : ℕ) ≤ ((788193749/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2650 :
    ((788231491/100000000 : ℚ) : ℝ) ≤ Real.log (2650 : ℕ)
      ∧ Real.log (2650 : ℕ) ≤ ((197057873/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2651 :
    ((39413461/5000000 : ℚ) : ℝ) ≤ Real.log (2651 : ℕ)
      ∧ Real.log (2651 : ℕ) ≤ ((788269221/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2652 :
    ((157661387/20000000 : ℚ) : ℝ) ≤ Real.log (2652 : ℕ)
      ∧ Real.log (2652 : ℕ) ≤ ((98538367/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2653 :
    ((157668927/20000000 : ℚ) : ℝ) ≤ Real.log (2653 : ℕ)
      ∧ Real.log (2653 : ℕ) ≤ ((197086159/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2654 :
    ((788382321/100000000 : ℚ) : ℝ) ≤ Real.log (2654 : ℕ)
      ∧ Real.log (2654 : ℕ) ≤ ((394191161/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2655 :
    ((788419993/100000000 : ℚ) : ℝ) ≤ Real.log (2655 : ℕ)
      ∧ Real.log (2655 : ℕ) ≤ ((394209997/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2656 :
    ((788457651/100000000 : ℚ) : ℝ) ≤ Real.log (2656 : ℕ)
      ∧ Real.log (2656 : ℕ) ≤ ((197114413/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2657 :
    ((394247647/50000000 : ℚ) : ℝ) ≤ Real.log (2657 : ℕ)
      ∧ Real.log (2657 : ℕ) ≤ ((157699059/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2658 :
    ((788532923/100000000 : ℚ) : ℝ) ≤ Real.log (2658 : ℕ)
      ∧ Real.log (2658 : ℕ) ≤ ((197133231/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2659 :
    ((788570539/100000000 : ℚ) : ℝ) ≤ Real.log (2659 : ℕ)
      ∧ Real.log (2659 : ℕ) ≤ ((39428527/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2660 :
    ((39430407/5000000 : ℚ) : ℝ) ≤ Real.log (2660 : ℕ)
      ∧ Real.log (2660 : ℕ) ≤ ((788608141/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2661 :
    ((788645727/100000000 : ℚ) : ℝ) ≤ Real.log (2661 : ℕ)
      ∧ Real.log (2661 : ℕ) ≤ ((24645179/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2662 :
    ((788683299/100000000 : ℚ) : ℝ) ≤ Real.log (2662 : ℕ)
      ∧ Real.log (2662 : ℕ) ≤ ((7886833/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2663 :
    ((394360429/50000000 : ℚ) : ℝ) ≤ Real.log (2663 : ℕ)
      ∧ Real.log (2663 : ℕ) ≤ ((788720859/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2664 :
    ((788758403/100000000 : ℚ) : ℝ) ≤ Real.log (2664 : ℕ)
      ∧ Real.log (2664 : ℕ) ≤ ((197189601/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2665 :
    ((788795933/100000000 : ℚ) : ℝ) ≤ Real.log (2665 : ℕ)
      ∧ Real.log (2665 : ℕ) ≤ ((394397967/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2666 :
    ((15776669/2000000 : ℚ) : ℝ) ≤ Real.log (2666 : ℕ)
      ∧ Real.log (2666 : ℕ) ≤ ((788833451/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2667 :
    ((98608869/12500000 : ℚ) : ℝ) ≤ Real.log (2667 : ℕ)
      ∧ Real.log (2667 : ℕ) ≤ ((788870953/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2668 :
    ((19722711/2500000 : ℚ) : ℝ) ≤ Real.log (2668 : ℕ)
      ∧ Real.log (2668 : ℕ) ≤ ((788908441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2669 :
    ((394472957/50000000 : ℚ) : ℝ) ≤ Real.log (2669 : ℕ)
      ∧ Real.log (2669 : ℕ) ≤ ((157789183/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2670 :
    ((6311867/800000 : ℚ) : ℝ) ≤ Real.log (2670 : ℕ)
      ∧ Real.log (2670 : ℕ) ≤ ((49311461/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2671 :
    ((789020821/100000000 : ℚ) : ℝ) ≤ Real.log (2671 : ℕ)
      ∧ Real.log (2671 : ℕ) ≤ ((394510411/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2672 :
    ((789058253/100000000 : ℚ) : ℝ) ≤ Real.log (2672 : ℕ)
      ∧ Real.log (2672 : ℕ) ≤ ((394529127/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2673 :
    ((789095671/100000000 : ℚ) : ℝ) ≤ Real.log (2673 : ℕ)
      ∧ Real.log (2673 : ℕ) ≤ ((98636959/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2674 :
    ((31565323/4000000 : ℚ) : ℝ) ≤ Real.log (2674 : ℕ)
      ∧ Real.log (2674 : ℕ) ≤ ((197283269/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2675 :
    ((157834093/20000000 : ℚ) : ℝ) ≤ Real.log (2675 : ℕ)
      ∧ Real.log (2675 : ℕ) ≤ ((394585233/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2676 :
    ((394603921/50000000 : ℚ) : ℝ) ≤ Real.log (2676 : ℕ)
      ∧ Real.log (2676 : ℕ) ≤ ((789207843/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2677 :
    ((197311301/25000000 : ℚ) : ℝ) ≤ Real.log (2677 : ℕ)
      ∧ Real.log (2677 : ℕ) ≤ ((157849041/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2678 :
    ((98660319/12500000 : ℚ) : ℝ) ≤ Real.log (2678 : ℕ)
      ∧ Real.log (2678 : ℕ) ≤ ((789282553/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2679 :
    ((157863977/20000000 : ℚ) : ℝ) ≤ Real.log (2679 : ℕ)
      ∧ Real.log (2679 : ℕ) ≤ ((49332493/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2680 :
    ((789357207/100000000 : ℚ) : ℝ) ≤ Real.log (2680 : ℕ)
      ∧ Real.log (2680 : ℕ) ≤ ((98669651/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2681 :
    ((789394513/100000000 : ℚ) : ℝ) ≤ Real.log (2681 : ℕ)
      ∧ Real.log (2681 : ℕ) ≤ ((394697257/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2682 :
    ((394715903/50000000 : ℚ) : ℝ) ≤ Real.log (2682 : ℕ)
      ∧ Real.log (2682 : ℕ) ≤ ((789431807/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2683 :
    ((157893817/20000000 : ℚ) : ℝ) ≤ Real.log (2683 : ℕ)
      ∧ Real.log (2683 : ℕ) ≤ ((394734543/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2684 :
    ((789506349/100000000 : ℚ) : ℝ) ≤ Real.log (2684 : ℕ)
      ∧ Real.log (2684 : ℕ) ≤ ((15790127/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2685 :
    ((1973859/250000 : ℚ) : ℝ) ≤ Real.log (2685 : ℕ)
      ∧ Real.log (2685 : ℕ) ≤ ((789543601/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2686 :
    ((789580837/100000000 : ℚ) : ℝ) ≤ Real.log (2686 : ℕ)
      ∧ Real.log (2686 : ℕ) ≤ ((394790419/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2687 :
    ((39480903/5000000 : ℚ) : ℝ) ≤ Real.log (2687 : ℕ)
      ∧ Real.log (2687 : ℕ) ≤ ((789618061/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2688 :
    ((78965527/10000000 : ℚ) : ℝ) ≤ Real.log (2688 : ℕ)
      ∧ Real.log (2688 : ℕ) ≤ ((789655271/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2689 :
    ((157938493/20000000 : ℚ) : ℝ) ≤ Real.log (2689 : ℕ)
      ∧ Real.log (2689 : ℕ) ≤ ((394846233/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2690 :
    ((789729647/100000000 : ℚ) : ℝ) ≤ Real.log (2690 : ℕ)
      ∧ Real.log (2690 : ℕ) ≤ ((49358103/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2691 :
    ((157953363/20000000 : ℚ) : ℝ) ≤ Real.log (2691 : ℕ)
      ∧ Real.log (2691 : ℕ) ≤ ((24680213/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2692 :
    ((789803969/100000000 : ℚ) : ℝ) ≤ Real.log (2692 : ℕ)
      ∧ Real.log (2692 : ℕ) ≤ ((78980397/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2693 :
    ((789841109/100000000 : ℚ) : ℝ) ≤ Real.log (2693 : ℕ)
      ∧ Real.log (2693 : ℕ) ≤ ((78984111/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2694 :
    ((157975647/20000000 : ℚ) : ℝ) ≤ Real.log (2694 : ℕ)
      ∧ Real.log (2694 : ℕ) ≤ ((197469559/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2695 :
    ((197478837/25000000 : ℚ) : ℝ) ≤ Real.log (2695 : ℕ)
      ∧ Real.log (2695 : ℕ) ≤ ((789915349/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2696 :
    ((789952447/100000000 : ℚ) : ℝ) ≤ Real.log (2696 : ℕ)
      ∧ Real.log (2696 : ℕ) ≤ ((12343007/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2697 :
    ((197497383/25000000 : ℚ) : ℝ) ≤ Real.log (2697 : ℕ)
      ∧ Real.log (2697 : ℕ) ≤ ((789989533/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2698 :
    ((790026603/100000000 : ℚ) : ℝ) ≤ Real.log (2698 : ℕ)
      ∧ Real.log (2698 : ℕ) ≤ ((197506651/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2699 :
    ((790063661/100000000 : ℚ) : ℝ) ≤ Real.log (2699 : ℕ)
      ∧ Real.log (2699 : ℕ) ≤ ((395031831/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2700 :
    ((158020141/20000000 : ℚ) : ℝ) ≤ Real.log (2700 : ℕ)
      ∧ Real.log (2700 : ℕ) ≤ ((395050353/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2701 :
    ((158027547/20000000 : ℚ) : ℝ) ≤ Real.log (2701 : ℕ)
      ∧ Real.log (2701 : ℕ) ≤ ((98767217/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2702 :
    ((790174751/100000000 : ℚ) : ℝ) ≤ Real.log (2702 : ℕ)
      ∧ Real.log (2702 : ℕ) ≤ ((24692961/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2703 :
    ((395105877/50000000 : ℚ) : ℝ) ≤ Real.log (2703 : ℕ)
      ∧ Real.log (2703 : ℕ) ≤ ((158042351/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2704 :
    ((790248743/100000000 : ℚ) : ℝ) ≤ Real.log (2704 : ℕ)
      ∧ Real.log (2704 : ℕ) ≤ ((98781093/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2705 :
    ((790285719/100000000 : ℚ) : ℝ) ≤ Real.log (2705 : ℕ)
      ∧ Real.log (2705 : ℕ) ≤ ((19757143/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2706 :
    ((19758067/2500000 : ℚ) : ℝ) ≤ Real.log (2706 : ℕ)
      ∧ Real.log (2706 : ℕ) ≤ ((790322681/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2707 :
    ((790359627/100000000 : ℚ) : ℝ) ≤ Real.log (2707 : ℕ)
      ∧ Real.log (2707 : ℕ) ≤ ((79035963/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2708 :
    ((790396563/100000000 : ℚ) : ℝ) ≤ Real.log (2708 : ℕ)
      ∧ Real.log (2708 : ℕ) ≤ ((197599141/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2709 :
    ((197608371/25000000 : ℚ) : ℝ) ≤ Real.log (2709 : ℕ)
      ∧ Real.log (2709 : ℕ) ≤ ((158086697/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2710 :
    ((790470391/100000000 : ℚ) : ℝ) ≤ Real.log (2710 : ℕ)
      ∧ Real.log (2710 : ℕ) ≤ ((98808799/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2711 :
    ((197626821/25000000 : ℚ) : ℝ) ≤ Real.log (2711 : ℕ)
      ∧ Real.log (2711 : ℕ) ≤ ((158101457/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2712 :
    ((197636041/25000000 : ℚ) : ℝ) ≤ Real.log (2712 : ℕ)
      ∧ Real.log (2712 : ℕ) ≤ ((158108833/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2713 :
    ((790581031/100000000 : ℚ) : ℝ) ≤ Real.log (2713 : ℕ)
      ∧ Real.log (2713 : ℕ) ≤ ((98822629/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2714 :
    ((790617883/100000000 : ℚ) : ℝ) ≤ Real.log (2714 : ℕ)
      ∧ Real.log (2714 : ℕ) ≤ ((395308943/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2715 :
    ((790654723/100000000 : ℚ) : ℝ) ≤ Real.log (2715 : ℕ)
      ∧ Real.log (2715 : ℕ) ≤ ((197663681/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2716 :
    ((197672887/25000000 : ℚ) : ℝ) ≤ Real.log (2716 : ℕ)
      ∧ Real.log (2716 : ℕ) ≤ ((790691549/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2717 :
    ((19768209/2500000 : ℚ) : ℝ) ≤ Real.log (2717 : ℕ)
      ∧ Real.log (2717 : ℕ) ≤ ((790728361/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2718 :
    ((790765159/100000000 : ℚ) : ℝ) ≤ Real.log (2718 : ℕ)
      ∧ Real.log (2718 : ℕ) ≤ ((19769129/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2719 :
    ((98850243/12500000 : ℚ) : ℝ) ≤ Real.log (2719 : ℕ)
      ∧ Real.log (2719 : ℕ) ≤ ((158160389/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2720 :
    ((158167743/20000000 : ℚ) : ℝ) ≤ Real.log (2720 : ℕ)
      ∧ Real.log (2720 : ℕ) ≤ ((197709679/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2721 :
    ((790875473/100000000 : ℚ) : ℝ) ≤ Real.log (2721 : ℕ)
      ∧ Real.log (2721 : ℕ) ≤ ((395437737/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2722 :
    ((395456109/50000000 : ℚ) : ℝ) ≤ Real.log (2722 : ℕ)
      ∧ Real.log (2722 : ℕ) ≤ ((790912219/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2723 :
    ((790948949/100000000 : ℚ) : ℝ) ≤ Real.log (2723 : ℕ)
      ∧ Real.log (2723 : ℕ) ≤ ((15818979/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2724 :
    ((395492833/50000000 : ℚ) : ℝ) ≤ Real.log (2724 : ℕ)
      ∧ Real.log (2724 : ℕ) ≤ ((790985667/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2725 :
    ((79102237/10000000 : ℚ) : ℝ) ≤ Real.log (2725 : ℕ)
      ∧ Real.log (2725 : ℕ) ≤ ((791022371/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2726 :
    ((791059061/100000000 : ℚ) : ℝ) ≤ Real.log (2726 : ℕ)
      ∧ Real.log (2726 : ℕ) ≤ ((395529531/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2727 :
    ((395547869/50000000 : ℚ) : ℝ) ≤ Real.log (2727 : ℕ)
      ∧ Real.log (2727 : ℕ) ≤ ((791095739/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2728 :
    ((791132401/100000000 : ℚ) : ℝ) ≤ Real.log (2728 : ℕ)
      ∧ Real.log (2728 : ℕ) ≤ ((395566201/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2729 :
    ((197792263/25000000 : ℚ) : ℝ) ≤ Real.log (2729 : ℕ)
      ∧ Real.log (2729 : ℕ) ≤ ((791169053/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2730 :
    ((98900711/12500000 : ℚ) : ℝ) ≤ Real.log (2730 : ℕ)
      ∧ Real.log (2730 : ℕ) ≤ ((791205689/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2731 :
    ((98905289/12500000 : ℚ) : ℝ) ≤ Real.log (2731 : ℕ)
      ∧ Real.log (2731 : ℕ) ≤ ((791242313/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2732 :
    ((395639461/50000000 : ℚ) : ℝ) ≤ Real.log (2732 : ℕ)
      ∧ Real.log (2732 : ℕ) ≤ ((791278923/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2733 :
    ((395657759/50000000 : ℚ) : ℝ) ≤ Real.log (2733 : ℕ)
      ∧ Real.log (2733 : ℕ) ≤ ((791315519/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2734 :
    ((791352101/100000000 : ℚ) : ℝ) ≤ Real.log (2734 : ℕ)
      ∧ Real.log (2734 : ℕ) ≤ ((395676051/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2735 :
    ((791388671/100000000 : ℚ) : ℝ) ≤ Real.log (2735 : ℕ)
      ∧ Real.log (2735 : ℕ) ≤ ((3091362/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2736 :
    ((791425227/100000000 : ℚ) : ℝ) ≤ Real.log (2736 : ℕ)
      ∧ Real.log (2736 : ℕ) ≤ ((197856307/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2737 :
    ((79146177/10000000 : ℚ) : ℝ) ≤ Real.log (2737 : ℕ)
      ∧ Real.log (2737 : ℕ) ≤ ((791461771/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2738 :
    ((7914983/1000000 : ℚ) : ℝ) ≤ Real.log (2738 : ℕ)
      ∧ Real.log (2738 : ℕ) ≤ ((791498301/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2739 :
    ((24735463/3125000 : ℚ) : ℝ) ≤ Real.log (2739 : ℕ)
      ∧ Real.log (2739 : ℕ) ≤ ((791534817/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2740 :
    ((791571319/100000000 : ℚ) : ℝ) ≤ Real.log (2740 : ℕ)
      ∧ Real.log (2740 : ℕ) ≤ ((19789283/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2741 :
    ((791607809/100000000 : ℚ) : ℝ) ≤ Real.log (2741 : ℕ)
      ∧ Real.log (2741 : ℕ) ≤ ((79160781/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2742 :
    ((158328857/20000000 : ℚ) : ℝ) ≤ Real.log (2742 : ℕ)
      ∧ Real.log (2742 : ℕ) ≤ ((6184721/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2743 :
    ((791680749/100000000 : ℚ) : ℝ) ≤ Real.log (2743 : ℕ)
      ∧ Real.log (2743 : ℕ) ≤ ((3166723/400000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2744 :
    ((395858599/50000000 : ℚ) : ℝ) ≤ Real.log (2744 : ℕ)
      ∧ Real.log (2744 : ℕ) ≤ ((791717199/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2745 :
    ((158350727/20000000 : ℚ) : ℝ) ≤ Real.log (2745 : ℕ)
      ∧ Real.log (2745 : ℕ) ≤ ((197938409/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2746 :
    ((395895029/50000000 : ℚ) : ℝ) ≤ Real.log (2746 : ℕ)
      ∧ Real.log (2746 : ℕ) ≤ ((791790059/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2747 :
    ((197956617/25000000 : ℚ) : ℝ) ≤ Real.log (2747 : ℕ)
      ∧ Real.log (2747 : ℕ) ≤ ((791826469/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2748 :
    ((158372573/20000000 : ℚ) : ℝ) ≤ Real.log (2748 : ℕ)
      ∧ Real.log (2748 : ℕ) ≤ ((395931433/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2749 :
    ((49493703/6250000 : ℚ) : ℝ) ≤ Real.log (2749 : ℕ)
      ∧ Real.log (2749 : ℕ) ≤ ((791899249/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2750 :
    ((791935619/100000000 : ℚ) : ℝ) ≤ Real.log (2750 : ℕ)
      ∧ Real.log (2750 : ℕ) ≤ ((39596781/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2751 :
    ((98996497/12500000 : ℚ) : ℝ) ≤ Real.log (2751 : ℕ)
      ∧ Real.log (2751 : ℕ) ≤ ((791971977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2752 :
    ((792008319/100000000 : ℚ) : ℝ) ≤ Real.log (2752 : ℕ)
      ∧ Real.log (2752 : ℕ) ≤ ((1237513/156250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2753 :
    ((15840893/2000000 : ℚ) : ℝ) ≤ Real.log (2753 : ℕ)
      ∧ Real.log (2753 : ℕ) ≤ ((792044651/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2754 :
    ((792080967/100000000 : ℚ) : ℝ) ≤ Real.log (2754 : ℕ)
      ∧ Real.log (2754 : ℕ) ≤ ((99010121/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2755 :
    ((99014659/12500000 : ℚ) : ℝ) ≤ Real.log (2755 : ℕ)
      ∧ Real.log (2755 : ℕ) ≤ ((792117273/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2756 :
    ((792153563/100000000 : ℚ) : ℝ) ≤ Real.log (2756 : ℕ)
      ∧ Real.log (2756 : ℕ) ≤ ((198038391/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2757 :
    ((792189841/100000000 : ℚ) : ℝ) ≤ Real.log (2757 : ℕ)
      ∧ Real.log (2757 : ℕ) ≤ ((396094921/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2758 :
    ((158445221/20000000 : ℚ) : ℝ) ≤ Real.log (2758 : ℕ)
      ∧ Real.log (2758 : ℕ) ≤ ((396113053/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2759 :
    ((792262357/100000000 : ℚ) : ℝ) ≤ Real.log (2759 : ℕ)
      ∧ Real.log (2759 : ℕ) ≤ ((396131179/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2760 :
    ((158459719/20000000 : ℚ) : ℝ) ≤ Real.log (2760 : ℕ)
      ∧ Real.log (2760 : ℕ) ≤ ((198074649/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2761 :
    ((792334821/100000000 : ℚ) : ℝ) ≤ Real.log (2761 : ℕ)
      ∧ Real.log (2761 : ℕ) ≤ ((396167411/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2762 :
    ((792371033/100000000 : ℚ) : ℝ) ≤ Real.log (2762 : ℕ)
      ∧ Real.log (2762 : ℕ) ≤ ((396185517/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2763 :
    ((12381363/1562500 : ℚ) : ℝ) ≤ Real.log (2763 : ℕ)
      ∧ Real.log (2763 : ℕ) ≤ ((792407233/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2764 :
    ((396221709/50000000 : ℚ) : ℝ) ≤ Real.log (2764 : ℕ)
      ∧ Real.log (2764 : ℕ) ≤ ((792443419/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2765 :
    ((792479591/100000000 : ℚ) : ℝ) ≤ Real.log (2765 : ℕ)
      ∧ Real.log (2765 : ℕ) ≤ ((99059949/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2766 :
    ((792515751/100000000 : ℚ) : ℝ) ≤ Real.log (2766 : ℕ)
      ∧ Real.log (2766 : ℕ) ≤ ((99064469/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2767 :
    ((99068987/12500000 : ℚ) : ℝ) ≤ Real.log (2767 : ℕ)
      ∧ Real.log (2767 : ℕ) ≤ ((792551899/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2768 :
    ((792588031/100000000 : ℚ) : ℝ) ≤ Real.log (2768 : ℕ)
      ∧ Real.log (2768 : ℕ) ≤ ((3096047/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2769 :
    ((99078019/12500000 : ℚ) : ℝ) ≤ Real.log (2769 : ℕ)
      ∧ Real.log (2769 : ℕ) ≤ ((792624153/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2770 :
    ((792660259/100000000 : ℚ) : ℝ) ≤ Real.log (2770 : ℕ)
      ∧ Real.log (2770 : ℕ) ≤ ((39633013/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2771 :
    ((396348177/50000000 : ℚ) : ℝ) ≤ Real.log (2771 : ℕ)
      ∧ Real.log (2771 : ℕ) ≤ ((158539271/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2772 :
    ((158546487/20000000 : ℚ) : ℝ) ≤ Real.log (2772 : ℕ)
      ∧ Real.log (2772 : ℕ) ≤ ((396366219/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2773 :
    ((99096063/12500000 : ℚ) : ℝ) ≤ Real.log (2773 : ℕ)
      ∧ Real.log (2773 : ℕ) ≤ ((158553701/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2774 :
    ((9910057/1250000 : ℚ) : ℝ) ≤ Real.log (2774 : ℕ)
      ∧ Real.log (2774 : ℕ) ≤ ((792804561/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2775 :
    ((396420301/50000000 : ℚ) : ℝ) ≤ Real.log (2775 : ℕ)
      ∧ Real.log (2775 : ℕ) ≤ ((792840603/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2776 :
    ((99109579/12500000 : ℚ) : ℝ) ≤ Real.log (2776 : ℕ)
      ∧ Real.log (2776 : ℕ) ≤ ((792876633/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2777 :
    ((99114081/12500000 : ℚ) : ℝ) ≤ Real.log (2777 : ℕ)
      ∧ Real.log (2777 : ℕ) ≤ ((792912649/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2778 :
    ((198237163/25000000 : ℚ) : ℝ) ≤ Real.log (2778 : ℕ)
      ∧ Real.log (2778 : ℕ) ≤ ((792948653/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2779 :
    ((792984641/100000000 : ℚ) : ℝ) ≤ Real.log (2779 : ℕ)
      ∧ Real.log (2779 : ℕ) ≤ ((198246161/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2780 :
    ((39651031/5000000 : ℚ) : ℝ) ≤ Real.log (2780 : ℕ)
      ∧ Real.log (2780 : ℕ) ≤ ((793020621/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2781 :
    ((158611317/20000000 : ℚ) : ℝ) ≤ Real.log (2781 : ℕ)
      ∧ Real.log (2781 : ℕ) ≤ ((396528293/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2782 :
    ((793092537/100000000 : ℚ) : ℝ) ≤ Real.log (2782 : ℕ)
      ∧ Real.log (2782 : ℕ) ≤ ((396546269/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2783 :
    ((198282119/25000000 : ℚ) : ℝ) ≤ Real.log (2783 : ℕ)
      ∧ Real.log (2783 : ℕ) ≤ ((793128477/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2784 :
    ((396582201/50000000 : ℚ) : ℝ) ≤ Real.log (2784 : ℕ)
      ∧ Real.log (2784 : ℕ) ≤ ((793164403/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2785 :
    ((158640063/20000000 : ℚ) : ℝ) ≤ Real.log (2785 : ℕ)
      ∧ Real.log (2785 : ℕ) ≤ ((198300079/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2786 :
    ((158647243/20000000 : ℚ) : ℝ) ≤ Real.log (2786 : ℕ)
      ∧ Real.log (2786 : ℕ) ≤ ((99154527/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2787 :
    ((396636051/50000000 : ℚ) : ℝ) ≤ Real.log (2787 : ℕ)
      ∧ Real.log (2787 : ℕ) ≤ ((793272103/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2788 :
    ((793307977/100000000 : ℚ) : ℝ) ≤ Real.log (2788 : ℕ)
      ∧ Real.log (2788 : ℕ) ≤ ((396653989/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2789 :
    ((396671919/50000000 : ℚ) : ℝ) ≤ Real.log (2789 : ℕ)
      ∧ Real.log (2789 : ℕ) ≤ ((793343839/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2790 :
    ((793379687/100000000 : ℚ) : ℝ) ≤ Real.log (2790 : ℕ)
      ∧ Real.log (2790 : ℕ) ≤ ((99172461/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2791 :
    ((793415523/100000000 : ℚ) : ℝ) ≤ Real.log (2791 : ℕ)
      ∧ Real.log (2791 : ℕ) ≤ ((198353881/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2792 :
    ((396725673/50000000 : ℚ) : ℝ) ≤ Real.log (2792 : ℕ)
      ∧ Real.log (2792 : ℕ) ≤ ((793451347/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2793 :
    ((198371789/25000000 : ℚ) : ℝ) ≤ Real.log (2793 : ℕ)
      ∧ Real.log (2793 : ℕ) ≤ ((793487157/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2794 :
    ((99190369/12500000 : ℚ) : ℝ) ≤ Real.log (2794 : ℕ)
      ∧ Real.log (2794 : ℕ) ≤ ((158704591/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2795 :
    ((396779369/50000000 : ℚ) : ℝ) ≤ Real.log (2795 : ℕ)
      ∧ Real.log (2795 : ℕ) ≤ ((793558739/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2796 :
    ((79359451/10000000 : ℚ) : ℝ) ≤ Real.log (2796 : ℕ)
      ∧ Real.log (2796 : ℕ) ≤ ((793594511/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2797 :
    ((793630269/100000000 : ℚ) : ℝ) ≤ Real.log (2797 : ℕ)
      ∧ Real.log (2797 : ℕ) ≤ ((79363027/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2798 :
    ((158733203/20000000 : ℚ) : ℝ) ≤ Real.log (2798 : ℕ)
      ∧ Real.log (2798 : ℕ) ≤ ((24802063/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2799 :
    ((198425437/25000000 : ℚ) : ℝ) ≤ Real.log (2799 : ℕ)
      ∧ Real.log (2799 : ℕ) ≤ ((793701749/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2800 :
    ((793737469/100000000 : ℚ) : ℝ) ≤ Real.log (2800 : ℕ)
      ∧ Real.log (2800 : ℕ) ≤ ((79373747/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2801 :
    ((793773177/100000000 : ℚ) : ℝ) ≤ Real.log (2801 : ℕ)
      ∧ Real.log (2801 : ℕ) ≤ ((396886589/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2802 :
    ((99226109/12500000 : ℚ) : ℝ) ≤ Real.log (2802 : ℕ)
      ∧ Real.log (2802 : ℕ) ≤ ((793808873/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2803 :
    ((158768911/20000000 : ℚ) : ℝ) ≤ Real.log (2803 : ℕ)
      ∧ Real.log (2803 : ℕ) ≤ ((198461139/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2804 :
    ((24808757/3125000 : ℚ) : ℝ) ≤ Real.log (2804 : ℕ)
      ∧ Real.log (2804 : ℕ) ≤ ((31755209/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2805 :
    ((793915881/100000000 : ℚ) : ℝ) ≤ Real.log (2805 : ℕ)
      ∧ Real.log (2805 : ℕ) ≤ ((396957941/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2806 :
    ((396975763/50000000 : ℚ) : ℝ) ≤ Real.log (2806 : ℕ)
      ∧ Real.log (2806 : ℕ) ≤ ((793951527/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2807 :
    ((793987157/100000000 : ℚ) : ℝ) ≤ Real.log (2807 : ℕ)
      ∧ Real.log (2807 : ℕ) ≤ ((396993579/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2808 :
    ((99252847/12500000 : ℚ) : ℝ) ≤ Real.log (2808 : ℕ)
      ∧ Real.log (2808 : ℕ) ≤ ((794022777/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2809 :
    ((397029191/50000000 : ℚ) : ℝ) ≤ Real.log (2809 : ℕ)
      ∧ Real.log (2809 : ℕ) ≤ ((794058383/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2810 :
    ((99261747/12500000 : ℚ) : ℝ) ≤ Real.log (2810 : ℕ)
      ∧ Real.log (2810 : ℕ) ≤ ((794093977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2811 :
    ((794129557/100000000 : ℚ) : ℝ) ≤ Real.log (2811 : ℕ)
      ∧ Real.log (2811 : ℕ) ≤ ((397064779/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2812 :
    ((6353321/800000 : ℚ) : ℝ) ≤ Real.log (2812 : ℕ)
      ∧ Real.log (2812 : ℕ) ≤ ((397082563/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2813 :
    ((19855017/2500000 : ℚ) : ℝ) ≤ Real.log (2813 : ℕ)
      ∧ Real.log (2813 : ℕ) ≤ ((794200681/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2814 :
    ((794236223/100000000 : ℚ) : ℝ) ≤ Real.log (2814 : ℕ)
      ∧ Real.log (2814 : ℕ) ≤ ((12409941/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2815 :
    ((397135877/50000000 : ℚ) : ℝ) ≤ Real.log (2815 : ℕ)
      ∧ Real.log (2815 : ℕ) ≤ ((158854351/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2816 :
    ((794307271/100000000 : ℚ) : ℝ) ≤ Real.log (2816 : ℕ)
      ∧ Real.log (2816 : ℕ) ≤ ((99288409/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2817 :
    ((99292847/12500000 : ℚ) : ℝ) ≤ Real.log (2817 : ℕ)
      ∧ Real.log (2817 : ℕ) ≤ ((794342777/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2818 :
    ((794378269/100000000 : ℚ) : ℝ) ≤ Real.log (2818 : ℕ)
      ∧ Real.log (2818 : ℕ) ≤ ((79437827/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2819 :
    ((794413749/100000000 : ℚ) : ℝ) ≤ Real.log (2819 : ℕ)
      ∧ Real.log (2819 : ℕ) ≤ ((635531/80000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2820 :
    ((12413269/1562500 : ℚ) : ℝ) ≤ Real.log (2820 : ℕ)
      ∧ Real.log (2820 : ℕ) ≤ ((794449217/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2821 :
    ((794484671/100000000 : ℚ) : ℝ) ≤ Real.log (2821 : ℕ)
      ∧ Real.log (2821 : ℕ) ≤ ((12413823/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2822 :
    ((794520113/100000000 : ℚ) : ℝ) ≤ Real.log (2822 : ℕ)
      ∧ Real.log (2822 : ℕ) ≤ ((397260057/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2823 :
    ((397277771/50000000 : ℚ) : ℝ) ≤ Real.log (2823 : ℕ)
      ∧ Real.log (2823 : ℕ) ≤ ((794555543/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2824 :
    ((794590959/100000000 : ℚ) : ℝ) ≤ Real.log (2824 : ℕ)
      ∧ Real.log (2824 : ℕ) ≤ ((9932387/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2825 :
    ((198656591/25000000 : ℚ) : ℝ) ≤ Real.log (2825 : ℕ)
      ∧ Real.log (2825 : ℕ) ≤ ((158925273/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2826 :
    ((198665439/25000000 : ℚ) : ℝ) ≤ Real.log (2826 : ℕ)
      ∧ Real.log (2826 : ℕ) ≤ ((794661757/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2827 :
    ((158939427/20000000 : ℚ) : ℝ) ≤ Real.log (2827 : ℕ)
      ∧ Real.log (2827 : ℕ) ≤ ((49668571/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2828 :
    ((397366251/50000000 : ℚ) : ℝ) ≤ Real.log (2828 : ℕ)
      ∧ Real.log (2828 : ℕ) ≤ ((794732503/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2829 :
    ((794767857/100000000 : ℚ) : ℝ) ≤ Real.log (2829 : ℕ)
      ∧ Real.log (2829 : ℕ) ≤ ((397383929/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2830 :
    ((794803199/100000000 : ℚ) : ℝ) ≤ Real.log (2830 : ℕ)
      ∧ Real.log (2830 : ℕ) ≤ ((124188/15625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2831 :
    ((3104838/390625 : ℚ) : ℝ) ≤ Real.log (2831 : ℕ)
      ∧ Real.log (2831 : ℕ) ≤ ((794838529/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2832 :
    ((158974769/20000000 : ℚ) : ℝ) ≤ Real.log (2832 : ℕ)
      ∧ Real.log (2832 : ℕ) ≤ ((397436923/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2833 :
    ((198727287/25000000 : ℚ) : ℝ) ≤ Real.log (2833 : ℕ)
      ∧ Real.log (2833 : ℕ) ≤ ((794909151/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2834 :
    ((794944441/100000000 : ℚ) : ℝ) ≤ Real.log (2834 : ℕ)
      ∧ Real.log (2834 : ℕ) ≤ ((198736111/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2835 :
    ((794979721/100000000 : ℚ) : ℝ) ≤ Real.log (2835 : ℕ)
      ∧ Real.log (2835 : ℕ) ≤ ((397489861/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2836 :
    ((198753747/25000000 : ℚ) : ℝ) ≤ Real.log (2836 : ℕ)
      ∧ Real.log (2836 : ℕ) ≤ ((795014989/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2837 :
    ((795050243/100000000 : ℚ) : ℝ) ≤ Real.log (2837 : ℕ)
      ∧ Real.log (2837 : ℕ) ≤ ((198762561/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2838 :
    ((159017097/20000000 : ℚ) : ℝ) ≤ Real.log (2838 : ℕ)
      ∧ Real.log (2838 : ℕ) ≤ ((397542743/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2839 :
    ((159024143/20000000 : ℚ) : ℝ) ≤ Real.log (2839 : ℕ)
      ∧ Real.log (2839 : ℕ) ≤ ((198780179/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2840 :
    ((795155933/100000000 : ℚ) : ℝ) ≤ Real.log (2840 : ℕ)
      ∧ Real.log (2840 : ℕ) ≤ ((397577967/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2841 :
    ((397595569/50000000 : ℚ) : ℝ) ≤ Real.log (2841 : ℕ)
      ∧ Real.log (2841 : ℕ) ≤ ((795191139/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2842 :
    ((79522633/10000000 : ℚ) : ℝ) ≤ Real.log (2842 : ℕ)
      ∧ Real.log (2842 : ℕ) ≤ ((795226331/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2843 :
    ((795261511/100000000 : ℚ) : ℝ) ≤ Real.log (2843 : ℕ)
      ∧ Real.log (2843 : ℕ) ≤ ((99407689/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2844 :
    ((795296679/100000000 : ℚ) : ℝ) ≤ Real.log (2844 : ℕ)
      ∧ Real.log (2844 : ℕ) ≤ ((19882417/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2845 :
    ((397665917/50000000 : ℚ) : ℝ) ≤ Real.log (2845 : ℕ)
      ∧ Real.log (2845 : ℕ) ≤ ((159066367/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2846 :
    ((795366977/100000000 : ℚ) : ℝ) ≤ Real.log (2846 : ℕ)
      ∧ Real.log (2846 : ℕ) ≤ ((397683489/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2847 :
    ((198850527/25000000 : ℚ) : ℝ) ≤ Real.log (2847 : ℕ)
      ∧ Real.log (2847 : ℕ) ≤ ((795402109/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2848 :
    ((795437227/100000000 : ℚ) : ℝ) ≤ Real.log (2848 : ℕ)
      ∧ Real.log (2848 : ℕ) ≤ ((198859307/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2849 :
    ((795472333/100000000 : ℚ) : ℝ) ≤ Real.log (2849 : ℕ)
      ∧ Real.log (2849 : ℕ) ≤ ((397736167/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2850 :
    ((795507427/100000000 : ℚ) : ℝ) ≤ Real.log (2850 : ℕ)
      ∧ Real.log (2850 : ℕ) ≤ ((198876857/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2851 :
    ((198885627/25000000 : ℚ) : ℝ) ≤ Real.log (2851 : ℕ)
      ∧ Real.log (2851 : ℕ) ≤ ((795542509/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2852 :
    ((397788789/50000000 : ℚ) : ℝ) ≤ Real.log (2852 : ℕ)
      ∧ Real.log (2852 : ℕ) ≤ ((795577579/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2853 :
    ((159122527/20000000 : ℚ) : ℝ) ≤ Real.log (2853 : ℕ)
      ∧ Real.log (2853 : ℕ) ≤ ((198903159/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2854 :
    ((795647679/100000000 : ℚ) : ℝ) ≤ Real.log (2854 : ℕ)
      ∧ Real.log (2854 : ℕ) ≤ ((2486399/312500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2855 :
    ((99460339/12500000 : ℚ) : ℝ) ≤ Real.log (2855 : ℕ)
      ∧ Real.log (2855 : ℕ) ≤ ((795682713/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2856 :
    ((198929433/25000000 : ℚ) : ℝ) ≤ Real.log (2856 : ℕ)
      ∧ Real.log (2856 : ℕ) ≤ ((795717733/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2857 :
    ((39787637/5000000 : ℚ) : ℝ) ≤ Real.log (2857 : ℕ)
      ∧ Real.log (2857 : ℕ) ≤ ((795752741/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2858 :
    ((159157547/20000000 : ℚ) : ℝ) ≤ Real.log (2858 : ℕ)
      ∧ Real.log (2858 : ℕ) ≤ ((99473467/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2859 :
    ((795822719/100000000 : ℚ) : ℝ) ≤ Real.log (2859 : ℕ)
      ∧ Real.log (2859 : ℕ) ≤ ((1243473/156250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2860 :
    ((79585769/10000000 : ℚ) : ℝ) ≤ Real.log (2860 : ℕ)
      ∧ Real.log (2860 : ℕ) ≤ ((795857691/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2861 :
    ((795892649/100000000 : ℚ) : ℝ) ≤ Real.log (2861 : ℕ)
      ∧ Real.log (2861 : ℕ) ≤ ((15917853/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2862 :
    ((159185519/20000000 : ℚ) : ℝ) ≤ Real.log (2862 : ℕ)
      ∧ Real.log (2862 : ℕ) ≤ ((397963799/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2863 :
    ((79596253/10000000 : ℚ) : ℝ) ≤ Real.log (2863 : ℕ)
      ∧ Real.log (2863 : ℕ) ≤ ((795962531/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2864 :
    ((198999363/25000000 : ℚ) : ℝ) ≤ Real.log (2864 : ℕ)
      ∧ Real.log (2864 : ℕ) ≤ ((795997453/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2865 :
    ((398016181/50000000 : ℚ) : ℝ) ≤ Real.log (2865 : ℕ)
      ∧ Real.log (2865 : ℕ) ≤ ((796032363/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2866 :
    ((39803363/5000000 : ℚ) : ℝ) ≤ Real.log (2866 : ℕ)
      ∧ Real.log (2866 : ℕ) ≤ ((796067261/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2867 :
    ((398051073/50000000 : ℚ) : ℝ) ≤ Real.log (2867 : ℕ)
      ∧ Real.log (2867 : ℕ) ≤ ((796102147/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2868 :
    ((39806851/5000000 : ℚ) : ℝ) ≤ Real.log (2868 : ℕ)
      ∧ Real.log (2868 : ℕ) ≤ ((796137021/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2869 :
    ((796171881/100000000 : ℚ) : ℝ) ≤ Real.log (2869 : ℕ)
      ∧ Real.log (2869 : ℕ) ≤ ((398085941/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2870 :
    ((79620673/10000000 : ℚ) : ℝ) ≤ Real.log (2870 : ℕ)
      ∧ Real.log (2870 : ℕ) ≤ ((796206731/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2871 :
    ((796241567/100000000 : ℚ) : ℝ) ≤ Real.log (2871 : ℕ)
      ∧ Real.log (2871 : ℕ) ≤ ((79624157/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2872 :
    ((99534549/12500000 : ℚ) : ℝ) ≤ Real.log (2872 : ℕ)
      ∧ Real.log (2872 : ℕ) ≤ ((159255279/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2873 :
    ((159262241/20000000 : ℚ) : ℝ) ≤ Real.log (2873 : ℕ)
      ∧ Real.log (2873 : ℕ) ≤ ((398155603/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2874 :
    ((398173003/50000000 : ℚ) : ℝ) ≤ Real.log (2874 : ℕ)
      ∧ Real.log (2874 : ℕ) ≤ ((796346007/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2875 :
    ((159276159/20000000 : ℚ) : ℝ) ≤ Real.log (2875 : ℕ)
      ∧ Real.log (2875 : ℕ) ≤ ((199095199/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2876 :
    ((796415571/100000000 : ℚ) : ℝ) ≤ Real.log (2876 : ℕ)
      ∧ Real.log (2876 : ℕ) ≤ ((199103893/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2877 :
    ((24889073/3125000 : ℚ) : ℝ) ≤ Real.log (2877 : ℕ)
      ∧ Real.log (2877 : ℕ) ≤ ((796450337/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2878 :
    ((24890159/3125000 : ℚ) : ℝ) ≤ Real.log (2878 : ℕ)
      ∧ Real.log (2878 : ℕ) ≤ ((796485089/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2879 :
    ((796519829/100000000 : ℚ) : ℝ) ≤ Real.log (2879 : ℕ)
      ∧ Real.log (2879 : ℕ) ≤ ((79651983/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2880 :
    ((796554557/100000000 : ℚ) : ℝ) ≤ Real.log (2880 : ℕ)
      ∧ Real.log (2880 : ℕ) ≤ ((398277279/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2881 :
    ((796589273/100000000 : ℚ) : ℝ) ≤ Real.log (2881 : ℕ)
      ∧ Real.log (2881 : ℕ) ≤ ((398294637/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2882 :
    ((796623977/100000000 : ℚ) : ℝ) ≤ Real.log (2882 : ℕ)
      ∧ Real.log (2882 : ℕ) ≤ ((398311989/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2883 :
    ((796658669/100000000 : ℚ) : ℝ) ≤ Real.log (2883 : ℕ)
      ∧ Real.log (2883 : ℕ) ≤ ((79665867/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2884 :
    ((796693349/100000000 : ℚ) : ℝ) ≤ Real.log (2884 : ℕ)
      ∧ Real.log (2884 : ℕ) ≤ ((15933867/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2885 :
    ((796728017/100000000 : ℚ) : ℝ) ≤ Real.log (2885 : ℕ)
      ∧ Real.log (2885 : ℕ) ≤ ((398364009/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2886 :
    ((796762673/100000000 : ℚ) : ℝ) ≤ Real.log (2886 : ℕ)
      ∧ Real.log (2886 : ℕ) ≤ ((398381337/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2887 :
    ((199199329/25000000 : ℚ) : ℝ) ≤ Real.log (2887 : ℕ)
      ∧ Real.log (2887 : ℕ) ≤ ((796797319/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2888 :
    ((796831949/100000000 : ℚ) : ℝ) ≤ Real.log (2888 : ℕ)
      ∧ Real.log (2888 : ℕ) ≤ ((49801997/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2889 :
    ((79686657/10000000 : ℚ) : ℝ) ≤ Real.log (2889 : ℕ)
      ∧ Real.log (2889 : ℕ) ≤ ((796866571/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2890 :
    ((398450589/50000000 : ℚ) : ℝ) ≤ Real.log (2890 : ℕ)
      ∧ Real.log (2890 : ℕ) ≤ ((796901179/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2891 :
    ((398467887/50000000 : ℚ) : ℝ) ≤ Real.log (2891 : ℕ)
      ∧ Real.log (2891 : ℕ) ≤ ((31877431/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2892 :
    ((398485179/50000000 : ℚ) : ℝ) ≤ Real.log (2892 : ℕ)
      ∧ Real.log (2892 : ℕ) ≤ ((796970359/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2893 :
    ((79700493/10000000 : ℚ) : ℝ) ≤ Real.log (2893 : ℕ)
      ∧ Real.log (2893 : ℕ) ≤ ((797004931/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2894 :
    ((79703949/10000000 : ℚ) : ℝ) ≤ Real.log (2894 : ℕ)
      ∧ Real.log (2894 : ℕ) ≤ ((797039491/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2895 :
    ((398537019/50000000 : ℚ) : ℝ) ≤ Real.log (2895 : ℕ)
      ∧ Real.log (2895 : ℕ) ≤ ((797074041/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2896 :
    ((31884343/4000000 : ℚ) : ℝ) ≤ Real.log (2896 : ℕ)
      ∧ Real.log (2896 : ℕ) ≤ ((24909643/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2897 :
    ((797143099/100000000 : ℚ) : ℝ) ≤ Real.log (2897 : ℕ)
      ∧ Real.log (2897 : ℕ) ≤ ((7971431/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2898 :
    ((199294403/25000000 : ℚ) : ℝ) ≤ Real.log (2898 : ℕ)
      ∧ Real.log (2898 : ℕ) ≤ ((797177613/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2899 :
    ((49825757/6250000 : ℚ) : ℝ) ≤ Real.log (2899 : ℕ)
      ∧ Real.log (2899 : ℕ) ≤ ((797212113/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2900 :
    ((797246601/100000000 : ℚ) : ℝ) ≤ Real.log (2900 : ℕ)
      ∧ Real.log (2900 : ℕ) ≤ ((398623301/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2901 :
    ((398640539/50000000 : ℚ) : ℝ) ≤ Real.log (2901 : ℕ)
      ∧ Real.log (2901 : ℕ) ≤ ((797281079/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2902 :
    ((797315543/100000000 : ℚ) : ℝ) ≤ Real.log (2902 : ℕ)
      ∧ Real.log (2902 : ℕ) ≤ ((99664443/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2903 :
    ((199337499/25000000 : ℚ) : ℝ) ≤ Real.log (2903 : ℕ)
      ∧ Real.log (2903 : ℕ) ≤ ((797349997/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2904 :
    ((797384437/100000000 : ℚ) : ℝ) ≤ Real.log (2904 : ℕ)
      ∧ Real.log (2904 : ℕ) ≤ ((398692219/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2905 :
    ((398709433/50000000 : ℚ) : ℝ) ≤ Real.log (2905 : ℕ)
      ∧ Real.log (2905 : ℕ) ≤ ((797418867/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2906 :
    ((199363321/25000000 : ℚ) : ℝ) ≤ Real.log (2906 : ℕ)
      ∧ Real.log (2906 : ℕ) ≤ ((159490657/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2907 :
    ((79748769/10000000 : ℚ) : ℝ) ≤ Real.log (2907 : ℕ)
      ∧ Real.log (2907 : ℕ) ≤ ((797487691/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2908 :
    ((797522083/100000000 : ℚ) : ℝ) ≤ Real.log (2908 : ℕ)
      ∧ Real.log (2908 : ℕ) ≤ ((199380521/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2909 :
    ((159511293/20000000 : ℚ) : ℝ) ≤ Real.log (2909 : ℕ)
      ∧ Real.log (2909 : ℕ) ≤ ((398778233/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2910 :
    ((159518167/20000000 : ℚ) : ℝ) ≤ Real.log (2910 : ℕ)
      ∧ Real.log (2910 : ℕ) ≤ ((398795419/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2911 :
    ((398812597/50000000 : ℚ) : ℝ) ≤ Real.log (2911 : ℕ)
      ∧ Real.log (2911 : ℕ) ≤ ((159525039/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2912 :
    ((39882977/5000000 : ℚ) : ℝ) ≤ Real.log (2912 : ℕ)
      ∧ Real.log (2912 : ℕ) ≤ ((797659541/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2913 :
    ((6381551/800000 : ℚ) : ℝ) ≤ Real.log (2913 : ℕ)
      ∧ Real.log (2913 : ℕ) ≤ ((199423469/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2914 :
    ((398864099/50000000 : ℚ) : ℝ) ≤ Real.log (2914 : ℕ)
      ∧ Real.log (2914 : ℕ) ≤ ((797728199/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2915 :
    ((797762509/100000000 : ℚ) : ℝ) ≤ Real.log (2915 : ℕ)
      ∧ Real.log (2915 : ℕ) ≤ ((79776251/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2916 :
    ((797796809/100000000 : ℚ) : ℝ) ≤ Real.log (2916 : ℕ)
      ∧ Real.log (2916 : ℕ) ≤ ((79779681/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2917 :
    ((159566219/20000000 : ℚ) : ℝ) ≤ Real.log (2917 : ℕ)
      ∧ Real.log (2917 : ℕ) ≤ ((398915549/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2918 :
    ((199466343/25000000 : ℚ) : ℝ) ≤ Real.log (2918 : ℕ)
      ∧ Real.log (2918 : ℕ) ≤ ((797865373/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2919 :
    ((797899637/100000000 : ℚ) : ℝ) ≤ Real.log (2919 : ℕ)
      ∧ Real.log (2919 : ℕ) ≤ ((398949819/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2920 :
    ((797933889/100000000 : ℚ) : ℝ) ≤ Real.log (2920 : ℕ)
      ∧ Real.log (2920 : ℕ) ≤ ((79793389/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2921 :
    ((79796813/10000000 : ℚ) : ℝ) ≤ Real.log (2921 : ℕ)
      ∧ Real.log (2921 : ℕ) ≤ ((797968131/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2922 :
    ((798002359/100000000 : ℚ) : ℝ) ≤ Real.log (2922 : ℕ)
      ∧ Real.log (2922 : ℕ) ≤ ((19950059/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2923 :
    ((24938643/3125000 : ℚ) : ℝ) ≤ Real.log (2923 : ℕ)
      ∧ Real.log (2923 : ℕ) ≤ ((798036577/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2924 :
    ((399035391/50000000 : ℚ) : ℝ) ≤ Real.log (2924 : ℕ)
      ∧ Real.log (2924 : ℕ) ≤ ((798070783/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2925 :
    ((399052487/50000000 : ℚ) : ℝ) ≤ Real.log (2925 : ℕ)
      ∧ Real.log (2925 : ℕ) ≤ ((798104977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2926 :
    ((399069579/50000000 : ℚ) : ℝ) ≤ Real.log (2926 : ℕ)
      ∧ Real.log (2926 : ℕ) ≤ ((798139159/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2927 :
    ((49885833/6250000 : ℚ) : ℝ) ≤ Real.log (2927 : ℕ)
      ∧ Real.log (2927 : ℕ) ≤ ((798173329/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2928 :
    ((798207487/100000000 : ℚ) : ℝ) ≤ Real.log (2928 : ℕ)
      ∧ Real.log (2928 : ℕ) ≤ ((3117998/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2929 :
    ((399120817/50000000 : ℚ) : ℝ) ≤ Real.log (2929 : ℕ)
      ∧ Real.log (2929 : ℕ) ≤ ((159648327/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2930 :
    ((79827577/10000000 : ℚ) : ℝ) ≤ Real.log (2930 : ℕ)
      ∧ Real.log (2930 : ℕ) ≤ ((798275771/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2931 :
    ((399154947/50000000 : ℚ) : ℝ) ≤ Real.log (2931 : ℕ)
      ∧ Real.log (2931 : ℕ) ≤ ((159661979/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2932 :
    ((399172003/50000000 : ℚ) : ℝ) ≤ Real.log (2932 : ℕ)
      ∧ Real.log (2932 : ℕ) ≤ ((798344007/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2933 :
    ((399189053/50000000 : ℚ) : ℝ) ≤ Real.log (2933 : ℕ)
      ∧ Real.log (2933 : ℕ) ≤ ((798378107/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2934 :
    ((159682439/20000000 : ℚ) : ℝ) ≤ Real.log (2934 : ℕ)
      ∧ Real.log (2934 : ℕ) ≤ ((199603049/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2935 :
    ((798446273/100000000 : ℚ) : ℝ) ≤ Real.log (2935 : ℕ)
      ∧ Real.log (2935 : ℕ) ≤ ((399223137/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2936 :
    ((798480337/100000000 : ℚ) : ℝ) ≤ Real.log (2936 : ℕ)
      ∧ Real.log (2936 : ℕ) ≤ ((39924017/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2937 :
    ((798514393/100000000 : ℚ) : ℝ) ≤ Real.log (2937 : ℕ)
      ∧ Real.log (2937 : ℕ) ≤ ((399257197/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2938 :
    ((159709687/20000000 : ℚ) : ℝ) ≤ Real.log (2938 : ℕ)
      ∧ Real.log (2938 : ℕ) ≤ ((199637109/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2939 :
    ((399291233/50000000 : ℚ) : ℝ) ≤ Real.log (2939 : ℕ)
      ∧ Real.log (2939 : ℕ) ≤ ((798582467/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2940 :
    ((159723297/20000000 : ℚ) : ℝ) ≤ Real.log (2940 : ℕ)
      ∧ Real.log (2940 : ℕ) ≤ ((99827061/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2941 :
    ((798650493/100000000 : ℚ) : ℝ) ≤ Real.log (2941 : ℕ)
      ∧ Real.log (2941 : ℕ) ≤ ((399325247/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2942 :
    ((79868449/10000000 : ℚ) : ℝ) ≤ Real.log (2942 : ℕ)
      ∧ Real.log (2942 : ℕ) ≤ ((798684491/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2943 :
    ((399359237/50000000 : ℚ) : ℝ) ≤ Real.log (2943 : ℕ)
      ∧ Real.log (2943 : ℕ) ≤ ((31948739/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2944 :
    ((399376223/50000000 : ℚ) : ℝ) ≤ Real.log (2944 : ℕ)
      ∧ Real.log (2944 : ℕ) ≤ ((798752449/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2945 :
    ((798786409/100000000 : ℚ) : ℝ) ≤ Real.log (2945 : ℕ)
      ∧ Real.log (2945 : ℕ) ≤ ((79878641/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2946 :
    ((798820359/100000000 : ℚ) : ℝ) ≤ Real.log (2946 : ℕ)
      ∧ Real.log (2946 : ℕ) ≤ ((19970509/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2947 :
    ((399427149/50000000 : ℚ) : ℝ) ≤ Real.log (2947 : ℕ)
      ∧ Real.log (2947 : ℕ) ≤ ((798854299/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2948 :
    ((31955529/4000000 : ℚ) : ℝ) ≤ Real.log (2948 : ℕ)
      ∧ Real.log (2948 : ℕ) ≤ ((399444113/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2949 :
    ((39946107/5000000 : ℚ) : ℝ) ≤ Real.log (2949 : ℕ)
      ∧ Real.log (2949 : ℕ) ≤ ((798922141/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2950 :
    ((199739011/25000000 : ℚ) : ℝ) ≤ Real.log (2950 : ℕ)
      ∧ Real.log (2950 : ℕ) ≤ ((159791209/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2951 :
    ((798989937/100000000 : ℚ) : ℝ) ≤ Real.log (2951 : ℕ)
      ∧ Real.log (2951 : ℕ) ≤ ((399494969/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2952 :
    ((399511909/50000000 : ℚ) : ℝ) ≤ Real.log (2952 : ℕ)
      ∧ Real.log (2952 : ℕ) ≤ ((799023819/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2953 :
    ((99882211/12500000 : ℚ) : ℝ) ≤ Real.log (2953 : ℕ)
      ∧ Real.log (2953 : ℕ) ≤ ((799057689/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2954 :
    ((399545773/50000000 : ℚ) : ℝ) ≤ Real.log (2954 : ℕ)
      ∧ Real.log (2954 : ℕ) ≤ ((799091547/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2955 :
    ((799125391/100000000 : ℚ) : ℝ) ≤ Real.log (2955 : ℕ)
      ∧ Real.log (2955 : ℕ) ≤ ((399562697/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2956 :
    ((199789807/25000000 : ℚ) : ℝ) ≤ Real.log (2956 : ℕ)
      ∧ Real.log (2956 : ℕ) ≤ ((799159229/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2957 :
    ((15983861/2000000 : ℚ) : ℝ) ≤ Real.log (2957 : ℕ)
      ∧ Real.log (2957 : ℕ) ≤ ((799193053/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2958 :
    ((49951679/6250000 : ℚ) : ℝ) ≤ Real.log (2958 : ℕ)
      ∧ Real.log (2958 : ℕ) ≤ ((159845373/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2959 :
    ((159852133/20000000 : ℚ) : ℝ) ≤ Real.log (2959 : ℕ)
      ∧ Real.log (2959 : ℕ) ≤ ((399630333/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2960 :
    ((399647227/50000000 : ℚ) : ℝ) ≤ Real.log (2960 : ℕ)
      ∧ Real.log (2960 : ℕ) ≤ ((159858891/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2961 :
    ((99916029/12500000 : ℚ) : ℝ) ≤ Real.log (2961 : ℕ)
      ∧ Real.log (2961 : ℕ) ≤ ((799328233/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2962 :
    ((799361999/100000000 : ℚ) : ℝ) ≤ Real.log (2962 : ℕ)
      ∧ Real.log (2962 : ℕ) ≤ ((399681/50000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2963 :
    ((399697877/50000000 : ℚ) : ℝ) ≤ Real.log (2963 : ℕ)
      ∧ Real.log (2963 : ℕ) ≤ ((159879151/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2964 :
    ((399714749/50000000 : ℚ) : ℝ) ≤ Real.log (2964 : ℕ)
      ∧ Real.log (2964 : ℕ) ≤ ((799429499/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2965 :
    ((799463231/100000000 : ℚ) : ℝ) ≤ Real.log (2965 : ℕ)
      ∧ Real.log (2965 : ℕ) ≤ ((12491613/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2966 :
    ((99937119/12500000 : ℚ) : ℝ) ≤ Real.log (2966 : ℕ)
      ∧ Real.log (2966 : ℕ) ≤ ((799496953/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2967 :
    ((799530661/100000000 : ℚ) : ℝ) ≤ Real.log (2967 : ℕ)
      ∧ Real.log (2967 : ℕ) ≤ ((99941333/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2968 :
    ((19989109/2500000 : ℚ) : ℝ) ≤ Real.log (2968 : ℕ)
      ∧ Real.log (2968 : ℕ) ≤ ((799564361/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2969 :
    ((799598047/100000000 : ℚ) : ℝ) ≤ Real.log (2969 : ℕ)
      ∧ Real.log (2969 : ℕ) ≤ ((24987439/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2970 :
    ((799631723/100000000 : ℚ) : ℝ) ≤ Real.log (2970 : ℕ)
      ∧ Real.log (2970 : ℕ) ≤ ((199907931/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2971 :
    ((799665387/100000000 : ℚ) : ℝ) ≤ Real.log (2971 : ℕ)
      ∧ Real.log (2971 : ℕ) ≤ ((199916347/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2972 :
    ((4998119/625000 : ℚ) : ℝ) ≤ Real.log (2972 : ℕ)
      ∧ Real.log (2972 : ℕ) ≤ ((799699041/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2973 :
    ((399866341/50000000 : ℚ) : ℝ) ≤ Real.log (2973 : ℕ)
      ∧ Real.log (2973 : ℕ) ≤ ((799732683/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2974 :
    ((99970789/12500000 : ℚ) : ℝ) ≤ Real.log (2974 : ℕ)
      ∧ Real.log (2974 : ℕ) ≤ ((799766313/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2975 :
    ((799799931/100000000 : ℚ) : ℝ) ≤ Real.log (2975 : ℕ)
      ∧ Real.log (2975 : ℕ) ≤ ((199949983/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2976 :
    ((799833539/100000000 : ℚ) : ℝ) ≤ Real.log (2976 : ℕ)
      ∧ Real.log (2976 : ℕ) ≤ ((39991677/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2977 :
    ((3124481/390625 : ℚ) : ℝ) ≤ Real.log (2977 : ℕ)
      ∧ Real.log (2977 : ℕ) ≤ ((799867137/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2978 :
    ((799900721/100000000 : ℚ) : ℝ) ≤ Real.log (2978 : ℕ)
      ∧ Real.log (2978 : ℕ) ≤ ((399950361/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2979 :
    ((159986859/20000000 : ℚ) : ℝ) ≤ Real.log (2979 : ℕ)
      ∧ Real.log (2979 : ℕ) ≤ ((99991787/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2980 :
    ((799967857/100000000 : ℚ) : ℝ) ≤ Real.log (2980 : ℕ)
      ∧ Real.log (2980 : ℕ) ≤ ((399983929/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2981 :
    ((800001409/100000000 : ℚ) : ℝ) ≤ Real.log (2981 : ℕ)
      ∧ Real.log (2981 : ℕ) ≤ ((80000141/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2982 :
    ((800034949/100000000 : ℚ) : ℝ) ≤ Real.log (2982 : ℕ)
      ∧ Real.log (2982 : ℕ) ≤ ((16000699/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2983 :
    ((400034239/50000000 : ℚ) : ℝ) ≤ Real.log (2983 : ℕ)
      ∧ Real.log (2983 : ℕ) ≤ ((800068479/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2984 :
    ((200025499/25000000 : ℚ) : ℝ) ≤ Real.log (2984 : ℕ)
      ∧ Real.log (2984 : ℕ) ≤ ((800101997/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2985 :
    ((400067751/50000000 : ℚ) : ℝ) ≤ Real.log (2985 : ℕ)
      ∧ Real.log (2985 : ℕ) ≤ ((800135503/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2986 :
    ((800168997/100000000 : ℚ) : ℝ) ≤ Real.log (2986 : ℕ)
      ∧ Real.log (2986 : ℕ) ≤ ((400084499/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2987 :
    ((800202481/100000000 : ℚ) : ℝ) ≤ Real.log (2987 : ℕ)
      ∧ Real.log (2987 : ℕ) ≤ ((400101241/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2988 :
    ((400117977/50000000 : ℚ) : ℝ) ≤ Real.log (2988 : ℕ)
      ∧ Real.log (2988 : ℕ) ≤ ((160047191/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2989 :
    ((100033677/12500000 : ℚ) : ℝ) ≤ Real.log (2989 : ℕ)
      ∧ Real.log (2989 : ℕ) ≤ ((800269417/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2990 :
    ((400151433/50000000 : ℚ) : ℝ) ≤ Real.log (2990 : ℕ)
      ∧ Real.log (2990 : ℕ) ≤ ((800302867/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2991 :
    ((160067261/20000000 : ℚ) : ℝ) ≤ Real.log (2991 : ℕ)
      ∧ Real.log (2991 : ℕ) ≤ ((400168153/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2992 :
    ((800369733/100000000 : ℚ) : ℝ) ≤ Real.log (2992 : ℕ)
      ∧ Real.log (2992 : ℕ) ≤ ((400184867/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2993 :
    ((16008063/2000000 : ℚ) : ℝ) ≤ Real.log (2993 : ℕ)
      ∧ Real.log (2993 : ℕ) ≤ ((800403151/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2994 :
    ((200109139/25000000 : ℚ) : ℝ) ≤ Real.log (2994 : ℕ)
      ∧ Real.log (2994 : ℕ) ≤ ((800436557/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2995 :
    ((800469951/100000000 : ℚ) : ℝ) ≤ Real.log (2995 : ℕ)
      ∧ Real.log (2995 : ℕ) ≤ ((12507343/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2996 :
    ((400251667/50000000 : ℚ) : ℝ) ≤ Real.log (2996 : ℕ)
      ∧ Real.log (2996 : ℕ) ≤ ((160100667/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2997 :
    ((400268353/50000000 : ℚ) : ℝ) ≤ Real.log (2997 : ℕ)
      ∧ Real.log (2997 : ℕ) ≤ ((800536707/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2998 :
    ((800570067/100000000 : ℚ) : ℝ) ≤ Real.log (2998 : ℕ)
      ∧ Real.log (2998 : ℕ) ≤ ((200142517/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_2999 :
    ((800603417/100000000 : ℚ) : ℝ) ≤ Real.log (2999 : ℕ)
      ∧ Real.log (2999 : ℕ) ≤ ((400301709/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3000 :
    ((200159189/25000000 : ℚ) : ℝ) ≤ Real.log (3000 : ℕ)
      ∧ Real.log (3000 : ℕ) ≤ ((800636757/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3001 :
    ((200167521/25000000 : ℚ) : ℝ) ≤ Real.log (3001 : ℕ)
      ∧ Real.log (3001 : ℕ) ≤ ((160134017/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3002 :
    ((800703401/100000000 : ℚ) : ℝ) ≤ Real.log (3002 : ℕ)
      ∧ Real.log (3002 : ℕ) ≤ ((400351701/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3003 :
    ((400368353/50000000 : ℚ) : ℝ) ≤ Real.log (3003 : ℕ)
      ∧ Real.log (3003 : ℕ) ≤ ((800736707/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3004 :
    ((800770001/100000000 : ℚ) : ℝ) ≤ Real.log (3004 : ℕ)
      ∧ Real.log (3004 : ℕ) ≤ ((400385001/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3005 :
    ((200200821/25000000 : ℚ) : ℝ) ≤ Real.log (3005 : ℕ)
      ∧ Real.log (3005 : ℕ) ≤ ((160160657/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3006 :
    ((200209139/25000000 : ℚ) : ℝ) ≤ Real.log (3006 : ℕ)
      ∧ Real.log (3006 : ℕ) ≤ ((800836559/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3007 :
    ((400434909/50000000 : ℚ) : ℝ) ≤ Real.log (3007 : ℕ)
      ∧ Real.log (3007 : ℕ) ≤ ((800869819/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3008 :
    ((200225767/25000000 : ℚ) : ℝ) ≤ Real.log (3008 : ℕ)
      ∧ Real.log (3008 : ℕ) ≤ ((800903069/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3009 :
    ((800936307/100000000 : ℚ) : ℝ) ≤ Real.log (3009 : ℕ)
      ∧ Real.log (3009 : ℕ) ≤ ((200234077/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3010 :
    ((160193907/20000000 : ℚ) : ℝ) ≤ Real.log (3010 : ℕ)
      ∧ Real.log (3010 : ℕ) ≤ ((12515149/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3011 :
    ((3128917/390625 : ℚ) : ℝ) ≤ Real.log (3011 : ℕ)
      ∧ Real.log (3011 : ℕ) ≤ ((801002753/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3012 :
    ((400517979/50000000 : ℚ) : ℝ) ≤ Real.log (3012 : ℕ)
      ∧ Real.log (3012 : ℕ) ≤ ((801035959/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3013 :
    ((801069153/100000000 : ℚ) : ℝ) ≤ Real.log (3013 : ℕ)
      ∧ Real.log (3013 : ℕ) ≤ ((400534577/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3014 :
    ((801102337/100000000 : ℚ) : ℝ) ≤ Real.log (3014 : ℕ)
      ∧ Real.log (3014 : ℕ) ≤ ((400551169/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3015 :
    ((80113551/10000000 : ℚ) : ℝ) ≤ Real.log (3015 : ℕ)
      ∧ Real.log (3015 : ℕ) ≤ ((801135511/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3016 :
    ((25036521/3125000 : ℚ) : ℝ) ≤ Real.log (3016 : ℕ)
      ∧ Real.log (3016 : ℕ) ≤ ((801168673/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3017 :
    ((801201823/100000000 : ℚ) : ℝ) ≤ Real.log (3017 : ℕ)
      ∧ Real.log (3017 : ℕ) ≤ ((25037557/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3018 :
    ((801234963/100000000 : ℚ) : ℝ) ≤ Real.log (3018 : ℕ)
      ∧ Real.log (3018 : ℕ) ≤ ((200308741/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3019 :
    ((801268091/100000000 : ℚ) : ℝ) ≤ Real.log (3019 : ℕ)
      ∧ Real.log (3019 : ℕ) ≤ ((400634047/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3020 :
    ((80130121/10000000 : ℚ) : ℝ) ≤ Real.log (3020 : ℕ)
      ∧ Real.log (3020 : ℕ) ≤ ((801301213/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3021 :
    ((400667159/50000000 : ℚ) : ℝ) ≤ Real.log (3021 : ℕ)
      ∧ Real.log (3021 : ℕ) ≤ ((801334319/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3022 :
    ((400683707/50000000 : ℚ) : ℝ) ≤ Real.log (3022 : ℕ)
      ∧ Real.log (3022 : ℕ) ≤ ((160273483/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3023 :
    ((801400499/100000000 : ℚ) : ℝ) ≤ Real.log (3023 : ℕ)
      ∧ Real.log (3023 : ℕ) ≤ ((1602801/200000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3024 :
    ((801433573/100000000 : ℚ) : ℝ) ≤ Real.log (3024 : ℕ)
      ∧ Real.log (3024 : ℕ) ≤ ((400716787/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3025 :
    ((801466637/100000000 : ℚ) : ℝ) ≤ Real.log (3025 : ℕ)
      ∧ Real.log (3025 : ℕ) ≤ ((400733319/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3026 :
    ((801499689/100000000 : ℚ) : ℝ) ≤ Real.log (3026 : ℕ)
      ∧ Real.log (3026 : ℕ) ≤ ((80149969/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3027 :
    ((80153273/10000000 : ℚ) : ℝ) ≤ Real.log (3027 : ℕ)
      ∧ Real.log (3027 : ℕ) ≤ ((801532731/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3028 :
    ((801565761/100000000 : ℚ) : ℝ) ≤ Real.log (3028 : ℕ)
      ∧ Real.log (3028 : ℕ) ≤ ((400782881/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3029 :
    ((801598781/100000000 : ℚ) : ℝ) ≤ Real.log (3029 : ℕ)
      ∧ Real.log (3029 : ℕ) ≤ ((400799391/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3030 :
    ((801631789/100000000 : ℚ) : ℝ) ≤ Real.log (3030 : ℕ)
      ∧ Real.log (3030 : ℕ) ≤ ((80163179/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3031 :
    ((801664787/100000000 : ℚ) : ℝ) ≤ Real.log (3031 : ℕ)
      ∧ Real.log (3031 : ℕ) ≤ ((200416197/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3032 :
    ((400848887/50000000 : ℚ) : ℝ) ≤ Real.log (3032 : ℕ)
      ∧ Real.log (3032 : ℕ) ≤ ((32067911/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3033 :
    ((3206923/400000 : ℚ) : ℝ) ≤ Real.log (3033 : ℕ)
      ∧ Real.log (3033 : ℕ) ≤ ((801730751/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3034 :
    ((400881857/50000000 : ℚ) : ℝ) ≤ Real.log (3034 : ℕ)
      ∧ Real.log (3034 : ℕ) ≤ ((801763717/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3035 :
    ((80179667/10000000 : ℚ) : ℝ) ≤ Real.log (3035 : ℕ)
      ∧ Real.log (3035 : ℕ) ≤ ((801796671/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3036 :
    ((801829613/100000000 : ℚ) : ℝ) ≤ Real.log (3036 : ℕ)
      ∧ Real.log (3036 : ℕ) ≤ ((400914807/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3037 :
    ((400931273/50000000 : ℚ) : ℝ) ≤ Real.log (3037 : ℕ)
      ∧ Real.log (3037 : ℕ) ≤ ((801862547/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3038 :
    ((200473867/25000000 : ℚ) : ℝ) ≤ Real.log (3038 : ℕ)
      ∧ Real.log (3038 : ℕ) ≤ ((801895469/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3039 :
    ((801928379/100000000 : ℚ) : ℝ) ≤ Real.log (3039 : ℕ)
      ∧ Real.log (3039 : ℕ) ≤ ((40096419/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3040 :
    ((801961279/100000000 : ℚ) : ℝ) ≤ Real.log (3040 : ℕ)
      ∧ Real.log (3040 : ℕ) ≤ ((2506129/312500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3041 :
    ((100249271/12500000 : ℚ) : ℝ) ≤ Real.log (3041 : ℕ)
      ∧ Real.log (3041 : ℕ) ≤ ((801994169/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3042 :
    ((802027047/100000000 : ℚ) : ℝ) ≤ Real.log (3042 : ℕ)
      ∧ Real.log (3042 : ℕ) ≤ ((100253381/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3043 :
    ((802059913/100000000 : ℚ) : ℝ) ≤ Real.log (3043 : ℕ)
      ∧ Real.log (3043 : ℕ) ≤ ((200514979/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3044 :
    ((802092771/100000000 : ℚ) : ℝ) ≤ Real.log (3044 : ℕ)
      ∧ Real.log (3044 : ℕ) ≤ ((200523193/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3045 :
    ((802125617/100000000 : ℚ) : ℝ) ≤ Real.log (3045 : ℕ)
      ∧ Real.log (3045 : ℕ) ≤ ((40106281/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3046 :
    ((802158453/100000000 : ℚ) : ℝ) ≤ Real.log (3046 : ℕ)
      ∧ Real.log (3046 : ℕ) ≤ ((401079227/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3047 :
    ((802191277/100000000 : ℚ) : ℝ) ≤ Real.log (3047 : ℕ)
      ∧ Real.log (3047 : ℕ) ≤ ((401095639/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3048 :
    ((802224091/100000000 : ℚ) : ℝ) ≤ Real.log (3048 : ℕ)
      ∧ Real.log (3048 : ℕ) ≤ ((200556023/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3049 :
    ((401128447/50000000 : ℚ) : ℝ) ≤ Real.log (3049 : ℕ)
      ∧ Real.log (3049 : ℕ) ≤ ((160451379/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3050 :
    ((160457937/20000000 : ℚ) : ℝ) ≤ Real.log (3050 : ℕ)
      ∧ Real.log (3050 : ℕ) ≤ ((100286211/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3051 :
    ((200580617/25000000 : ℚ) : ℝ) ≤ Real.log (3051 : ℕ)
      ∧ Real.log (3051 : ℕ) ≤ ((802322469/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3052 :
    ((802355239/100000000 : ℚ) : ℝ) ≤ Real.log (3052 : ℕ)
      ∧ Real.log (3052 : ℕ) ≤ ((20058881/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3053 :
    ((802387999/100000000 : ℚ) : ℝ) ≤ Real.log (3053 : ℕ)
      ∧ Real.log (3053 : ℕ) ≤ ((200597/25000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3054 :
    ((200605187/25000000 : ℚ) : ℝ) ≤ Real.log (3054 : ℕ)
      ∧ Real.log (3054 : ℕ) ≤ ((802420749/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3055 :
    ((802453487/100000000 : ℚ) : ℝ) ≤ Real.log (3055 : ℕ)
      ∧ Real.log (3055 : ℕ) ≤ ((50153343/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3056 :
    ((401243107/50000000 : ℚ) : ℝ) ≤ Real.log (3056 : ℕ)
      ∧ Real.log (3056 : ℕ) ≤ ((802486217/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3057 :
    ((200629733/25000000 : ℚ) : ℝ) ≤ Real.log (3057 : ℕ)
      ∧ Real.log (3057 : ℕ) ≤ ((802518933/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3058 :
    ((401275819/50000000 : ℚ) : ℝ) ≤ Real.log (3058 : ℕ)
      ∧ Real.log (3058 : ℕ) ≤ ((802551639/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3059 :
    ((401292167/50000000 : ℚ) : ℝ) ≤ Real.log (3059 : ℕ)
      ∧ Real.log (3059 : ℕ) ≤ ((160516867/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3060 :
    ((802617019/100000000 : ℚ) : ℝ) ≤ Real.log (3060 : ℕ)
      ∧ Real.log (3060 : ℕ) ≤ ((40130851/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3061 :
    ((802649693/100000000 : ℚ) : ℝ) ≤ Real.log (3061 : ℕ)
      ∧ Real.log (3061 : ℕ) ≤ ((401324847/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3062 :
    ((802682357/100000000 : ℚ) : ℝ) ≤ Real.log (3062 : ℕ)
      ∧ Real.log (3062 : ℕ) ≤ ((401341179/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3063 :
    ((80271501/10000000 : ℚ) : ℝ) ≤ Real.log (3063 : ℕ)
      ∧ Real.log (3063 : ℕ) ≤ ((802715011/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3064 :
    ((802747653/100000000 : ℚ) : ℝ) ≤ Real.log (3064 : ℕ)
      ∧ Real.log (3064 : ℕ) ≤ ((401373827/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3065 :
    ((200695071/25000000 : ℚ) : ℝ) ≤ Real.log (3065 : ℕ)
      ∧ Real.log (3065 : ℕ) ≤ ((160556057/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3066 :
    ((160562581/20000000 : ℚ) : ℝ) ≤ Real.log (3066 : ℕ)
      ∧ Real.log (3066 : ℕ) ≤ ((401406453/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3067 :
    ((200711379/25000000 : ℚ) : ℝ) ≤ Real.log (3067 : ℕ)
      ∧ Real.log (3067 : ℕ) ≤ ((802845517/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3068 :
    ((200719529/25000000 : ℚ) : ℝ) ≤ Real.log (3068 : ℕ)
      ∧ Real.log (3068 : ℕ) ≤ ((802878117/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3069 :
    ((160582141/20000000 : ℚ) : ℝ) ≤ Real.log (3069 : ℕ)
      ∧ Real.log (3069 : ℕ) ≤ ((401455353/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3070 :
    ((200735821/25000000 : ℚ) : ℝ) ≤ Real.log (3070 : ℕ)
      ∧ Real.log (3070 : ℕ) ≤ ((160588657/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3071 :
    ((200743963/25000000 : ℚ) : ℝ) ≤ Real.log (3071 : ℕ)
      ∧ Real.log (3071 : ℕ) ≤ ((802975853/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3072 :
    ((803008409/100000000 : ℚ) : ℝ) ≤ Real.log (3072 : ℕ)
      ∧ Real.log (3072 : ℕ) ≤ ((80300841/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3073 :
    ((200760239/25000000 : ℚ) : ℝ) ≤ Real.log (3073 : ℕ)
      ∧ Real.log (3073 : ℕ) ≤ ((803040957/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3074 :
    ((200768373/25000000 : ℚ) : ℝ) ≤ Real.log (3074 : ℕ)
      ∧ Real.log (3074 : ℕ) ≤ ((803073493/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3075 :
    ((803106017/100000000 : ℚ) : ℝ) ≤ Real.log (3075 : ℕ)
      ∧ Real.log (3075 : ℕ) ≤ ((40155301/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3076 :
    ((803138533/100000000 : ℚ) : ℝ) ≤ Real.log (3076 : ℕ)
      ∧ Real.log (3076 : ℕ) ≤ ((401569267/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3077 :
    ((803171037/100000000 : ℚ) : ℝ) ≤ Real.log (3077 : ℕ)
      ∧ Real.log (3077 : ℕ) ≤ ((401585519/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3078 :
    ((803203531/100000000 : ℚ) : ℝ) ≤ Real.log (3078 : ℕ)
      ∧ Real.log (3078 : ℕ) ≤ ((200800883/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3079 :
    ((401618007/50000000 : ℚ) : ℝ) ≤ Real.log (3079 : ℕ)
      ∧ Real.log (3079 : ℕ) ≤ ((160647203/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3080 :
    ((803268487/100000000 : ℚ) : ℝ) ≤ Real.log (3080 : ℕ)
      ∧ Real.log (3080 : ℕ) ≤ ((100408561/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3081 :
    ((803300949/100000000 : ℚ) : ℝ) ≤ Real.log (3081 : ℕ)
      ∧ Real.log (3081 : ℕ) ≤ ((16066019/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3082 :
    ((803333401/100000000 : ℚ) : ℝ) ≤ Real.log (3082 : ℕ)
      ∧ Real.log (3082 : ℕ) ≤ ((401666701/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3083 :
    ((401682921/50000000 : ℚ) : ℝ) ≤ Real.log (3083 : ℕ)
      ∧ Real.log (3083 : ℕ) ≤ ((803365843/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3084 :
    ((803398273/100000000 : ℚ) : ℝ) ≤ Real.log (3084 : ℕ)
      ∧ Real.log (3084 : ℕ) ≤ ((401699137/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3085 :
    ((803430693/100000000 : ℚ) : ℝ) ≤ Real.log (3085 : ℕ)
      ∧ Real.log (3085 : ℕ) ≤ ((401715347/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3086 :
    ((803463103/100000000 : ℚ) : ℝ) ≤ Real.log (3086 : ℕ)
      ∧ Real.log (3086 : ℕ) ≤ ((12554111/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3087 :
    ((401747751/50000000 : ℚ) : ℝ) ≤ Real.log (3087 : ℕ)
      ∧ Real.log (3087 : ℕ) ≤ ((803495503/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3088 :
    ((803527891/100000000 : ℚ) : ℝ) ≤ Real.log (3088 : ℕ)
      ∧ Real.log (3088 : ℕ) ≤ ((200881973/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3089 :
    ((803560269/100000000 : ℚ) : ℝ) ≤ Real.log (3089 : ℕ)
      ∧ Real.log (3089 : ℕ) ≤ ((80356027/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3090 :
    ((160718527/20000000 : ℚ) : ℝ) ≤ Real.log (3090 : ℕ)
      ∧ Real.log (3090 : ℕ) ≤ ((401796319/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3091 :
    ((401812497/50000000 : ℚ) : ℝ) ≤ Real.log (3091 : ℕ)
      ∧ Real.log (3091 : ℕ) ≤ ((160724999/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3092 :
    ((803657339/100000000 : ℚ) : ℝ) ≤ Real.log (3092 : ℕ)
      ∧ Real.log (3092 : ℕ) ≤ ((401828671/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3093 :
    ((803689677/100000000 : ℚ) : ℝ) ≤ Real.log (3093 : ℕ)
      ∧ Real.log (3093 : ℕ) ≤ ((401844839/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3094 :
    ((803722003/100000000 : ℚ) : ℝ) ≤ Real.log (3094 : ℕ)
      ∧ Real.log (3094 : ℕ) ≤ ((200930501/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3095 :
    ((401877159/50000000 : ℚ) : ℝ) ≤ Real.log (3095 : ℕ)
      ∧ Real.log (3095 : ℕ) ≤ ((803754319/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3096 :
    ((803786623/100000000 : ℚ) : ℝ) ≤ Real.log (3096 : ℕ)
      ∧ Real.log (3096 : ℕ) ≤ ((6279583/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3097 :
    ((200954729/25000000 : ℚ) : ℝ) ≤ Real.log (3097 : ℕ)
      ∧ Real.log (3097 : ℕ) ≤ ((803818919/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3098 :
    ((401925601/50000000 : ℚ) : ℝ) ≤ Real.log (3098 : ℕ)
      ∧ Real.log (3098 : ℕ) ≤ ((803851203/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3099 :
    ((32155339/4000000 : ℚ) : ℝ) ≤ Real.log (3099 : ℕ)
      ∧ Real.log (3099 : ℕ) ≤ ((200970869/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3100 :
    ((803915739/100000000 : ℚ) : ℝ) ≤ Real.log (3100 : ℕ)
      ∧ Real.log (3100 : ℕ) ≤ ((40195787/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3101 :
    ((803947991/100000000 : ℚ) : ℝ) ≤ Real.log (3101 : ℕ)
      ∧ Real.log (3101 : ℕ) ≤ ((100493499/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3102 :
    ((401990117/50000000 : ℚ) : ℝ) ≤ Real.log (3102 : ℕ)
      ∧ Real.log (3102 : ℕ) ≤ ((160796047/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3103 :
    ((402006233/50000000 : ℚ) : ℝ) ≤ Real.log (3103 : ℕ)
      ∧ Real.log (3103 : ℕ) ≤ ((804012467/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3104 :
    ((50252793/6250000 : ℚ) : ℝ) ≤ Real.log (3104 : ℕ)
      ∧ Real.log (3104 : ℕ) ≤ ((804044689/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3105 :
    ((804076899/100000000 : ℚ) : ℝ) ≤ Real.log (3105 : ℕ)
      ∧ Real.log (3105 : ℕ) ≤ ((8040769/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3106 :
    ((8041091/1000000 : ℚ) : ℝ) ≤ Real.log (3106 : ℕ)
      ∧ Real.log (3106 : ℕ) ≤ ((804109101/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3107 :
    ((80414129/10000000 : ℚ) : ℝ) ≤ Real.log (3107 : ℕ)
      ∧ Real.log (3107 : ℕ) ≤ ((804141291/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3108 :
    ((804173471/100000000 : ℚ) : ℝ) ≤ Real.log (3108 : ℕ)
      ∧ Real.log (3108 : ℕ) ≤ ((25130421/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3109 :
    ((20105141/2500000 : ℚ) : ℝ) ≤ Real.log (3109 : ℕ)
      ∧ Real.log (3109 : ℕ) ≤ ((804205643/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3110 :
    ((4021189/500000 : ℚ) : ℝ) ≤ Real.log (3110 : ℕ)
      ∧ Real.log (3110 : ℕ) ≤ ((804237801/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3111 :
    ((804269949/100000000 : ℚ) : ℝ) ≤ Real.log (3111 : ℕ)
      ∧ Real.log (3111 : ℕ) ≤ ((16085399/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3112 :
    ((100537761/12500000 : ℚ) : ℝ) ≤ Real.log (3112 : ℕ)
      ∧ Real.log (3112 : ℕ) ≤ ((804302089/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3113 :
    ((804334217/100000000 : ℚ) : ℝ) ≤ Real.log (3113 : ℕ)
      ∧ Real.log (3113 : ℕ) ≤ ((402167109/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3114 :
    ((160873267/20000000 : ℚ) : ℝ) ≤ Real.log (3114 : ℕ)
      ∧ Real.log (3114 : ℕ) ≤ ((3142056/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3115 :
    ((804398443/100000000 : ℚ) : ℝ) ≤ Real.log (3115 : ℕ)
      ∧ Real.log (3115 : ℕ) ≤ ((201099611/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3116 :
    ((40221527/5000000 : ℚ) : ℝ) ≤ Real.log (3116 : ℕ)
      ∧ Real.log (3116 : ℕ) ≤ ((804430541/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3117 :
    ((402231313/50000000 : ℚ) : ℝ) ≤ Real.log (3117 : ℕ)
      ∧ Real.log (3117 : ℕ) ≤ ((804462629/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3118 :
    ((804494703/100000000 : ℚ) : ℝ) ≤ Real.log (3118 : ℕ)
      ∧ Real.log (3118 : ℕ) ≤ ((402247353/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3119 :
    ((804526771/100000000 : ℚ) : ℝ) ≤ Real.log (3119 : ℕ)
      ∧ Real.log (3119 : ℕ) ≤ ((201131693/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3120 :
    ((201139707/25000000 : ℚ) : ℝ) ≤ Real.log (3120 : ℕ)
      ∧ Real.log (3120 : ℕ) ≤ ((804558829/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3121 :
    ((402295437/50000000 : ℚ) : ℝ) ≤ Real.log (3121 : ℕ)
      ∧ Real.log (3121 : ℕ) ≤ ((6436727/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3122 :
    ((80462291/10000000 : ℚ) : ℝ) ≤ Real.log (3122 : ℕ)
      ∧ Real.log (3122 : ℕ) ≤ ((804622911/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3123 :
    ((160930987/20000000 : ℚ) : ℝ) ≤ Real.log (3123 : ℕ)
      ∧ Real.log (3123 : ℕ) ≤ ((100581867/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3124 :
    ((804686951/100000000 : ℚ) : ℝ) ≤ Real.log (3124 : ℕ)
      ∧ Real.log (3124 : ℕ) ≤ ((100585869/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3125 :
    ((201179739/25000000 : ℚ) : ℝ) ≤ Real.log (3125 : ℕ)
      ∧ Real.log (3125 : ℕ) ≤ ((804718957/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3126 :
    ((804750951/100000000 : ℚ) : ℝ) ≤ Real.log (3126 : ℕ)
      ∧ Real.log (3126 : ℕ) ≤ ((100593869/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3127 :
    ((160956587/20000000 : ℚ) : ℝ) ≤ Real.log (3127 : ℕ)
      ∧ Real.log (3127 : ℕ) ≤ ((100597867/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3128 :
    ((80481491/10000000 : ℚ) : ℝ) ≤ Real.log (3128 : ℕ)
      ∧ Real.log (3128 : ℕ) ≤ ((804814911/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3129 :
    ((402423437/50000000 : ℚ) : ℝ) ≤ Real.log (3129 : ℕ)
      ∧ Real.log (3129 : ℕ) ≤ ((257551/32000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3130 :
    ((201219707/25000000 : ℚ) : ℝ) ≤ Real.log (3130 : ℕ)
      ∧ Real.log (3130 : ℕ) ≤ ((804878829/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3131 :
    ((201227693/25000000 : ℚ) : ℝ) ≤ Real.log (3131 : ℕ)
      ∧ Real.log (3131 : ℕ) ≤ ((804910773/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3132 :
    ((160988541/20000000 : ℚ) : ℝ) ≤ Real.log (3132 : ℕ)
      ∧ Real.log (3132 : ℕ) ≤ ((402471353/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3133 :
    ((804974629/100000000 : ℚ) : ℝ) ≤ Real.log (3133 : ℕ)
      ∧ Real.log (3133 : ℕ) ≤ ((80497463/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3134 :
    ((402503271/50000000 : ℚ) : ℝ) ≤ Real.log (3134 : ℕ)
      ∧ Real.log (3134 : ℕ) ≤ ((805006543/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3135 :
    ((161007689/20000000 : ℚ) : ℝ) ≤ Real.log (3135 : ℕ)
      ∧ Real.log (3135 : ℕ) ≤ ((402519223/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3136 :
    ((402535169/50000000 : ℚ) : ℝ) ≤ Real.log (3136 : ℕ)
      ∧ Real.log (3136 : ℕ) ≤ ((805070339/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3137 :
    ((40255111/5000000 : ℚ) : ℝ) ≤ Real.log (3137 : ℕ)
      ∧ Real.log (3137 : ℕ) ≤ ((805102221/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3138 :
    ((805134093/100000000 : ℚ) : ℝ) ≤ Real.log (3138 : ℕ)
      ∧ Real.log (3138 : ℕ) ≤ ((402567047/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3139 :
    ((161033191/20000000 : ℚ) : ℝ) ≤ Real.log (3139 : ℕ)
      ∧ Real.log (3139 : ℕ) ≤ ((201291489/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3140 :
    ((805197807/100000000 : ℚ) : ℝ) ≤ Real.log (3140 : ℕ)
      ∧ Real.log (3140 : ℕ) ≤ ((50324863/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3141 :
    ((50326853/6250000 : ℚ) : ℝ) ≤ Real.log (3141 : ℕ)
      ∧ Real.log (3141 : ℕ) ≤ ((805229651/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3142 :
    ((805261481/100000000 : ℚ) : ℝ) ≤ Real.log (3142 : ℕ)
      ∧ Real.log (3142 : ℕ) ≤ ((402630741/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3143 :
    ((805293303/100000000 : ℚ) : ℝ) ≤ Real.log (3143 : ℕ)
      ∧ Real.log (3143 : ℕ) ≤ ((100661663/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3144 :
    ((161065023/20000000 : ℚ) : ℝ) ≤ Real.log (3144 : ℕ)
      ∧ Real.log (3144 : ℕ) ≤ ((201331279/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3145 :
    ((201339229/25000000 : ℚ) : ℝ) ≤ Real.log (3145 : ℕ)
      ∧ Real.log (3145 : ℕ) ≤ ((805356917/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3146 :
    ((201347177/25000000 : ℚ) : ℝ) ≤ Real.log (3146 : ℕ)
      ∧ Real.log (3146 : ℕ) ≤ ((805388709/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3147 :
    ((805420489/100000000 : ℚ) : ℝ) ≤ Real.log (3147 : ℕ)
      ∧ Real.log (3147 : ℕ) ≤ ((80542049/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3148 :
    ((805452259/100000000 : ℚ) : ℝ) ≤ Real.log (3148 : ℕ)
      ∧ Real.log (3148 : ℕ) ≤ ((402726131/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3149 :
    ((402742011/50000000 : ℚ) : ℝ) ≤ Real.log (3149 : ℕ)
      ∧ Real.log (3149 : ℕ) ≤ ((805484023/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3150 :
    ((805515773/100000000 : ℚ) : ℝ) ≤ Real.log (3150 : ℕ)
      ∧ Real.log (3150 : ℕ) ≤ ((402757887/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3151 :
    ((402773757/50000000 : ℚ) : ℝ) ≤ Real.log (3151 : ℕ)
      ∧ Real.log (3151 : ℕ) ≤ ((161109503/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3152 :
    ((161115849/20000000 : ℚ) : ℝ) ≤ Real.log (3152 : ℕ)
      ∧ Real.log (3152 : ℕ) ≤ ((402789623/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3153 :
    ((201402741/25000000 : ℚ) : ℝ) ≤ Real.log (3153 : ℕ)
      ∧ Real.log (3153 : ℕ) ≤ ((805610967/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3154 :
    ((201410669/25000000 : ℚ) : ℝ) ≤ Real.log (3154 : ℕ)
      ∧ Real.log (3154 : ℕ) ≤ ((805642677/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3155 :
    ((805674377/100000000 : ℚ) : ℝ) ≤ Real.log (3155 : ℕ)
      ∧ Real.log (3155 : ℕ) ≤ ((402837189/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3156 :
    ((201426517/25000000 : ℚ) : ℝ) ≤ Real.log (3156 : ℕ)
      ∧ Real.log (3156 : ℕ) ≤ ((805706069/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3157 :
    ((201434437/25000000 : ℚ) : ℝ) ≤ Real.log (3157 : ℕ)
      ∧ Real.log (3157 : ℕ) ≤ ((805737749/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3158 :
    ((805769419/100000000 : ℚ) : ℝ) ≤ Real.log (3158 : ℕ)
      ∧ Real.log (3158 : ℕ) ≤ ((40288471/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3159 :
    ((20145027/2500000 : ℚ) : ℝ) ≤ Real.log (3159 : ℕ)
      ∧ Real.log (3159 : ℕ) ≤ ((805801081/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3160 :
    ((80583273/10000000 : ℚ) : ℝ) ≤ Real.log (3160 : ℕ)
      ∧ Real.log (3160 : ℕ) ≤ ((805832731/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3161 :
    ((805864371/100000000 : ℚ) : ℝ) ≤ Real.log (3161 : ℕ)
      ∧ Real.log (3161 : ℕ) ≤ ((201466093/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3162 :
    ((805896001/100000000 : ℚ) : ℝ) ≤ Real.log (3162 : ℕ)
      ∧ Real.log (3162 : ℕ) ≤ ((402948001/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3163 :
    ((402963811/50000000 : ℚ) : ℝ) ≤ Real.log (3163 : ℕ)
      ∧ Real.log (3163 : ℕ) ≤ ((805927623/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3164 :
    ((12593113/1562500 : ℚ) : ℝ) ≤ Real.log (3164 : ℕ)
      ∧ Real.log (3164 : ℕ) ≤ ((805959233/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3165 :
    ((805990833/100000000 : ℚ) : ℝ) ≤ Real.log (3165 : ℕ)
      ∧ Real.log (3165 : ℕ) ≤ ((402995417/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3166 :
    ((100752803/12500000 : ℚ) : ℝ) ≤ Real.log (3166 : ℕ)
      ∧ Real.log (3166 : ℕ) ≤ ((32240897/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3167 :
    ((201513501/25000000 : ℚ) : ℝ) ≤ Real.log (3167 : ℕ)
      ∧ Real.log (3167 : ℕ) ≤ ((161210801/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3168 :
    ((32243423/4000000 : ℚ) : ℝ) ≤ Real.log (3168 : ℕ)
      ∧ Real.log (3168 : ℕ) ≤ ((100760697/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3169 :
    ((403058567/50000000 : ℚ) : ℝ) ≤ Real.log (3169 : ℕ)
      ∧ Real.log (3169 : ℕ) ≤ ((806117137/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3170 :
    ((403074343/50000000 : ℚ) : ℝ) ≤ Real.log (3170 : ℕ)
      ∧ Real.log (3170 : ℕ) ≤ ((806148687/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3171 :
    ((806180227/100000000 : ℚ) : ℝ) ≤ Real.log (3171 : ℕ)
      ∧ Real.log (3171 : ℕ) ≤ ((201545057/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3172 :
    ((403105879/50000000 : ℚ) : ℝ) ≤ Real.log (3172 : ℕ)
      ∧ Real.log (3172 : ℕ) ≤ ((806211759/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3173 :
    ((806243279/100000000 : ℚ) : ℝ) ≤ Real.log (3173 : ℕ)
      ∧ Real.log (3173 : ℕ) ≤ ((10078041/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3174 :
    ((80627479/10000000 : ℚ) : ℝ) ≤ Real.log (3174 : ℕ)
      ∧ Real.log (3174 : ℕ) ≤ ((806274791/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3175 :
    ((806306291/100000000 : ℚ) : ℝ) ≤ Real.log (3175 : ℕ)
      ∧ Real.log (3175 : ℕ) ≤ ((201576573/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3176 :
    ((403168891/50000000 : ℚ) : ℝ) ≤ Real.log (3176 : ℕ)
      ∧ Real.log (3176 : ℕ) ≤ ((806337783/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3177 :
    ((806369263/100000000 : ℚ) : ℝ) ≤ Real.log (3177 : ℕ)
      ∧ Real.log (3177 : ℕ) ≤ ((50398079/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3178 :
    ((403200367/50000000 : ℚ) : ℝ) ≤ Real.log (3178 : ℕ)
      ∧ Real.log (3178 : ℕ) ≤ ((161280147/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3179 :
    ((201608049/25000000 : ℚ) : ℝ) ≤ Real.log (3179 : ℕ)
      ∧ Real.log (3179 : ℕ) ≤ ((806432197/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3180 :
    ((806463647/100000000 : ℚ) : ℝ) ≤ Real.log (3180 : ℕ)
      ∧ Real.log (3180 : ℕ) ≤ ((25201989/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3181 :
    ((806495089/100000000 : ℚ) : ℝ) ≤ Real.log (3181 : ℕ)
      ∧ Real.log (3181 : ℕ) ≤ ((80649509/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3182 :
    ((20163163/2500000 : ℚ) : ℝ) ≤ Real.log (3182 : ℕ)
      ∧ Real.log (3182 : ℕ) ≤ ((806526521/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3183 :
    ((403278971/50000000 : ℚ) : ℝ) ≤ Real.log (3183 : ℕ)
      ∧ Real.log (3183 : ℕ) ≤ ((806557943/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3184 :
    ((403294677/50000000 : ℚ) : ℝ) ≤ Real.log (3184 : ℕ)
      ∧ Real.log (3184 : ℕ) ≤ ((161317871/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3185 :
    ((201655189/25000000 : ℚ) : ℝ) ≤ Real.log (3185 : ℕ)
      ∧ Real.log (3185 : ℕ) ≤ ((806620757/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3186 :
    ((806652149/100000000 : ℚ) : ℝ) ≤ Real.log (3186 : ℕ)
      ∧ Real.log (3186 : ℕ) ≤ ((16133043/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3187 :
    ((806683531/100000000 : ℚ) : ℝ) ≤ Real.log (3187 : ℕ)
      ∧ Real.log (3187 : ℕ) ≤ ((201670883/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3188 :
    ((403357451/50000000 : ℚ) : ℝ) ≤ Real.log (3188 : ℕ)
      ∧ Real.log (3188 : ℕ) ≤ ((161342981/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3189 :
    ((403373133/50000000 : ℚ) : ℝ) ≤ Real.log (3189 : ℕ)
      ∧ Real.log (3189 : ℕ) ≤ ((806746267/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3190 :
    ((806777619/100000000 : ℚ) : ℝ) ≤ Real.log (3190 : ℕ)
      ∧ Real.log (3190 : ℕ) ≤ ((40338881/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3191 :
    ((403404481/50000000 : ℚ) : ℝ) ≤ Real.log (3191 : ℕ)
      ∧ Real.log (3191 : ℕ) ≤ ((806808963/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3192 :
    ((161368059/20000000 : ℚ) : ℝ) ≤ Real.log (3192 : ℕ)
      ∧ Real.log (3192 : ℕ) ≤ ((100855037/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3193 :
    ((806871619/100000000 : ℚ) : ℝ) ≤ Real.log (3193 : ℕ)
      ∧ Real.log (3193 : ℕ) ≤ ((40343581/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3194 :
    ((201725733/25000000 : ℚ) : ℝ) ≤ Real.log (3194 : ℕ)
      ∧ Real.log (3194 : ℕ) ≤ ((806902933/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3195 :
    ((201733559/25000000 : ℚ) : ℝ) ≤ Real.log (3195 : ℕ)
      ∧ Real.log (3195 : ℕ) ≤ ((806934237/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3196 :
    ((80696553/10000000 : ℚ) : ℝ) ≤ Real.log (3196 : ℕ)
      ∧ Real.log (3196 : ℕ) ≤ ((806965531/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3197 :
    ((403498407/50000000 : ℚ) : ℝ) ≤ Real.log (3197 : ℕ)
      ∧ Real.log (3197 : ℕ) ≤ ((161399363/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3198 :
    ((807028089/100000000 : ℚ) : ℝ) ≤ Real.log (3198 : ℕ)
      ∧ Real.log (3198 : ℕ) ≤ ((80702809/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3199 :
    ((100882419/12500000 : ℚ) : ℝ) ≤ Real.log (3199 : ℕ)
      ∧ Real.log (3199 : ℕ) ≤ ((161411871/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3200 :
    ((50443163/6250000 : ℚ) : ℝ) ≤ Real.log (3200 : ℕ)
      ∧ Real.log (3200 : ℕ) ≤ ((807090609/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3201 :
    ((201780463/25000000 : ℚ) : ℝ) ≤ Real.log (3201 : ℕ)
      ∧ Real.log (3201 : ℕ) ≤ ((161424371/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3202 :
    ((807153089/100000000 : ℚ) : ℝ) ≤ Real.log (3202 : ℕ)
      ∧ Real.log (3202 : ℕ) ≤ ((80715309/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3203 :
    ((807184313/100000000 : ℚ) : ℝ) ≤ Real.log (3203 : ℕ)
      ∧ Real.log (3203 : ℕ) ≤ ((201796079/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3204 :
    ((80721553/10000000 : ℚ) : ℝ) ≤ Real.log (3204 : ℕ)
      ∧ Real.log (3204 : ℕ) ≤ ((807215531/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3205 :
    ((50452921/6250000 : ℚ) : ℝ) ≤ Real.log (3205 : ℕ)
      ∧ Real.log (3205 : ℕ) ≤ ((807246737/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3206 :
    ((807277933/100000000 : ℚ) : ℝ) ≤ Real.log (3206 : ℕ)
      ∧ Real.log (3206 : ℕ) ≤ ((403638967/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3207 :
    ((403654559/50000000 : ℚ) : ℝ) ≤ Real.log (3207 : ℕ)
      ∧ Real.log (3207 : ℕ) ≤ ((807309121/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3208 :
    ((100917537/12500000 : ℚ) : ℝ) ≤ Real.log (3208 : ℕ)
      ∧ Real.log (3208 : ℕ) ≤ ((807340297/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3209 :
    ((100921433/12500000 : ℚ) : ℝ) ≤ Real.log (3209 : ℕ)
      ∧ Real.log (3209 : ℕ) ≤ ((161474293/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3210 :
    ((807402621/100000000 : ℚ) : ℝ) ≤ Real.log (3210 : ℕ)
      ∧ Real.log (3210 : ℕ) ≤ ((403701311/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3211 :
    ((807433769/100000000 : ℚ) : ℝ) ≤ Real.log (3211 : ℕ)
      ∧ Real.log (3211 : ℕ) ≤ ((80743377/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3212 :
    ((807464907/100000000 : ℚ) : ℝ) ≤ Real.log (3212 : ℕ)
      ∧ Real.log (3212 : ℕ) ≤ ((201866227/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3213 :
    ((161499207/20000000 : ℚ) : ℝ) ≤ Real.log (3213 : ℕ)
      ∧ Real.log (3213 : ℕ) ≤ ((201874009/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3214 :
    ((403763577/50000000 : ℚ) : ℝ) ≤ Real.log (3214 : ℕ)
      ∧ Real.log (3214 : ℕ) ≤ ((161505431/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3215 :
    ((807558263/100000000 : ℚ) : ℝ) ≤ Real.log (3215 : ℕ)
      ∧ Real.log (3215 : ℕ) ≤ ((100944783/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3216 :
    ((403794681/50000000 : ℚ) : ℝ) ≤ Real.log (3216 : ℕ)
      ∧ Real.log (3216 : ℕ) ≤ ((161517873/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3217 :
    ((201905113/25000000 : ℚ) : ℝ) ≤ Real.log (3217 : ℕ)
      ∧ Real.log (3217 : ℕ) ≤ ((807620453/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3218 :
    ((201912883/25000000 : ℚ) : ℝ) ≤ Real.log (3218 : ℕ)
      ∧ Real.log (3218 : ℕ) ≤ ((807651533/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3219 :
    ((807682603/100000000 : ℚ) : ℝ) ≤ Real.log (3219 : ℕ)
      ∧ Real.log (3219 : ℕ) ≤ ((201920651/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3220 :
    ((807713663/100000000 : ℚ) : ℝ) ≤ Real.log (3220 : ℕ)
      ∧ Real.log (3220 : ℕ) ≤ ((6310263/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3221 :
    ((403872357/50000000 : ℚ) : ℝ) ≤ Real.log (3221 : ℕ)
      ∧ Real.log (3221 : ℕ) ≤ ((161548943/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3222 :
    ((201943939/25000000 : ℚ) : ℝ) ≤ Real.log (3222 : ℕ)
      ∧ Real.log (3222 : ℕ) ≤ ((807775757/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3223 :
    ((201951697/25000000 : ℚ) : ℝ) ≤ Real.log (3223 : ℕ)
      ∧ Real.log (3223 : ℕ) ≤ ((807806789/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3224 :
    ((80783781/10000000 : ℚ) : ℝ) ≤ Real.log (3224 : ℕ)
      ∧ Real.log (3224 : ℕ) ≤ ((807837811/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3225 :
    ((403934411/50000000 : ℚ) : ℝ) ≤ Real.log (3225 : ℕ)
      ∧ Real.log (3225 : ℕ) ≤ ((807868823/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3226 :
    ((32315993/4000000 : ℚ) : ℝ) ≤ Real.log (3226 : ℕ)
      ∧ Real.log (3226 : ℕ) ≤ ((403949913/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3227 :
    ((807930819/100000000 : ℚ) : ℝ) ≤ Real.log (3227 : ℕ)
      ∧ Real.log (3227 : ℕ) ≤ ((40396541/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3228 :
    ((403980901/50000000 : ℚ) : ℝ) ≤ Real.log (3228 : ℕ)
      ∧ Real.log (3228 : ℕ) ≤ ((807961803/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3229 :
    ((807992777/100000000 : ℚ) : ℝ) ≤ Real.log (3229 : ℕ)
      ∧ Real.log (3229 : ℕ) ≤ ((403996389/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3230 :
    ((808023741/100000000 : ℚ) : ℝ) ≤ Real.log (3230 : ℕ)
      ∧ Real.log (3230 : ℕ) ≤ ((404011871/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3231 :
    ((101006837/12500000 : ℚ) : ℝ) ≤ Real.log (3231 : ℕ)
      ∧ Real.log (3231 : ℕ) ≤ ((808054697/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3232 :
    ((20202141/2500000 : ℚ) : ℝ) ≤ Real.log (3232 : ℕ)
      ∧ Real.log (3232 : ℕ) ≤ ((808085643/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3233 :
    ((808116577/100000000 : ℚ) : ℝ) ≤ Real.log (3233 : ℕ)
      ∧ Real.log (3233 : ℕ) ≤ ((404058289/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3234 :
    ((808147503/100000000 : ℚ) : ℝ) ≤ Real.log (3234 : ℕ)
      ∧ Real.log (3234 : ℕ) ≤ ((404073753/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3235 :
    ((40408921/5000000 : ℚ) : ℝ) ≤ Real.log (3235 : ℕ)
      ∧ Real.log (3235 : ℕ) ≤ ((808178421/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3236 :
    ((808209327/100000000 : ℚ) : ℝ) ≤ Real.log (3236 : ℕ)
      ∧ Real.log (3236 : ℕ) ≤ ((50513083/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3237 :
    ((32329609/4000000 : ℚ) : ℝ) ≤ Real.log (3237 : ℕ)
      ∧ Real.log (3237 : ℕ) ≤ ((404120113/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3238 :
    ((808271113/100000000 : ℚ) : ℝ) ≤ Real.log (3238 : ℕ)
      ∧ Real.log (3238 : ℕ) ≤ ((404135557/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3239 :
    ((808301991/100000000 : ℚ) : ℝ) ≤ Real.log (3239 : ℕ)
      ∧ Real.log (3239 : ℕ) ≤ ((101037749/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3240 :
    ((40416643/5000000 : ℚ) : ℝ) ≤ Real.log (3240 : ℕ)
      ∧ Real.log (3240 : ℕ) ≤ ((808332861/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3241 :
    ((20209093/2500000 : ℚ) : ℝ) ≤ Real.log (3241 : ℕ)
      ∧ Real.log (3241 : ℕ) ≤ ((808363721/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3242 :
    ((80839457/10000000 : ℚ) : ℝ) ≤ Real.log (3242 : ℕ)
      ∧ Real.log (3242 : ℕ) ≤ ((808394571/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3243 :
    ((80842541/10000000 : ℚ) : ℝ) ≤ Real.log (3243 : ℕ)
      ∧ Real.log (3243 : ℕ) ≤ ((808425411/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3244 :
    ((808456241/100000000 : ℚ) : ℝ) ≤ Real.log (3244 : ℕ)
      ∧ Real.log (3244 : ℕ) ≤ ((404228121/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3245 :
    ((404243531/50000000 : ℚ) : ℝ) ≤ Real.log (3245 : ℕ)
      ∧ Real.log (3245 : ℕ) ≤ ((808487063/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3246 :
    ((404258937/50000000 : ℚ) : ℝ) ≤ Real.log (3246 : ℕ)
      ∧ Real.log (3246 : ℕ) ≤ ((6468143/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3247 :
    ((808548677/100000000 : ℚ) : ℝ) ≤ Real.log (3247 : ℕ)
      ∧ Real.log (3247 : ℕ) ≤ ((404274339/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3248 :
    ((80857947/10000000 : ℚ) : ℝ) ≤ Real.log (3248 : ℕ)
      ∧ Real.log (3248 : ℕ) ≤ ((808579471/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3249 :
    ((808610253/100000000 : ℚ) : ℝ) ≤ Real.log (3249 : ℕ)
      ∧ Real.log (3249 : ℕ) ≤ ((404305127/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3250 :
    ((808641027/100000000 : ℚ) : ℝ) ≤ Real.log (3250 : ℕ)
      ∧ Real.log (3250 : ℕ) ≤ ((202160257/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3251 :
    ((808671791/100000000 : ℚ) : ℝ) ≤ Real.log (3251 : ℕ)
      ∧ Real.log (3251 : ℕ) ≤ ((404335897/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3252 :
    ((808702547/100000000 : ℚ) : ℝ) ≤ Real.log (3252 : ℕ)
      ∧ Real.log (3252 : ℕ) ≤ ((202175637/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3253 :
    ((202183323/25000000 : ℚ) : ℝ) ≤ Real.log (3253 : ℕ)
      ∧ Real.log (3253 : ℕ) ≤ ((808733293/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3254 :
    ((202191007/25000000 : ℚ) : ℝ) ≤ Real.log (3254 : ℕ)
      ∧ Real.log (3254 : ℕ) ≤ ((808764029/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3255 :
    ((161758951/20000000 : ℚ) : ℝ) ≤ Real.log (3255 : ℕ)
      ∧ Real.log (3255 : ℕ) ≤ ((202198689/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3256 :
    ((6318949/781250 : ℚ) : ℝ) ≤ Real.log (3256 : ℕ)
      ∧ Real.log (3256 : ℕ) ≤ ((808825473/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3257 :
    ((40442809/5000000 : ℚ) : ℝ) ≤ Real.log (3257 : ℕ)
      ∧ Real.log (3257 : ℕ) ≤ ((808856181/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3258 :
    ((404443439/50000000 : ℚ) : ℝ) ≤ Real.log (3258 : ℕ)
      ∧ Real.log (3258 : ℕ) ≤ ((808886879/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3259 :
    ((808917567/100000000 : ℚ) : ℝ) ≤ Real.log (3259 : ℕ)
      ∧ Real.log (3259 : ℕ) ≤ ((12639337/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3260 :
    ((808948247/100000000 : ℚ) : ℝ) ≤ Real.log (3260 : ℕ)
      ∧ Real.log (3260 : ℕ) ≤ ((101118531/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3261 :
    ((808978917/100000000 : ℚ) : ℝ) ≤ Real.log (3261 : ℕ)
      ∧ Real.log (3261 : ℕ) ≤ ((404489459/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3262 :
    ((404504789/50000000 : ℚ) : ℝ) ≤ Real.log (3262 : ℕ)
      ∧ Real.log (3262 : ℕ) ≤ ((809009579/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3263 :
    ((809040229/100000000 : ℚ) : ℝ) ≤ Real.log (3263 : ℕ)
      ∧ Real.log (3263 : ℕ) ≤ ((80904023/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3264 :
    ((809070871/100000000 : ℚ) : ℝ) ≤ Real.log (3264 : ℕ)
      ∧ Real.log (3264 : ℕ) ≤ ((101133859/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3265 :
    ((12642211/1562500 : ℚ) : ℝ) ≤ Real.log (3265 : ℕ)
      ∧ Real.log (3265 : ℕ) ≤ ((161820301/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3266 :
    ((809132127/100000000 : ℚ) : ℝ) ≤ Real.log (3266 : ℕ)
      ∧ Real.log (3266 : ℕ) ≤ ((25285379/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3267 :
    ((809162741/100000000 : ℚ) : ℝ) ≤ Real.log (3267 : ℕ)
      ∧ Real.log (3267 : ℕ) ≤ ((404581371/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3268 :
    ((161838669/20000000 : ℚ) : ℝ) ≤ Real.log (3268 : ℕ)
      ∧ Real.log (3268 : ℕ) ≤ ((404596673/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3269 :
    ((40461197/5000000 : ℚ) : ℝ) ≤ Real.log (3269 : ℕ)
      ∧ Real.log (3269 : ℕ) ≤ ((809223941/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3270 :
    ((404627263/50000000 : ℚ) : ℝ) ≤ Real.log (3270 : ℕ)
      ∧ Real.log (3270 : ℕ) ≤ ((809254527/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3271 :
    ((404642551/50000000 : ℚ) : ℝ) ≤ Real.log (3271 : ℕ)
      ∧ Real.log (3271 : ℕ) ≤ ((809285103/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3272 :
    ((809315669/100000000 : ℚ) : ℝ) ≤ Real.log (3272 : ℕ)
      ∧ Real.log (3272 : ℕ) ≤ ((80931567/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3273 :
    ((809346227/100000000 : ℚ) : ℝ) ≤ Real.log (3273 : ℕ)
      ∧ Real.log (3273 : ℕ) ≤ ((202336557/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3274 :
    ((32375071/4000000 : ℚ) : ℝ) ≤ Real.log (3274 : ℕ)
      ∧ Real.log (3274 : ℕ) ≤ ((101172097/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3275 :
    ((404703657/50000000 : ℚ) : ℝ) ≤ Real.log (3275 : ℕ)
      ∧ Real.log (3275 : ℕ) ≤ ((161881463/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3276 :
    ((202359461/25000000 : ℚ) : ℝ) ≤ Real.log (3276 : ℕ)
      ∧ Real.log (3276 : ℕ) ≤ ((161887569/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3277 :
    ((202367091/25000000 : ℚ) : ℝ) ≤ Real.log (3277 : ℕ)
      ∧ Real.log (3277 : ℕ) ≤ ((161893673/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3278 :
    ((6475991/800000 : ℚ) : ℝ) ≤ Real.log (3278 : ℕ)
      ∧ Real.log (3278 : ℕ) ≤ ((202374719/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3279 :
    ((809529377/100000000 : ℚ) : ℝ) ≤ Real.log (3279 : ℕ)
      ∧ Real.log (3279 : ℕ) ≤ ((404764689/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3280 :
    ((80955987/10000000 : ℚ) : ℝ) ≤ Real.log (3280 : ℕ)
      ∧ Real.log (3280 : ℕ) ≤ ((809559871/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3281 :
    ((809590353/100000000 : ℚ) : ℝ) ≤ Real.log (3281 : ℕ)
      ∧ Real.log (3281 : ℕ) ≤ ((404795177/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3282 :
    ((809620827/100000000 : ℚ) : ℝ) ≤ Real.log (3282 : ℕ)
      ∧ Real.log (3282 : ℕ) ≤ ((202405207/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3283 :
    ((809651291/100000000 : ℚ) : ℝ) ≤ Real.log (3283 : ℕ)
      ∧ Real.log (3283 : ℕ) ≤ ((202412823/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3284 :
    ((809681747/100000000 : ℚ) : ℝ) ≤ Real.log (3284 : ℕ)
      ∧ Real.log (3284 : ℕ) ≤ ((202420437/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3285 :
    ((809712193/100000000 : ℚ) : ℝ) ≤ Real.log (3285 : ℕ)
      ∧ Real.log (3285 : ℕ) ≤ ((404856097/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3286 :
    ((809742629/100000000 : ℚ) : ℝ) ≤ Real.log (3286 : ℕ)
      ∧ Real.log (3286 : ℕ) ≤ ((80974263/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3287 :
    ((809773057/100000000 : ℚ) : ℝ) ≤ Real.log (3287 : ℕ)
      ∧ Real.log (3287 : ℕ) ≤ ((404886529/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3288 :
    ((32392139/4000000 : ℚ) : ℝ) ≤ Real.log (3288 : ℕ)
      ∧ Real.log (3288 : ℕ) ≤ ((202450869/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3289 :
    ((202458471/25000000 : ℚ) : ℝ) ≤ Real.log (3289 : ℕ)
      ∧ Real.log (3289 : ℕ) ≤ ((161966777/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3290 :
    ((202466071/25000000 : ℚ) : ℝ) ≤ Real.log (3290 : ℕ)
      ∧ Real.log (3290 : ℕ) ≤ ((161972857/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3291 :
    ((404947337/50000000 : ℚ) : ℝ) ≤ Real.log (3291 : ℕ)
      ∧ Real.log (3291 : ℕ) ≤ ((32395787/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3292 :
    ((12655079/1562500 : ℚ) : ℝ) ≤ Real.log (3292 : ℕ)
      ∧ Real.log (3292 : ℕ) ≤ ((809925057/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3293 :
    ((202488857/25000000 : ℚ) : ℝ) ≤ Real.log (3293 : ℕ)
      ∧ Real.log (3293 : ℕ) ≤ ((809955429/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3294 :
    ((809985791/100000000 : ℚ) : ℝ) ≤ Real.log (3294 : ℕ)
      ∧ Real.log (3294 : ℕ) ≤ ((3164007/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3295 :
    ((50626009/6250000 : ℚ) : ℝ) ≤ Real.log (3295 : ℕ)
      ∧ Real.log (3295 : ℕ) ≤ ((162003229/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3296 :
    ((810046489/100000000 : ℚ) : ℝ) ≤ Real.log (3296 : ℕ)
      ∧ Real.log (3296 : ℕ) ≤ ((81004649/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3297 :
    ((101259603/12500000 : ℚ) : ℝ) ≤ Real.log (3297 : ℕ)
      ∧ Real.log (3297 : ℕ) ≤ ((32403073/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3298 :
    ((16202143/2000000 : ℚ) : ℝ) ≤ Real.log (3298 : ℕ)
      ∧ Real.log (3298 : ℕ) ≤ ((810107151/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3299 :
    ((810137467/100000000 : ℚ) : ℝ) ≤ Real.log (3299 : ℕ)
      ∧ Real.log (3299 : ℕ) ≤ ((202534367/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3300 :
    ((405083887/50000000 : ℚ) : ℝ) ≤ Real.log (3300 : ℕ)
      ∧ Real.log (3300 : ℕ) ≤ ((32406711/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3301 :
    ((810198073/100000000 : ℚ) : ℝ) ≤ Real.log (3301 : ℕ)
      ∧ Real.log (3301 : ℕ) ≤ ((405099037/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3302 :
    ((405114181/50000000 : ℚ) : ℝ) ≤ Real.log (3302 : ℕ)
      ∧ Real.log (3302 : ℕ) ≤ ((810228363/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3303 :
    ((405129321/50000000 : ℚ) : ℝ) ≤ Real.log (3303 : ℕ)
      ∧ Real.log (3303 : ℕ) ≤ ((810258643/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3304 :
    ((810288913/100000000 : ℚ) : ℝ) ≤ Real.log (3304 : ℕ)
      ∧ Real.log (3304 : ℕ) ≤ ((405144457/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3305 :
    ((32412767/4000000 : ℚ) : ℝ) ≤ Real.log (3305 : ℕ)
      ∧ Real.log (3305 : ℕ) ≤ ((101289897/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3306 :
    ((810349427/100000000 : ℚ) : ℝ) ≤ Real.log (3306 : ℕ)
      ∧ Real.log (3306 : ℕ) ≤ ((202587357/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3307 :
    ((810379671/100000000 : ℚ) : ℝ) ≤ Real.log (3307 : ℕ)
      ∧ Real.log (3307 : ℕ) ≤ ((101297459/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3308 :
    ((162081981/20000000 : ℚ) : ℝ) ≤ Real.log (3308 : ℕ)
      ∧ Real.log (3308 : ℕ) ≤ ((405204953/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3309 :
    ((81044013/10000000 : ℚ) : ℝ) ≤ Real.log (3309 : ℕ)
      ∧ Real.log (3309 : ℕ) ≤ ((810440131/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3310 :
    ((405235173/50000000 : ℚ) : ℝ) ≤ Real.log (3310 : ℕ)
      ∧ Real.log (3310 : ℕ) ≤ ((810470347/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3311 :
    ((810500553/100000000 : ℚ) : ℝ) ≤ Real.log (3311 : ℕ)
      ∧ Real.log (3311 : ℕ) ≤ ((405250277/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3312 :
    ((810530751/100000000 : ℚ) : ℝ) ≤ Real.log (3312 : ℕ)
      ∧ Real.log (3312 : ℕ) ≤ ((12664543/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3313 :
    ((40528047/5000000 : ℚ) : ℝ) ≤ Real.log (3313 : ℕ)
      ∧ Real.log (3313 : ℕ) ≤ ((810560941/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3314 :
    ((810591119/100000000 : ℚ) : ℝ) ≤ Real.log (3314 : ℕ)
      ∧ Real.log (3314 : ℕ) ≤ ((10132389/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3315 :
    ((81062129/10000000 : ℚ) : ℝ) ≤ Real.log (3315 : ℕ)
      ∧ Real.log (3315 : ℕ) ≤ ((810621291/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3316 :
    ((810651451/100000000 : ℚ) : ℝ) ≤ Real.log (3316 : ℕ)
      ∧ Real.log (3316 : ℕ) ≤ ((202662863/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3317 :
    ((810681603/100000000 : ℚ) : ℝ) ≤ Real.log (3317 : ℕ)
      ∧ Real.log (3317 : ℕ) ≤ ((202670401/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3318 :
    ((810711747/100000000 : ℚ) : ℝ) ≤ Real.log (3318 : ℕ)
      ∧ Real.log (3318 : ℕ) ≤ ((202677937/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3319 :
    ((810741881/100000000 : ℚ) : ℝ) ≤ Real.log (3319 : ℕ)
      ∧ Real.log (3319 : ℕ) ≤ ((405370941/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3320 :
    ((405386003/50000000 : ℚ) : ℝ) ≤ Real.log (3320 : ℕ)
      ∧ Real.log (3320 : ℕ) ≤ ((810772007/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3321 :
    ((405401061/50000000 : ℚ) : ℝ) ≤ Real.log (3321 : ℕ)
      ∧ Real.log (3321 : ℕ) ≤ ((810802123/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3322 :
    ((202708057/25000000 : ℚ) : ℝ) ≤ Real.log (3322 : ℕ)
      ∧ Real.log (3322 : ℕ) ≤ ((810832231/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3323 :
    ((405431163/50000000 : ℚ) : ℝ) ≤ Real.log (3323 : ℕ)
      ∧ Real.log (3323 : ℕ) ≤ ((810862327/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3324 :
    ((162178483/20000000 : ℚ) : ℝ) ≤ Real.log (3324 : ℕ)
      ∧ Real.log (3324 : ℕ) ≤ ((6335097/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3325 :
    ((162184499/20000000 : ℚ) : ℝ) ≤ Real.log (3325 : ℕ)
      ∧ Real.log (3325 : ℕ) ≤ ((3167666/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3326 :
    ((202738141/25000000 : ℚ) : ℝ) ≤ Real.log (3326 : ℕ)
      ∧ Real.log (3326 : ℕ) ≤ ((810952567/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3327 :
    ((810982627/100000000 : ℚ) : ℝ) ≤ Real.log (3327 : ℕ)
      ∧ Real.log (3327 : ℕ) ≤ ((202745657/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3328 :
    ((20275317/2500000 : ℚ) : ℝ) ≤ Real.log (3328 : ℕ)
      ∧ Real.log (3328 : ℕ) ≤ ((811012681/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3329 :
    ((811042723/100000000 : ℚ) : ℝ) ≤ Real.log (3329 : ℕ)
      ∧ Real.log (3329 : ℕ) ≤ ((202760681/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3330 :
    ((405536379/50000000 : ℚ) : ℝ) ≤ Real.log (3330 : ℕ)
      ∧ Real.log (3330 : ℕ) ≤ ((811072759/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3331 :
    ((811102783/100000000 : ℚ) : ℝ) ≤ Real.log (3331 : ℕ)
      ∧ Real.log (3331 : ℕ) ≤ ((12673481/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3332 :
    ((253479/31250 : ℚ) : ℝ) ≤ Real.log (3332 : ℕ)
      ∧ Real.log (3332 : ℕ) ≤ ((811132801/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3333 :
    ((811162807/100000000 : ℚ) : ℝ) ≤ Real.log (3333 : ℕ)
      ∧ Real.log (3333 : ℕ) ≤ ((101395351/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3334 :
    ((405596403/50000000 : ℚ) : ℝ) ≤ Real.log (3334 : ℕ)
      ∧ Real.log (3334 : ℕ) ≤ ((811192807/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3335 :
    ((162244559/20000000 : ℚ) : ℝ) ≤ Real.log (3335 : ℕ)
      ∧ Real.log (3335 : ℕ) ≤ ((202805699/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3336 :
    ((101406597/12500000 : ℚ) : ℝ) ≤ Real.log (3336 : ℕ)
      ∧ Real.log (3336 : ℕ) ≤ ((811252777/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3337 :
    ((811282747/100000000 : ℚ) : ℝ) ≤ Real.log (3337 : ℕ)
      ∧ Real.log (3337 : ℕ) ≤ ((202820687/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3338 :
    ((81131271/10000000 : ℚ) : ℝ) ≤ Real.log (3338 : ℕ)
      ∧ Real.log (3338 : ℕ) ≤ ((811312711/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3339 :
    ((405671331/50000000 : ℚ) : ℝ) ≤ Real.log (3339 : ℕ)
      ∧ Real.log (3339 : ℕ) ≤ ((162268533/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3340 :
    ((12677697/1562500 : ℚ) : ℝ) ≤ Real.log (3340 : ℕ)
      ∧ Real.log (3340 : ℕ) ≤ ((811372609/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3341 :
    ((50712659/6250000 : ℚ) : ℝ) ≤ Real.log (3341 : ℕ)
      ∧ Real.log (3341 : ℕ) ≤ ((162280509/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3342 :
    ((81143247/10000000 : ℚ) : ℝ) ≤ Real.log (3342 : ℕ)
      ∧ Real.log (3342 : ℕ) ≤ ((811432471/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3343 :
    ((202865597/25000000 : ℚ) : ℝ) ≤ Real.log (3343 : ℕ)
      ∧ Real.log (3343 : ℕ) ≤ ((811462389/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3344 :
    ((811492297/100000000 : ℚ) : ℝ) ≤ Real.log (3344 : ℕ)
      ∧ Real.log (3344 : ℕ) ≤ ((405746149/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3345 :
    ((811522197/100000000 : ℚ) : ℝ) ≤ Real.log (3345 : ℕ)
      ∧ Real.log (3345 : ℕ) ≤ ((405761099/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3346 :
    ((101444011/12500000 : ℚ) : ℝ) ≤ Real.log (3346 : ℕ)
      ∧ Real.log (3346 : ℕ) ≤ ((811552089/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3347 :
    ((81158197/10000000 : ℚ) : ℝ) ≤ Real.log (3347 : ℕ)
      ∧ Real.log (3347 : ℕ) ≤ ((811581971/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3348 :
    ((811611843/100000000 : ℚ) : ℝ) ≤ Real.log (3348 : ℕ)
      ∧ Real.log (3348 : ℕ) ≤ ((202902961/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3349 :
    ((811641707/100000000 : ℚ) : ℝ) ≤ Real.log (3349 : ℕ)
      ∧ Real.log (3349 : ℕ) ≤ ((202910427/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3350 :
    ((405835781/50000000 : ℚ) : ℝ) ≤ Real.log (3350 : ℕ)
      ∧ Real.log (3350 : ℕ) ≤ ((811671563/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3351 :
    ((25365669/3125000 : ℚ) : ℝ) ≤ Real.log (3351 : ℕ)
      ∧ Real.log (3351 : ℕ) ≤ ((811701409/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3352 :
    ((405865623/50000000 : ℚ) : ℝ) ≤ Real.log (3352 : ℕ)
      ∧ Real.log (3352 : ℕ) ≤ ((811731247/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3353 :
    ((405880537/50000000 : ℚ) : ℝ) ≤ Real.log (3353 : ℕ)
      ∧ Real.log (3353 : ℕ) ≤ ((32470443/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3354 :
    ((405895447/50000000 : ℚ) : ℝ) ≤ Real.log (3354 : ℕ)
      ∧ Real.log (3354 : ℕ) ≤ ((162358179/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3355 :
    ((25369397/3125000 : ℚ) : ℝ) ≤ Real.log (3355 : ℕ)
      ∧ Real.log (3355 : ℕ) ≤ ((162364141/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3356 :
    ((405925253/50000000 : ℚ) : ℝ) ≤ Real.log (3356 : ℕ)
      ∧ Real.log (3356 : ℕ) ≤ ((811850507/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3357 :
    ((811880299/100000000 : ℚ) : ℝ) ≤ Real.log (3357 : ℕ)
      ∧ Real.log (3357 : ℕ) ≤ ((8118803/1000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3358 :
    ((811910083/100000000 : ℚ) : ℝ) ≤ Real.log (3358 : ℕ)
      ∧ Real.log (3358 : ℕ) ≤ ((202977521/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3359 :
    ((811939857/100000000 : ℚ) : ℝ) ≤ Real.log (3359 : ℕ)
      ∧ Real.log (3359 : ℕ) ≤ ((40596993/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3360 :
    ((6495757/800000 : ℚ) : ℝ) ≤ Real.log (3360 : ℕ)
      ∧ Real.log (3360 : ℕ) ≤ ((405984813/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3361 :
    ((405999691/50000000 : ℚ) : ℝ) ≤ Real.log (3361 : ℕ)
      ∧ Real.log (3361 : ℕ) ≤ ((811999383/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3362 :
    ((812029131/100000000 : ℚ) : ℝ) ≤ Real.log (3362 : ℕ)
      ∧ Real.log (3362 : ℕ) ≤ ((203007283/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3363 :
    ((812058871/100000000 : ℚ) : ℝ) ≤ Real.log (3363 : ℕ)
      ∧ Real.log (3363 : ℕ) ≤ ((101507359/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3364 :
    ((406044301/50000000 : ℚ) : ℝ) ≤ Real.log (3364 : ℕ)
      ∧ Real.log (3364 : ℕ) ≤ ((812088603/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3365 :
    ((203029581/25000000 : ℚ) : ℝ) ≤ Real.log (3365 : ℕ)
      ∧ Real.log (3365 : ℕ) ≤ ((32484733/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3366 :
    ((812148037/100000000 : ℚ) : ℝ) ≤ Real.log (3366 : ℕ)
      ∧ Real.log (3366 : ℕ) ≤ ((406074019/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3367 :
    ((812177741/100000000 : ℚ) : ℝ) ≤ Real.log (3367 : ℕ)
      ∧ Real.log (3367 : ℕ) ≤ ((406088871/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3368 :
    ((812207437/100000000 : ℚ) : ℝ) ≤ Real.log (3368 : ℕ)
      ∧ Real.log (3368 : ℕ) ≤ ((406103719/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3369 :
    ((203059281/25000000 : ℚ) : ℝ) ≤ Real.log (3369 : ℕ)
      ∧ Real.log (3369 : ℕ) ≤ ((6497897/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3370 :
    ((406133401/50000000 : ℚ) : ℝ) ≤ Real.log (3370 : ℕ)
      ∧ Real.log (3370 : ℕ) ≤ ((812266803/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3371 :
    ((812296471/100000000 : ℚ) : ℝ) ≤ Real.log (3371 : ℕ)
      ∧ Real.log (3371 : ℕ) ≤ ((101537059/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3372 :
    ((812326131/100000000 : ℚ) : ℝ) ≤ Real.log (3372 : ℕ)
      ∧ Real.log (3372 : ℕ) ≤ ((203081533/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3373 :
    ((812355783/100000000 : ℚ) : ℝ) ≤ Real.log (3373 : ℕ)
      ∧ Real.log (3373 : ℕ) ≤ ((101544473/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3374 :
    ((406192713/50000000 : ℚ) : ℝ) ≤ Real.log (3374 : ℕ)
      ∧ Real.log (3374 : ℕ) ≤ ((812385427/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3375 :
    ((40620753/5000000 : ℚ) : ℝ) ≤ Real.log (3375 : ℕ)
      ∧ Real.log (3375 : ℕ) ≤ ((812415061/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3376 :
    ((162488937/20000000 : ℚ) : ℝ) ≤ Real.log (3376 : ℕ)
      ∧ Real.log (3376 : ℕ) ≤ ((406222343/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3377 :
    ((812474301/100000000 : ℚ) : ℝ) ≤ Real.log (3377 : ℕ)
      ∧ Real.log (3377 : ℕ) ≤ ((12694911/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3378 :
    ((812503909/100000000 : ℚ) : ℝ) ≤ Real.log (3378 : ℕ)
      ∧ Real.log (3378 : ℕ) ≤ ((81250391/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3379 :
    ((203133377/25000000 : ℚ) : ℝ) ≤ Real.log (3379 : ℕ)
      ∧ Real.log (3379 : ℕ) ≤ ((812533509/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3380 :
    ((406281549/50000000 : ℚ) : ℝ) ≤ Real.log (3380 : ℕ)
      ∧ Real.log (3380 : ℕ) ≤ ((812563099/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3381 :
    ((20314817/2500000 : ℚ) : ℝ) ≤ Real.log (3381 : ℕ)
      ∧ Real.log (3381 : ℕ) ≤ ((812592681/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3382 :
    ((203155563/25000000 : ℚ) : ℝ) ≤ Real.log (3382 : ℕ)
      ∧ Real.log (3382 : ℕ) ≤ ((812622253/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3383 :
    ((101581477/12500000 : ℚ) : ℝ) ≤ Real.log (3383 : ℕ)
      ∧ Real.log (3383 : ℕ) ≤ ((812651817/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3384 :
    ((203170343/25000000 : ℚ) : ℝ) ≤ Real.log (3384 : ℕ)
      ∧ Real.log (3384 : ℕ) ≤ ((812681373/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3385 :
    ((406355459/50000000 : ℚ) : ℝ) ≤ Real.log (3385 : ℕ)
      ∧ Real.log (3385 : ℕ) ≤ ((812710919/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3386 :
    ((101592557/12500000 : ℚ) : ℝ) ≤ Real.log (3386 : ℕ)
      ∧ Real.log (3386 : ℕ) ≤ ((812740457/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3387 :
    ((162553997/20000000 : ℚ) : ℝ) ≤ Real.log (3387 : ℕ)
      ∧ Real.log (3387 : ℕ) ≤ ((406384993/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3388 :
    ((162559901/20000000 : ℚ) : ℝ) ≤ Real.log (3388 : ℕ)
      ∧ Real.log (3388 : ℕ) ≤ ((406399753/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3389 :
    ((812829017/100000000 : ℚ) : ℝ) ≤ Real.log (3389 : ℕ)
      ∧ Real.log (3389 : ℕ) ≤ ((406414509/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3390 :
    ((812858519/100000000 : ℚ) : ℝ) ≤ Real.log (3390 : ℕ)
      ∧ Real.log (3390 : ℕ) ≤ ((406429261/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3391 :
    ((406444007/50000000 : ℚ) : ℝ) ≤ Real.log (3391 : ℕ)
      ∧ Real.log (3391 : ℕ) ≤ ((162577603/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3392 :
    ((812917499/100000000 : ℚ) : ℝ) ≤ Real.log (3392 : ℕ)
      ∧ Real.log (3392 : ℕ) ≤ ((325167/40000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3393 :
    ((25404593/3125000 : ℚ) : ℝ) ≤ Real.log (3393 : ℕ)
      ∧ Real.log (3393 : ℕ) ≤ ((812946977/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3394 :
    ((203244111/25000000 : ℚ) : ℝ) ≤ Real.log (3394 : ℕ)
      ∧ Real.log (3394 : ℕ) ≤ ((162595289/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3395 :
    ((406502951/50000000 : ℚ) : ℝ) ≤ Real.log (3395 : ℕ)
      ∧ Real.log (3395 : ℕ) ≤ ((162601181/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3396 :
    ((406517677/50000000 : ℚ) : ℝ) ≤ Real.log (3396 : ℕ)
      ∧ Real.log (3396 : ℕ) ≤ ((162607071/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3397 :
    ((203266199/25000000 : ℚ) : ℝ) ≤ Real.log (3397 : ℕ)
      ∧ Real.log (3397 : ℕ) ≤ ((813064797/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3398 :
    ((81309423/10000000 : ℚ) : ℝ) ≤ Real.log (3398 : ℕ)
      ∧ Real.log (3398 : ℕ) ≤ ((813094231/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3399 :
    ((813123653/100000000 : ℚ) : ℝ) ≤ Real.log (3399 : ℕ)
      ∧ Real.log (3399 : ℕ) ≤ ((101640457/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3400 :
    ((813153071/100000000 : ℚ) : ℝ) ≤ Real.log (3400 : ℕ)
      ∧ Real.log (3400 : ℕ) ≤ ((50822067/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3401 :
    ((406591239/50000000 : ℚ) : ℝ) ≤ Real.log (3401 : ℕ)
      ∧ Real.log (3401 : ℕ) ≤ ((813182479/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3402 :
    ((813211877/100000000 : ℚ) : ℝ) ≤ Real.log (3402 : ℕ)
      ∧ Real.log (3402 : ℕ) ≤ ((406605939/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3403 :
    ((813241267/100000000 : ℚ) : ℝ) ≤ Real.log (3403 : ℕ)
      ∧ Real.log (3403 : ℕ) ≤ ((203310317/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3404 :
    ((813270647/100000000 : ℚ) : ℝ) ≤ Real.log (3404 : ℕ)
      ∧ Real.log (3404 : ℕ) ≤ ((16265413/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3405 :
    ((813300021/100000000 : ℚ) : ℝ) ≤ Real.log (3405 : ℕ)
      ∧ Real.log (3405 : ℕ) ≤ ((406650011/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3406 :
    ((406664693/50000000 : ℚ) : ℝ) ≤ Real.log (3406 : ℕ)
      ∧ Real.log (3406 : ℕ) ≤ ((813329387/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3407 :
    ((813358741/100000000 : ℚ) : ℝ) ≤ Real.log (3407 : ℕ)
      ∧ Real.log (3407 : ℕ) ≤ ((406679371/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3408 :
    ((101673511/12500000 : ℚ) : ℝ) ≤ Real.log (3408 : ℕ)
      ∧ Real.log (3408 : ℕ) ≤ ((813388089/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3409 :
    ((813417427/100000000 : ℚ) : ℝ) ≤ Real.log (3409 : ℕ)
      ∧ Real.log (3409 : ℕ) ≤ ((203354357/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3410 :
    ((203361689/25000000 : ℚ) : ℝ) ≤ Real.log (3410 : ℕ)
      ∧ Real.log (3410 : ℕ) ≤ ((813446759/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3411 :
    ((406738039/50000000 : ℚ) : ℝ) ≤ Real.log (3411 : ℕ)
      ∧ Real.log (3411 : ℕ) ≤ ((813476079/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3412 :
    ((81350539/10000000 : ℚ) : ℝ) ≤ Real.log (3412 : ℕ)
      ∧ Real.log (3412 : ℕ) ≤ ((813505391/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3413 :
    ((406767347/50000000 : ℚ) : ℝ) ≤ Real.log (3413 : ℕ)
      ∧ Real.log (3413 : ℕ) ≤ ((162706939/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3414 :
    ((81356399/10000000 : ℚ) : ℝ) ≤ Real.log (3414 : ℕ)
      ∧ Real.log (3414 : ℕ) ≤ ((813563991/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3415 :
    ((813593277/100000000 : ℚ) : ℝ) ≤ Real.log (3415 : ℕ)
      ∧ Real.log (3415 : ℕ) ≤ ((406796639/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3416 :
    ((162724511/20000000 : ℚ) : ℝ) ≤ Real.log (3416 : ℕ)
      ∧ Real.log (3416 : ℕ) ≤ ((203405639/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3417 :
    ((32546073/4000000 : ℚ) : ℝ) ≤ Real.log (3417 : ℕ)
      ∧ Real.log (3417 : ℕ) ≤ ((406825913/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3418 :
    ((406840543/50000000 : ℚ) : ℝ) ≤ Real.log (3418 : ℕ)
      ∧ Real.log (3418 : ℕ) ≤ ((813681087/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3419 :
    ((813710337/100000000 : ℚ) : ℝ) ≤ Real.log (3419 : ℕ)
      ∧ Real.log (3419 : ℕ) ≤ ((40685517/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3420 :
    ((406869791/50000000 : ℚ) : ℝ) ≤ Real.log (3420 : ℕ)
      ∧ Real.log (3420 : ℕ) ≤ ((162747917/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3421 :
    ((406884409/50000000 : ℚ) : ℝ) ≤ Real.log (3421 : ℕ)
      ∧ Real.log (3421 : ℕ) ≤ ((813768819/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3422 :
    ((162759609/20000000 : ℚ) : ℝ) ≤ Real.log (3422 : ℕ)
      ∧ Real.log (3422 : ℕ) ≤ ((406899023/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3423 :
    ((813827263/100000000 : ℚ) : ℝ) ≤ Real.log (3423 : ℕ)
      ∧ Real.log (3423 : ℕ) ≤ ((12716051/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3424 :
    ((813856473/100000000 : ℚ) : ℝ) ≤ Real.log (3424 : ℕ)
      ∧ Real.log (3424 : ℕ) ≤ ((406928237/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3425 :
    ((32555427/4000000 : ℚ) : ℝ) ≤ Real.log (3425 : ℕ)
      ∧ Real.log (3425 : ℕ) ≤ ((203471419/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3426 :
    ((813914867/100000000 : ℚ) : ℝ) ≤ Real.log (3426 : ℕ)
      ∧ Real.log (3426 : ℕ) ≤ ((203478717/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3427 :
    ((203486013/25000000 : ℚ) : ℝ) ≤ Real.log (3427 : ℕ)
      ∧ Real.log (3427 : ℕ) ≤ ((813944053/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3428 :
    ((406986613/50000000 : ℚ) : ℝ) ≤ Real.log (3428 : ℕ)
      ∧ Real.log (3428 : ℕ) ≤ ((813973229/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3429 :
    ((162800479/20000000 : ℚ) : ℝ) ≤ Real.log (3429 : ℕ)
      ∧ Real.log (3429 : ℕ) ≤ ((203500599/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3430 :
    ((814031553/100000000 : ℚ) : ℝ) ≤ Real.log (3430 : ℕ)
      ∧ Real.log (3430 : ℕ) ≤ ((203507889/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3431 :
    ((25439397/3125000 : ℚ) : ℝ) ≤ Real.log (3431 : ℕ)
      ∧ Real.log (3431 : ℕ) ≤ ((162812141/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3432 :
    ((407044923/50000000 : ℚ) : ℝ) ≤ Real.log (3432 : ℕ)
      ∧ Real.log (3432 : ℕ) ≤ ((814089847/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3433 :
    ((814118979/100000000 : ℚ) : ℝ) ≤ Real.log (3433 : ℕ)
      ∧ Real.log (3433 : ℕ) ≤ ((40705949/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3434 :
    ((101768513/12500000 : ℚ) : ℝ) ≤ Real.log (3434 : ℕ)
      ∧ Real.log (3434 : ℕ) ≤ ((162829621/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3435 :
    ((40708861/5000000 : ℚ) : ℝ) ≤ Real.log (3435 : ℕ)
      ∧ Real.log (3435 : ℕ) ≤ ((814177221/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3436 :
    ((101775791/12500000 : ℚ) : ℝ) ≤ Real.log (3436 : ℕ)
      ∧ Real.log (3436 : ℕ) ≤ ((814206329/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3437 :
    ((814235427/100000000 : ℚ) : ℝ) ≤ Real.log (3437 : ℕ)
      ∧ Real.log (3437 : ℕ) ≤ ((203558857/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3438 :
    ((407132259/50000000 : ℚ) : ℝ) ≤ Real.log (3438 : ℕ)
      ∧ Real.log (3438 : ℕ) ≤ ((814264519/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3439 :
    ((814293601/100000000 : ℚ) : ℝ) ≤ Real.log (3439 : ℕ)
      ∧ Real.log (3439 : ℕ) ≤ ((407146801/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3440 :
    ((407161337/50000000 : ℚ) : ℝ) ≤ Real.log (3440 : ℕ)
      ∧ Real.log (3440 : ℕ) ≤ ((814322677/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3441 :
    ((40717587/5000000 : ℚ) : ℝ) ≤ Real.log (3441 : ℕ)
      ∧ Real.log (3441 : ℕ) ≤ ((814351741/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3442 :
    ((814380797/100000000 : ℚ) : ℝ) ≤ Real.log (3442 : ℕ)
      ∧ Real.log (3442 : ℕ) ≤ ((407190399/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3443 :
    ((407204923/50000000 : ℚ) : ℝ) ≤ Real.log (3443 : ℕ)
      ∧ Real.log (3443 : ℕ) ≤ ((814409847/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3444 :
    ((407219443/50000000 : ℚ) : ℝ) ≤ Real.log (3444 : ℕ)
      ∧ Real.log (3444 : ℕ) ≤ ((814438887/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3445 :
    ((407233959/50000000 : ℚ) : ℝ) ≤ Real.log (3445 : ℕ)
      ∧ Real.log (3445 : ℕ) ≤ ((814467919/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3446 :
    ((814496941/100000000 : ℚ) : ℝ) ≤ Real.log (3446 : ℕ)
      ∧ Real.log (3446 : ℕ) ≤ ((407248471/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3447 :
    ((203631489/25000000 : ℚ) : ℝ) ≤ Real.log (3447 : ℕ)
      ∧ Real.log (3447 : ℕ) ≤ ((814525957/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3448 :
    ((814554963/100000000 : ℚ) : ℝ) ≤ Real.log (3448 : ℕ)
      ∧ Real.log (3448 : ℕ) ≤ ((203638741/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3449 :
    ((814583961/100000000 : ℚ) : ℝ) ≤ Real.log (3449 : ℕ)
      ∧ Real.log (3449 : ℕ) ≤ ((407291981/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3450 :
    ((16292259/2000000 : ℚ) : ℝ) ≤ Real.log (3450 : ℕ)
      ∧ Real.log (3450 : ℕ) ≤ ((814612953/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3451 :
    ((203660483/25000000 : ℚ) : ℝ) ≤ Real.log (3451 : ℕ)
      ∧ Real.log (3451 : ℕ) ≤ ((814641933/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3452 :
    ((162934181/20000000 : ℚ) : ℝ) ≤ Real.log (3452 : ℕ)
      ∧ Real.log (3452 : ℕ) ≤ ((407335453/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3453 :
    ((814699869/100000000 : ℚ) : ℝ) ≤ Real.log (3453 : ℕ)
      ∧ Real.log (3453 : ℕ) ≤ ((81469987/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3454 :
    ((32589153/4000000 : ℚ) : ℝ) ≤ Real.log (3454 : ℕ)
      ∧ Real.log (3454 : ℕ) ≤ ((407364413/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3455 :
    ((814757773/100000000 : ℚ) : ℝ) ≤ Real.log (3455 : ℕ)
      ∧ Real.log (3455 : ℕ) ≤ ((407378887/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3456 :
    ((814786711/100000000 : ℚ) : ℝ) ≤ Real.log (3456 : ℕ)
      ∧ Real.log (3456 : ℕ) ≤ ((407393357/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3457 :
    ((407407821/50000000 : ℚ) : ℝ) ≤ Real.log (3457 : ℕ)
      ∧ Real.log (3457 : ℕ) ≤ ((162963129/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3458 :
    ((407422283/50000000 : ℚ) : ℝ) ≤ Real.log (3458 : ℕ)
      ∧ Real.log (3458 : ℕ) ≤ ((814844567/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3459 :
    ((20371837/2500000 : ℚ) : ℝ) ≤ Real.log (3459 : ℕ)
      ∧ Real.log (3459 : ℕ) ≤ ((814873481/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3460 :
    ((407451193/50000000 : ℚ) : ℝ) ≤ Real.log (3460 : ℕ)
      ∧ Real.log (3460 : ℕ) ≤ ((814902387/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3461 :
    ((203732821/25000000 : ℚ) : ℝ) ≤ Real.log (3461 : ℕ)
      ∧ Real.log (3461 : ℕ) ≤ ((162986257/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3462 :
    ((814960173/100000000 : ℚ) : ℝ) ≤ Real.log (3462 : ℕ)
      ∧ Real.log (3462 : ℕ) ≤ ((407480087/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3463 :
    ((407494527/50000000 : ℚ) : ℝ) ≤ Real.log (3463 : ℕ)
      ∧ Real.log (3463 : ℕ) ≤ ((162997811/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3464 :
    ((32600717/4000000 : ℚ) : ℝ) ≤ Real.log (3464 : ℕ)
      ∧ Real.log (3464 : ℕ) ≤ ((101877241/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3465 :
    ((815046791/100000000 : ℚ) : ℝ) ≤ Real.log (3465 : ℕ)
      ∧ Real.log (3465 : ℕ) ≤ ((101880849/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3466 :
    ((407537823/50000000 : ℚ) : ℝ) ≤ Real.log (3466 : ℕ)
      ∧ Real.log (3466 : ℕ) ≤ ((815075649/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3467 :
    ((407552247/50000000 : ℚ) : ℝ) ≤ Real.log (3467 : ℕ)
      ∧ Real.log (3467 : ℕ) ≤ ((163020899/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3468 :
    ((815133333/100000000 : ℚ) : ℝ) ≤ Real.log (3468 : ℕ)
      ∧ Real.log (3468 : ℕ) ≤ ((407566667/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3469 :
    ((203790541/25000000 : ℚ) : ℝ) ≤ Real.log (3469 : ℕ)
      ∧ Real.log (3469 : ℕ) ≤ ((163032433/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3470 :
    ((815190987/100000000 : ℚ) : ℝ) ≤ Real.log (3470 : ℕ)
      ∧ Real.log (3470 : ℕ) ≤ ((203797747/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3471 :
    ((815219801/100000000 : ℚ) : ℝ) ≤ Real.log (3471 : ℕ)
      ∧ Real.log (3471 : ℕ) ≤ ((407609901/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3472 :
    ((815248607/100000000 : ℚ) : ℝ) ≤ Real.log (3472 : ℕ)
      ∧ Real.log (3472 : ℕ) ≤ ((25476519/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3473 :
    ((163055481/20000000 : ℚ) : ℝ) ≤ Real.log (3473 : ℕ)
      ∧ Real.log (3473 : ℕ) ≤ ((407638703/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3474 :
    ((407653097/50000000 : ℚ) : ℝ) ≤ Real.log (3474 : ℕ)
      ∧ Real.log (3474 : ℕ) ≤ ((163061239/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3475 :
    ((32613399/4000000 : ℚ) : ℝ) ≤ Real.log (3475 : ℕ)
      ∧ Real.log (3475 : ℕ) ≤ ((12739609/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3476 :
    ((203840937/25000000 : ℚ) : ℝ) ≤ Real.log (3476 : ℕ)
      ∧ Real.log (3476 : ℕ) ≤ ((815363749/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3477 :
    ((815392513/100000000 : ℚ) : ℝ) ≤ Real.log (3477 : ℕ)
      ∧ Real.log (3477 : ℕ) ≤ ((407696257/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3478 :
    ((815421269/100000000 : ℚ) : ℝ) ≤ Real.log (3478 : ℕ)
      ∧ Real.log (3478 : ℕ) ≤ ((81542127/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3479 :
    ((815450017/100000000 : ℚ) : ℝ) ≤ Real.log (3479 : ℕ)
      ∧ Real.log (3479 : ℕ) ≤ ((407725009/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3480 :
    ((815478757/100000000 : ℚ) : ℝ) ≤ Real.log (3480 : ℕ)
      ∧ Real.log (3480 : ℕ) ≤ ((407739379/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3481 :
    ((25484609/3125000 : ℚ) : ℝ) ≤ Real.log (3481 : ℕ)
      ∧ Real.log (3481 : ℕ) ≤ ((815507489/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3482 :
    ((815536211/100000000 : ℚ) : ℝ) ≤ Real.log (3482 : ℕ)
      ∧ Real.log (3482 : ℕ) ≤ ((407768107/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3483 :
    ((407782463/50000000 : ℚ) : ℝ) ≤ Real.log (3483 : ℕ)
      ∧ Real.log (3483 : ℕ) ≤ ((815564929/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3484 :
    ((815593633/100000000 : ℚ) : ℝ) ≤ Real.log (3484 : ℕ)
      ∧ Real.log (3484 : ℕ) ≤ ((407796817/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3485 :
    ((203905583/25000000 : ℚ) : ℝ) ≤ Real.log (3485 : ℕ)
      ∧ Real.log (3485 : ℕ) ≤ ((815622333/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3486 :
    ((407825511/50000000 : ℚ) : ℝ) ≤ Real.log (3486 : ℕ)
      ∧ Real.log (3486 : ℕ) ≤ ((815651023/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3487 :
    ((101959963/12500000 : ℚ) : ℝ) ≤ Real.log (3487 : ℕ)
      ∧ Real.log (3487 : ℕ) ≤ ((163135941/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3488 :
    ((407854189/50000000 : ℚ) : ℝ) ≤ Real.log (3488 : ℕ)
      ∧ Real.log (3488 : ℕ) ≤ ((815708379/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3489 :
    ((203934261/25000000 : ℚ) : ℝ) ≤ Real.log (3489 : ℕ)
      ∧ Real.log (3489 : ℕ) ≤ ((163147409/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3490 :
    ((815765701/100000000 : ℚ) : ℝ) ≤ Real.log (3490 : ℕ)
      ∧ Real.log (3490 : ℕ) ≤ ((407882851/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3491 :
    ((16315887/2000000 : ℚ) : ℝ) ≤ Real.log (3491 : ℕ)
      ∧ Real.log (3491 : ℕ) ≤ ((815794351/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3492 :
    ((815822991/100000000 : ℚ) : ℝ) ≤ Real.log (3492 : ℕ)
      ∧ Real.log (3492 : ℕ) ≤ ((50988937/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3493 :
    ((101981453/12500000 : ℚ) : ℝ) ≤ Real.log (3493 : ℕ)
      ∧ Real.log (3493 : ℕ) ≤ ((6526813/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3494 :
    ((815880249/100000000 : ℚ) : ℝ) ≤ Real.log (3494 : ℕ)
      ∧ Real.log (3494 : ℕ) ≤ ((3263521/400000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3495 :
    ((163181773/20000000 : ℚ) : ℝ) ≤ Real.log (3495 : ℕ)
      ∧ Real.log (3495 : ℕ) ≤ ((407954433/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3496 :
    ((815937473/100000000 : ℚ) : ℝ) ≤ Real.log (3496 : ℕ)
      ∧ Real.log (3496 : ℕ) ≤ ((407968737/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3497 :
    ((815966073/100000000 : ℚ) : ℝ) ≤ Real.log (3497 : ℕ)
      ∧ Real.log (3497 : ℕ) ≤ ((407983037/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3498 :
    ((163198933/20000000 : ℚ) : ℝ) ≤ Real.log (3498 : ℕ)
      ∧ Real.log (3498 : ℕ) ≤ ((407997333/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3499 :
    ((816023249/100000000 : ℚ) : ℝ) ≤ Real.log (3499 : ℕ)
      ∧ Real.log (3499 : ℕ) ≤ ((3264093/400000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3500 :
    ((51003239/6250000 : ℚ) : ℝ) ≤ Real.log (3500 : ℕ)
      ∧ Real.log (3500 : ℕ) ≤ ((32642073/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3501 :
    ((102010049/12500000 : ℚ) : ℝ) ≤ Real.log (3501 : ℕ)
      ∧ Real.log (3501 : ℕ) ≤ ((816080393/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3502 :
    ((816108951/100000000 : ℚ) : ℝ) ≤ Real.log (3502 : ℕ)
      ∧ Real.log (3502 : ℕ) ≤ ((102013619/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3503 :
    ((408068751/50000000 : ℚ) : ℝ) ≤ Real.log (3503 : ℕ)
      ∧ Real.log (3503 : ℕ) ≤ ((816137503/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3504 :
    ((163233209/20000000 : ℚ) : ℝ) ≤ Real.log (3504 : ℕ)
      ∧ Real.log (3504 : ℕ) ≤ ((408083023/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3505 :
    ((816194579/100000000 : ℚ) : ℝ) ≤ Real.log (3505 : ℕ)
      ∧ Real.log (3505 : ℕ) ≤ ((40809729/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3506 :
    ((408111553/50000000 : ℚ) : ℝ) ≤ Real.log (3506 : ℕ)
      ∧ Real.log (3506 : ℕ) ≤ ((816223107/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3507 :
    ((102031453/12500000 : ℚ) : ℝ) ≤ Real.log (3507 : ℕ)
      ∧ Real.log (3507 : ℕ) ≤ ((816251627/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3508 :
    ((163256027/20000000 : ℚ) : ℝ) ≤ Real.log (3508 : ℕ)
      ∧ Real.log (3508 : ℕ) ≤ ((102035017/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3509 :
    ((816308637/100000000 : ℚ) : ℝ) ≤ Real.log (3509 : ℕ)
      ∧ Real.log (3509 : ℕ) ≤ ((408154319/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3510 :
    ((816337131/100000000 : ℚ) : ℝ) ≤ Real.log (3510 : ℕ)
      ∧ Real.log (3510 : ℕ) ≤ ((204084283/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3511 :
    ((816365617/100000000 : ℚ) : ℝ) ≤ Real.log (3511 : ℕ)
      ∧ Real.log (3511 : ℕ) ≤ ((408182809/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3512 :
    ((163278819/20000000 : ℚ) : ℝ) ≤ Real.log (3512 : ℕ)
      ∧ Real.log (3512 : ℕ) ≤ ((51024631/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3513 :
    ((163284513/20000000 : ℚ) : ℝ) ≤ Real.log (3513 : ℕ)
      ∧ Real.log (3513 : ℕ) ≤ ((408211283/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3514 :
    ((408225513/50000000 : ℚ) : ℝ) ≤ Real.log (3514 : ℕ)
      ∧ Real.log (3514 : ℕ) ≤ ((816451027/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3515 :
    ((20411987/2500000 : ℚ) : ℝ) ≤ Real.log (3515 : ℕ)
      ∧ Real.log (3515 : ℕ) ≤ ((816479481/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3516 :
    ((32660317/4000000 : ℚ) : ℝ) ≤ Real.log (3516 : ℕ)
      ∧ Real.log (3516 : ℕ) ≤ ((408253963/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3517 :
    ((816536363/100000000 : ℚ) : ℝ) ≤ Real.log (3517 : ℕ)
      ∧ Real.log (3517 : ℕ) ≤ ((204134091/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3518 :
    ((102070599/12500000 : ℚ) : ℝ) ≤ Real.log (3518 : ℕ)
      ∧ Real.log (3518 : ℕ) ≤ ((816564793/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3519 :
    ((816593213/100000000 : ℚ) : ℝ) ≤ Real.log (3519 : ℕ)
      ∧ Real.log (3519 : ℕ) ≤ ((408296607/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3520 :
    ((408310813/50000000 : ℚ) : ℝ) ≤ Real.log (3520 : ℕ)
      ∧ Real.log (3520 : ℕ) ≤ ((816621627/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3521 :
    ((816650031/100000000 : ℚ) : ℝ) ≤ Real.log (3521 : ℕ)
      ∧ Real.log (3521 : ℕ) ≤ ((51040627/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3522 :
    ((204169607/25000000 : ℚ) : ℝ) ≤ Real.log (3522 : ℕ)
      ∧ Real.log (3522 : ℕ) ≤ ((816678429/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3523 :
    ((816706817/100000000 : ℚ) : ℝ) ≤ Real.log (3523 : ℕ)
      ∧ Real.log (3523 : ℕ) ≤ ((408353409/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3524 :
    ((408367599/50000000 : ℚ) : ℝ) ≤ Real.log (3524 : ℕ)
      ∧ Real.log (3524 : ℕ) ≤ ((816735199/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3525 :
    ((816763571/100000000 : ℚ) : ℝ) ≤ Real.log (3525 : ℕ)
      ∧ Real.log (3525 : ℕ) ≤ ((204190893/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3526 :
    ((6381187/781250 : ℚ) : ℝ) ≤ Real.log (3526 : ℕ)
      ∧ Real.log (3526 : ℕ) ≤ ((816791937/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3527 :
    ((204205073/25000000 : ℚ) : ℝ) ≤ Real.log (3527 : ℕ)
      ∧ Real.log (3527 : ℕ) ≤ ((163364059/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3528 :
    ((816848641/100000000 : ℚ) : ℝ) ≤ Real.log (3528 : ℕ)
      ∧ Real.log (3528 : ℕ) ≤ ((408424321/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3529 :
    ((408438491/50000000 : ℚ) : ℝ) ≤ Real.log (3529 : ℕ)
      ∧ Real.log (3529 : ℕ) ≤ ((816876983/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3530 :
    ((816905313/100000000 : ℚ) : ℝ) ≤ Real.log (3530 : ℕ)
      ∧ Real.log (3530 : ℕ) ≤ ((204226329/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3531 :
    ((816933639/100000000 : ℚ) : ℝ) ≤ Real.log (3531 : ℕ)
      ∧ Real.log (3531 : ℕ) ≤ ((20423341/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3532 :
    ((204240489/25000000 : ℚ) : ℝ) ≤ Real.log (3532 : ℕ)
      ∧ Real.log (3532 : ℕ) ≤ ((816961957/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3533 :
    ((102123783/12500000 : ℚ) : ℝ) ≤ Real.log (3533 : ℕ)
      ∧ Real.log (3533 : ℕ) ≤ ((163398053/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3534 :
    ((163403713/20000000 : ℚ) : ℝ) ≤ Real.log (3534 : ℕ)
      ∧ Real.log (3534 : ℕ) ≤ ((408509283/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3535 :
    ((817046857/100000000 : ℚ) : ℝ) ≤ Real.log (3535 : ℕ)
      ∧ Real.log (3535 : ℕ) ≤ ((408523429/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3536 :
    ((408537571/50000000 : ℚ) : ℝ) ≤ Real.log (3536 : ℕ)
      ∧ Real.log (3536 : ℕ) ≤ ((817075143/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3537 :
    ((408551709/50000000 : ℚ) : ℝ) ≤ Real.log (3537 : ℕ)
      ∧ Real.log (3537 : ℕ) ≤ ((817103419/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3538 :
    ((817131687/100000000 : ℚ) : ℝ) ≤ Real.log (3538 : ℕ)
      ∧ Real.log (3538 : ℕ) ≤ ((102141461/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3539 :
    ((817159947/100000000 : ℚ) : ℝ) ≤ Real.log (3539 : ℕ)
      ∧ Real.log (3539 : ℕ) ≤ ((16343199/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3540 :
    ((4085941/500000 : ℚ) : ℝ) ≤ Real.log (3540 : ℕ)
      ∧ Real.log (3540 : ℕ) ≤ ((817188201/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3541 :
    ((163443289/20000000 : ℚ) : ℝ) ≤ Real.log (3541 : ℕ)
      ∧ Real.log (3541 : ℕ) ≤ ((408608223/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3542 :
    ((817244681/100000000 : ℚ) : ℝ) ≤ Real.log (3542 : ℕ)
      ∧ Real.log (3542 : ℕ) ≤ ((408622341/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3543 :
    ((81727291/10000000 : ℚ) : ℝ) ≤ Real.log (3543 : ℕ)
      ∧ Real.log (3543 : ℕ) ≤ ((817272911/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3544 :
    ((817301131/100000000 : ℚ) : ℝ) ≤ Real.log (3544 : ℕ)
      ∧ Real.log (3544 : ℕ) ≤ ((204325283/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3545 :
    ((817329343/100000000 : ℚ) : ℝ) ≤ Real.log (3545 : ℕ)
      ∧ Real.log (3545 : ℕ) ≤ ((12770771/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3546 :
    ((204339387/25000000 : ℚ) : ℝ) ≤ Real.log (3546 : ℕ)
      ∧ Real.log (3546 : ℕ) ≤ ((817357549/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3547 :
    ((163477149/20000000 : ℚ) : ℝ) ≤ Real.log (3547 : ℕ)
      ∧ Real.log (3547 : ℕ) ≤ ((408692873/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3548 :
    ((408706967/50000000 : ℚ) : ℝ) ≤ Real.log (3548 : ℕ)
      ∧ Real.log (3548 : ℕ) ≤ ((163482787/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3549 :
    ((163488423/20000000 : ℚ) : ℝ) ≤ Real.log (3549 : ℕ)
      ∧ Real.log (3549 : ℕ) ≤ ((204360529/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3550 :
    ((51091893/6250000 : ℚ) : ℝ) ≤ Real.log (3550 : ℕ)
      ∧ Real.log (3550 : ℕ) ≤ ((817470289/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3551 :
    ((817498453/100000000 : ℚ) : ℝ) ≤ Real.log (3551 : ℕ)
      ∧ Real.log (3551 : ℕ) ≤ ((408749227/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3552 :
    ((81752661/10000000 : ℚ) : ℝ) ≤ Real.log (3552 : ℕ)
      ∧ Real.log (3552 : ℕ) ≤ ((817526611/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3553 :
    ((817554759/100000000 : ℚ) : ℝ) ≤ Real.log (3553 : ℕ)
      ∧ Real.log (3553 : ℕ) ≤ ((20438869/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3554 :
    ((8175829/1000000 : ℚ) : ℝ) ≤ Real.log (3554 : ℕ)
      ∧ Real.log (3554 : ℕ) ≤ ((817582901/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3555 :
    ((408805517/50000000 : ℚ) : ℝ) ≤ Real.log (3555 : ℕ)
      ∧ Real.log (3555 : ℕ) ≤ ((163522207/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3556 :
    ((817639159/100000000 : ℚ) : ℝ) ≤ Real.log (3556 : ℕ)
      ∧ Real.log (3556 : ℕ) ≤ ((20440979/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3557 :
    ((817667277/100000000 : ℚ) : ℝ) ≤ Real.log (3557 : ℕ)
      ∧ Real.log (3557 : ℕ) ≤ ((408833639/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3558 :
    ((408847693/50000000 : ℚ) : ℝ) ≤ Real.log (3558 : ℕ)
      ∧ Real.log (3558 : ℕ) ≤ ((817695387/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3559 :
    ((25553859/3125000 : ℚ) : ℝ) ≤ Real.log (3559 : ℕ)
      ∧ Real.log (3559 : ℕ) ≤ ((817723489/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3560 :
    ((408875791/50000000 : ℚ) : ℝ) ≤ Real.log (3560 : ℕ)
      ∧ Real.log (3560 : ℕ) ≤ ((817751583/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3561 :
    ((204444917/25000000 : ℚ) : ℝ) ≤ Real.log (3561 : ℕ)
      ∧ Real.log (3561 : ℕ) ≤ ((817779669/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3562 :
    ((408903873/50000000 : ℚ) : ℝ) ≤ Real.log (3562 : ℕ)
      ∧ Real.log (3562 : ℕ) ≤ ((817807747/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3563 :
    ((102229477/12500000 : ℚ) : ℝ) ≤ Real.log (3563 : ℕ)
      ∧ Real.log (3563 : ℕ) ≤ ((817835817/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3564 :
    ((408931939/50000000 : ℚ) : ℝ) ≤ Real.log (3564 : ℕ)
      ∧ Real.log (3564 : ℕ) ≤ ((817863879/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3565 :
    ((817891933/100000000 : ℚ) : ℝ) ≤ Real.log (3565 : ℕ)
      ∧ Real.log (3565 : ℕ) ≤ ((408945967/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3566 :
    ((817919979/100000000 : ℚ) : ℝ) ≤ Real.log (3566 : ℕ)
      ∧ Real.log (3566 : ℕ) ≤ ((40895999/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3567 :
    ((408974009/50000000 : ℚ) : ℝ) ≤ Real.log (3567 : ℕ)
      ∧ Real.log (3567 : ℕ) ≤ ((817948019/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3568 :
    ((817976049/100000000 : ℚ) : ℝ) ≤ Real.log (3568 : ℕ)
      ∧ Real.log (3568 : ℕ) ≤ ((16359521/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3569 :
    ((102250509/12500000 : ℚ) : ℝ) ≤ Real.log (3569 : ℕ)
      ∧ Real.log (3569 : ℕ) ≤ ((818004073/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3570 :
    ((818032087/100000000 : ℚ) : ℝ) ≤ Real.log (3570 : ℕ)
      ∧ Real.log (3570 : ℕ) ≤ ((102254011/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3571 :
    ((409030047/50000000 : ℚ) : ℝ) ≤ Real.log (3571 : ℕ)
      ∧ Real.log (3571 : ℕ) ≤ ((163612019/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3572 :
    ((409044047/50000000 : ℚ) : ℝ) ≤ Real.log (3572 : ℕ)
      ∧ Real.log (3572 : ℕ) ≤ ((163617619/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3573 :
    ((163623217/20000000 : ℚ) : ℝ) ≤ Real.log (3573 : ℕ)
      ∧ Real.log (3573 : ℕ) ≤ ((409058043/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3574 :
    ((818144069/100000000 : ℚ) : ℝ) ≤ Real.log (3574 : ℕ)
      ∧ Real.log (3574 : ℕ) ≤ ((81814407/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3575 :
    ((163634409/20000000 : ℚ) : ℝ) ≤ Real.log (3575 : ℕ)
      ∧ Real.log (3575 : ℕ) ≤ ((409086023/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3576 :
    ((818200013/100000000 : ℚ) : ℝ) ≤ Real.log (3576 : ℕ)
      ∧ Real.log (3576 : ℕ) ≤ ((409100007/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3577 :
    ((818227973/100000000 : ℚ) : ℝ) ≤ Real.log (3577 : ℕ)
      ∧ Real.log (3577 : ℕ) ≤ ((409113987/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3578 :
    ((409127963/50000000 : ℚ) : ℝ) ≤ Real.log (3578 : ℕ)
      ∧ Real.log (3578 : ℕ) ≤ ((818255927/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3579 :
    ((818283871/100000000 : ℚ) : ℝ) ≤ Real.log (3579 : ℕ)
      ∧ Real.log (3579 : ℕ) ≤ ((25571371/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3580 :
    ((818311807/100000000 : ℚ) : ℝ) ≤ Real.log (3580 : ℕ)
      ∧ Real.log (3580 : ℕ) ≤ ((6393061/781250 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3581 :
    ((163667947/20000000 : ℚ) : ℝ) ≤ Real.log (3581 : ℕ)
      ∧ Real.log (3581 : ℕ) ≤ ((409169869/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3582 :
    ((409183829/50000000 : ℚ) : ℝ) ≤ Real.log (3582 : ℕ)
      ∧ Real.log (3582 : ℕ) ≤ ((818367659/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3583 :
    ((818395571/100000000 : ℚ) : ℝ) ≤ Real.log (3583 : ℕ)
      ∧ Real.log (3583 : ℕ) ≤ ((204598893/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3584 :
    ((818423477/100000000 : ℚ) : ℝ) ≤ Real.log (3584 : ℕ)
      ∧ Real.log (3584 : ℕ) ≤ ((409211739/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3585 :
    ((6547611/800000 : ℚ) : ℝ) ≤ Real.log (3585 : ℕ)
      ∧ Real.log (3585 : ℕ) ≤ ((51153211/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3586 :
    ((163695853/20000000 : ℚ) : ℝ) ≤ Real.log (3586 : ℕ)
      ∧ Real.log (3586 : ℕ) ≤ ((409239633/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3587 :
    ((818507147/100000000 : ℚ) : ℝ) ≤ Real.log (3587 : ℕ)
      ∧ Real.log (3587 : ℕ) ≤ ((204626787/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3588 :
    ((409267511/50000000 : ℚ) : ℝ) ≤ Real.log (3588 : ℕ)
      ∧ Real.log (3588 : ℕ) ≤ ((818535023/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3589 :
    ((818562889/100000000 : ℚ) : ℝ) ≤ Real.log (3589 : ℕ)
      ∧ Real.log (3589 : ℕ) ≤ ((81856289/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3590 :
    ((204647687/25000000 : ℚ) : ℝ) ≤ Real.log (3590 : ℕ)
      ∧ Real.log (3590 : ℕ) ≤ ((818590749/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3591 :
    ((818618599/100000000 : ℚ) : ℝ) ≤ Real.log (3591 : ℕ)
      ∧ Real.log (3591 : ℕ) ≤ ((4093093/500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3592 :
    ((409323221/50000000 : ℚ) : ℝ) ≤ Real.log (3592 : ℕ)
      ∧ Real.log (3592 : ℕ) ≤ ((818646443/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3593 :
    ((409337139/50000000 : ℚ) : ℝ) ≤ Real.log (3593 : ℕ)
      ∧ Real.log (3593 : ℕ) ≤ ((818674279/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3594 :
    ((409351053/50000000 : ℚ) : ℝ) ≤ Real.log (3594 : ℕ)
      ∧ Real.log (3594 : ℕ) ≤ ((818702107/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3595 :
    ((409364963/50000000 : ℚ) : ℝ) ≤ Real.log (3595 : ℕ)
      ∧ Real.log (3595 : ℕ) ≤ ((818729929/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3596 :
    ((818757739/100000000 : ℚ) : ℝ) ≤ Real.log (3596 : ℕ)
      ∧ Real.log (3596 : ℕ) ≤ ((40937887/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3597 :
    ((102348193/12500000 : ℚ) : ℝ) ≤ Real.log (3597 : ℕ)
      ∧ Real.log (3597 : ℕ) ≤ ((163757109/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3598 :
    ((818813341/100000000 : ℚ) : ℝ) ≤ Real.log (3598 : ℕ)
      ∧ Real.log (3598 : ℕ) ≤ ((409406671/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3599 :
    ((81884113/10000000 : ℚ) : ℝ) ≤ Real.log (3599 : ℕ)
      ∧ Real.log (3599 : ℕ) ≤ ((818841131/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3600 :
    ((51179307/6250000 : ℚ) : ℝ) ≤ Real.log (3600 : ℕ)
      ∧ Real.log (3600 : ℕ) ≤ ((818868913/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3601 :
    ((409448343/50000000 : ℚ) : ℝ) ≤ Real.log (3601 : ℕ)
      ∧ Real.log (3601 : ℕ) ≤ ((818896687/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3602 :
    ((204731113/25000000 : ℚ) : ℝ) ≤ Real.log (3602 : ℕ)
      ∧ Real.log (3602 : ℕ) ≤ ((818924453/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3603 :
    ((818952211/100000000 : ℚ) : ℝ) ≤ Real.log (3603 : ℕ)
      ∧ Real.log (3603 : ℕ) ≤ ((204738053/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3604 :
    ((818979961/100000000 : ℚ) : ℝ) ≤ Real.log (3604 : ℕ)
      ∧ Real.log (3604 : ℕ) ≤ ((409489981/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3605 :
    ((819007703/100000000 : ℚ) : ℝ) ≤ Real.log (3605 : ℕ)
      ∧ Real.log (3605 : ℕ) ≤ ((409503853/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3606 :
    ((10237943/1250000 : ℚ) : ℝ) ≤ Real.log (3606 : ℕ)
      ∧ Real.log (3606 : ℕ) ≤ ((819035441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3607 :
    ((6398931/781250 : ℚ) : ℝ) ≤ Real.log (3607 : ℕ)
      ∧ Real.log (3607 : ℕ) ≤ ((819063169/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3608 :
    ((102386361/12500000 : ℚ) : ℝ) ≤ Real.log (3608 : ℕ)
      ∧ Real.log (3608 : ℕ) ≤ ((819090889/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3609 :
    ((4095593/500000 : ℚ) : ℝ) ≤ Real.log (3609 : ℕ)
      ∧ Real.log (3609 : ℕ) ≤ ((819118601/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3610 :
    ((163829261/20000000 : ℚ) : ℝ) ≤ Real.log (3610 : ℕ)
      ∧ Real.log (3610 : ℕ) ≤ ((409573153/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3611 :
    ((409587001/50000000 : ℚ) : ℝ) ≤ Real.log (3611 : ℕ)
      ∧ Real.log (3611 : ℕ) ≤ ((819174003/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3612 :
    ((819201691/100000000 : ℚ) : ℝ) ≤ Real.log (3612 : ℕ)
      ∧ Real.log (3612 : ℕ) ≤ ((204800423/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3613 :
    ((819229373/100000000 : ℚ) : ℝ) ≤ Real.log (3613 : ℕ)
      ∧ Real.log (3613 : ℕ) ≤ ((409614687/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3614 :
    ((819257047/100000000 : ℚ) : ℝ) ≤ Real.log (3614 : ℕ)
      ∧ Real.log (3614 : ℕ) ≤ ((102407131/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3615 :
    ((819284713/100000000 : ℚ) : ℝ) ≤ Real.log (3615 : ℕ)
      ∧ Real.log (3615 : ℕ) ≤ ((409642357/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3616 :
    ((204828093/25000000 : ℚ) : ℝ) ≤ Real.log (3616 : ℕ)
      ∧ Real.log (3616 : ℕ) ≤ ((819312373/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3617 :
    ((819340023/100000000 : ℚ) : ℝ) ≤ Real.log (3617 : ℕ)
      ∧ Real.log (3617 : ℕ) ≤ ((102417503/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3618 :
    ((409683833/50000000 : ℚ) : ℝ) ≤ Real.log (3618 : ℕ)
      ∧ Real.log (3618 : ℕ) ≤ ((819367667/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3619 :
    ((409697651/50000000 : ℚ) : ℝ) ≤ Real.log (3619 : ℕ)
      ∧ Real.log (3619 : ℕ) ≤ ((819395303/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3620 :
    ((81942293/10000000 : ℚ) : ℝ) ≤ Real.log (3620 : ℕ)
      ∧ Real.log (3620 : ℕ) ≤ ((819422931/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3621 :
    ((819450549/100000000 : ℚ) : ℝ) ≤ Real.log (3621 : ℕ)
      ∧ Real.log (3621 : ℕ) ≤ ((102431319/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3622 :
    ((819478163/100000000 : ℚ) : ℝ) ≤ Real.log (3622 : ℕ)
      ∧ Real.log (3622 : ℕ) ≤ ((204869541/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3623 :
    ((819505769/100000000 : ℚ) : ℝ) ≤ Real.log (3623 : ℕ)
      ∧ Real.log (3623 : ℕ) ≤ ((81950577/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3624 :
    ((409766683/50000000 : ℚ) : ℝ) ≤ Real.log (3624 : ℕ)
      ∧ Real.log (3624 : ℕ) ≤ ((819533367/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3625 :
    ((204890239/25000000 : ℚ) : ℝ) ≤ Real.log (3625 : ℕ)
      ∧ Real.log (3625 : ℕ) ≤ ((819560957/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3626 :
    ((819588539/100000000 : ℚ) : ℝ) ≤ Real.log (3626 : ℕ)
      ∧ Real.log (3626 : ℕ) ≤ ((40979427/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3627 :
    ((819616113/100000000 : ℚ) : ℝ) ≤ Real.log (3627 : ℕ)
      ∧ Real.log (3627 : ℕ) ≤ ((409808057/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3628 :
    ((819643681/100000000 : ℚ) : ℝ) ≤ Real.log (3628 : ℕ)
      ∧ Real.log (3628 : ℕ) ≤ ((409821841/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3629 :
    ((20491781/2500000 : ℚ) : ℝ) ≤ Real.log (3629 : ℕ)
      ∧ Real.log (3629 : ℕ) ≤ ((819671241/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3630 :
    ((102462349/12500000 : ℚ) : ℝ) ≤ Real.log (3630 : ℕ)
      ∧ Real.log (3630 : ℕ) ≤ ((819698793/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3631 :
    ((819726337/100000000 : ℚ) : ℝ) ≤ Real.log (3631 : ℕ)
      ∧ Real.log (3631 : ℕ) ≤ ((409863169/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3632 :
    ((51234617/6250000 : ℚ) : ℝ) ≤ Real.log (3632 : ℕ)
      ∧ Real.log (3632 : ℕ) ≤ ((6558031/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3633 :
    ((819781403/100000000 : ℚ) : ℝ) ≤ Real.log (3633 : ℕ)
      ∧ Real.log (3633 : ℕ) ≤ ((204945351/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3634 :
    ((204952231/25000000 : ℚ) : ℝ) ≤ Real.log (3634 : ℕ)
      ∧ Real.log (3634 : ℕ) ≤ ((32792357/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3635 :
    ((819836437/100000000 : ℚ) : ℝ) ≤ Real.log (3635 : ℕ)
      ∧ Real.log (3635 : ℕ) ≤ ((20495911/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3636 :
    ((163972789/20000000 : ℚ) : ℝ) ≤ Real.log (3636 : ℕ)
      ∧ Real.log (3636 : ℕ) ≤ ((409931973/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3637 :
    ((204972861/25000000 : ℚ) : ℝ) ≤ Real.log (3637 : ℕ)
      ∧ Real.log (3637 : ℕ) ≤ ((163978289/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3638 :
    ((163983787/20000000 : ℚ) : ℝ) ≤ Real.log (3638 : ℕ)
      ∧ Real.log (3638 : ℕ) ≤ ((102489867/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3639 :
    ((819946419/100000000 : ℚ) : ℝ) ≤ Real.log (3639 : ℕ)
      ∧ Real.log (3639 : ℕ) ≤ ((40997321/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3640 :
    ((102496737/12500000 : ℚ) : ℝ) ≤ Real.log (3640 : ℕ)
      ∧ Real.log (3640 : ℕ) ≤ ((819973897/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3641 :
    ((205000341/25000000 : ℚ) : ℝ) ≤ Real.log (3641 : ℕ)
      ∧ Real.log (3641 : ℕ) ≤ ((164000273/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3642 :
    ((32801153/4000000 : ℚ) : ℝ) ≤ Real.log (3642 : ℕ)
      ∧ Real.log (3642 : ℕ) ≤ ((205007207/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3643 :
    ((820056279/100000000 : ℚ) : ℝ) ≤ Real.log (3643 : ℕ)
      ∧ Real.log (3643 : ℕ) ≤ ((20501407/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3644 :
    ((32803349/4000000 : ℚ) : ℝ) ≤ Real.log (3644 : ℕ)
      ∧ Real.log (3644 : ℕ) ≤ ((410041863/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3645 :
    ((205027791/25000000 : ℚ) : ℝ) ≤ Real.log (3645 : ℕ)
      ∧ Real.log (3645 : ℕ) ≤ ((164022233/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3646 :
    ((164027719/20000000 : ℚ) : ℝ) ≤ Real.log (3646 : ℕ)
      ∧ Real.log (3646 : ℕ) ≤ ((205034649/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3647 :
    ((820166019/100000000 : ℚ) : ℝ) ≤ Real.log (3647 : ℕ)
      ∧ Real.log (3647 : ℕ) ≤ ((41008301/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3648 :
    ((164038687/20000000 : ℚ) : ℝ) ≤ Real.log (3648 : ℕ)
      ∧ Real.log (3648 : ℕ) ≤ ((205048359/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3649 :
    ((820220843/100000000 : ℚ) : ℝ) ≤ Real.log (3649 : ℕ)
      ∧ Real.log (3649 : ℕ) ≤ ((205055211/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3650 :
    ((205062061/25000000 : ℚ) : ℝ) ≤ Real.log (3650 : ℕ)
      ∧ Real.log (3650 : ℕ) ≤ ((164049649/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3651 :
    ((410137819/50000000 : ℚ) : ℝ) ≤ Real.log (3651 : ℕ)
      ∧ Real.log (3651 : ℕ) ≤ ((820275639/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3652 :
    ((51268939/6250000 : ℚ) : ℝ) ≤ Real.log (3652 : ℕ)
      ∧ Real.log (3652 : ℕ) ≤ ((32812121/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3653 :
    ((410165201/50000000 : ℚ) : ℝ) ≤ Real.log (3653 : ℕ)
      ∧ Real.log (3653 : ℕ) ≤ ((820330403/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3654 :
    ((820357773/100000000 : ℚ) : ℝ) ≤ Real.log (3654 : ℕ)
      ∧ Real.log (3654 : ℕ) ≤ ((410178887/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3655 :
    ((820385137/100000000 : ℚ) : ℝ) ≤ Real.log (3655 : ℕ)
      ∧ Real.log (3655 : ℕ) ≤ ((410192569/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3656 :
    ((820412493/100000000 : ℚ) : ℝ) ≤ Real.log (3656 : ℕ)
      ∧ Real.log (3656 : ℕ) ≤ ((410206247/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3657 :
    ((820439841/100000000 : ℚ) : ℝ) ≤ Real.log (3657 : ℕ)
      ∧ Real.log (3657 : ℕ) ≤ ((410219921/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3658 :
    ((410233591/50000000 : ℚ) : ℝ) ≤ Real.log (3658 : ℕ)
      ∧ Real.log (3658 : ℕ) ≤ ((820467183/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3659 :
    ((205123629/25000000 : ℚ) : ℝ) ≤ Real.log (3659 : ℕ)
      ∧ Real.log (3659 : ℕ) ≤ ((820494517/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3660 :
    ((410260921/50000000 : ℚ) : ℝ) ≤ Real.log (3660 : ℕ)
      ∧ Real.log (3660 : ℕ) ≤ ((820521843/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3661 :
    ((820549161/100000000 : ℚ) : ℝ) ≤ Real.log (3661 : ℕ)
      ∧ Real.log (3661 : ℕ) ≤ ((410274581/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3662 :
    ((102572059/12500000 : ℚ) : ℝ) ≤ Real.log (3662 : ℕ)
      ∧ Real.log (3662 : ℕ) ≤ ((820576473/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3663 :
    ((6410967/781250 : ℚ) : ℝ) ≤ Real.log (3663 : ℕ)
      ∧ Real.log (3663 : ℕ) ≤ ((820603777/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3664 :
    ((25644721/3125000 : ℚ) : ℝ) ≤ Real.log (3664 : ℕ)
      ∧ Real.log (3664 : ℕ) ≤ ((820631073/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3665 :
    ((820658361/100000000 : ℚ) : ℝ) ≤ Real.log (3665 : ℕ)
      ∧ Real.log (3665 : ℕ) ≤ ((410329181/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3666 :
    ((410342821/50000000 : ℚ) : ℝ) ≤ Real.log (3666 : ℕ)
      ∧ Real.log (3666 : ℕ) ≤ ((820685643/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3667 :
    ((205178229/25000000 : ℚ) : ℝ) ≤ Real.log (3667 : ℕ)
      ∧ Real.log (3667 : ℕ) ≤ ((820712917/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3668 :
    ((820740183/100000000 : ℚ) : ℝ) ≤ Real.log (3668 : ℕ)
      ∧ Real.log (3668 : ℕ) ≤ ((102592523/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3669 :
    ((410383721/50000000 : ℚ) : ℝ) ≤ Real.log (3669 : ℕ)
      ∧ Real.log (3669 : ℕ) ≤ ((820767443/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3670 :
    ((410397347/50000000 : ℚ) : ℝ) ≤ Real.log (3670 : ℕ)
      ∧ Real.log (3670 : ℕ) ≤ ((164158939/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3671 :
    ((410410969/50000000 : ℚ) : ℝ) ≤ Real.log (3671 : ℕ)
      ∧ Real.log (3671 : ℕ) ≤ ((820821939/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3672 :
    ((32833967/4000000 : ℚ) : ℝ) ≤ Real.log (3672 : ℕ)
      ∧ Real.log (3672 : ℕ) ≤ ((102606147/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3673 :
    ((205219101/25000000 : ℚ) : ℝ) ≤ Real.log (3673 : ℕ)
      ∧ Real.log (3673 : ℕ) ≤ ((164175281/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3674 :
    ((410451813/50000000 : ℚ) : ℝ) ≤ Real.log (3674 : ℕ)
      ∧ Real.log (3674 : ℕ) ≤ ((820903627/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3675 :
    ((820930841/100000000 : ℚ) : ℝ) ≤ Real.log (3675 : ℕ)
      ∧ Real.log (3675 : ℕ) ≤ ((410465421/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3676 :
    ((25654939/3125000 : ℚ) : ℝ) ≤ Real.log (3676 : ℕ)
      ∧ Real.log (3676 : ℕ) ≤ ((820958049/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3677 :
    ((25655789/3125000 : ℚ) : ℝ) ≤ Real.log (3677 : ℕ)
      ∧ Real.log (3677 : ℕ) ≤ ((820985249/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3678 :
    ((20525311/2500000 : ℚ) : ℝ) ≤ Real.log (3678 : ℕ)
      ∧ Real.log (3678 : ℕ) ≤ ((821012441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3679 :
    ((6568317/800000 : ℚ) : ℝ) ≤ Real.log (3679 : ℕ)
      ∧ Real.log (3679 : ℕ) ≤ ((410519813/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3680 :
    ((821066803/100000000 : ℚ) : ℝ) ≤ Real.log (3680 : ℕ)
      ∧ Real.log (3680 : ℕ) ≤ ((205266701/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3681 :
    ((821093973/100000000 : ℚ) : ℝ) ≤ Real.log (3681 : ℕ)
      ∧ Real.log (3681 : ℕ) ≤ ((410546987/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3682 :
    ((51320071/6250000 : ℚ) : ℝ) ≤ Real.log (3682 : ℕ)
      ∧ Real.log (3682 : ℕ) ≤ ((821121137/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3683 :
    ((821148291/100000000 : ℚ) : ℝ) ≤ Real.log (3683 : ℕ)
      ∧ Real.log (3683 : ℕ) ≤ ((205287073/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3684 :
    ((821175439/100000000 : ℚ) : ℝ) ≤ Real.log (3684 : ℕ)
      ∧ Real.log (3684 : ℕ) ≤ ((10264693/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3685 :
    ((41060129/5000000 : ℚ) : ℝ) ≤ Real.log (3685 : ℕ)
      ∧ Real.log (3685 : ℕ) ≤ ((821202581/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3686 :
    ((821229713/100000000 : ℚ) : ℝ) ≤ Real.log (3686 : ℕ)
      ∧ Real.log (3686 : ℕ) ≤ ((410614857/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3687 :
    ((821256839/100000000 : ℚ) : ℝ) ≤ Real.log (3687 : ℕ)
      ∧ Real.log (3687 : ℕ) ≤ ((20531421/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3688 :
    ((410641979/50000000 : ℚ) : ℝ) ≤ Real.log (3688 : ℕ)
      ∧ Real.log (3688 : ℕ) ≤ ((821283959/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3689 :
    ((821311069/100000000 : ℚ) : ℝ) ≤ Real.log (3689 : ℕ)
      ∧ Real.log (3689 : ℕ) ≤ ((82131107/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3690 :
    ((821338173/100000000 : ℚ) : ℝ) ≤ Real.log (3690 : ℕ)
      ∧ Real.log (3690 : ℕ) ≤ ((410669087/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3691 :
    ((82136527/10000000 : ℚ) : ℝ) ≤ Real.log (3691 : ℕ)
      ∧ Real.log (3691 : ℕ) ≤ ((821365271/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3692 :
    ((821392359/100000000 : ℚ) : ℝ) ≤ Real.log (3692 : ℕ)
      ∧ Real.log (3692 : ℕ) ≤ ((20534809/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3693 :
    ((821419441/100000000 : ℚ) : ℝ) ≤ Real.log (3693 : ℕ)
      ∧ Real.log (3693 : ℕ) ≤ ((410709721/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3694 :
    ((205361629/25000000 : ℚ) : ℝ) ≤ Real.log (3694 : ℕ)
      ∧ Real.log (3694 : ℕ) ≤ ((821446517/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3695 :
    ((821473583/100000000 : ℚ) : ℝ) ≤ Real.log (3695 : ℕ)
      ∧ Real.log (3695 : ℕ) ≤ ((51342099/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3696 :
    ((821500643/100000000 : ℚ) : ℝ) ≤ Real.log (3696 : ℕ)
      ∧ Real.log (3696 : ℕ) ≤ ((205375161/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3697 :
    ((164305539/20000000 : ℚ) : ℝ) ≤ Real.log (3697 : ℕ)
      ∧ Real.log (3697 : ℕ) ≤ ((51345481/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3698 :
    ((821554741/100000000 : ℚ) : ℝ) ≤ Real.log (3698 : ℕ)
      ∧ Real.log (3698 : ℕ) ≤ ((410777371/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3699 :
    ((821581779/100000000 : ℚ) : ℝ) ≤ Real.log (3699 : ℕ)
      ∧ Real.log (3699 : ℕ) ≤ ((41079089/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3700 :
    ((821608809/100000000 : ℚ) : ℝ) ≤ Real.log (3700 : ℕ)
      ∧ Real.log (3700 : ℕ) ≤ ((82160881/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3701 :
    ((821635833/100000000 : ℚ) : ℝ) ≤ Real.log (3701 : ℕ)
      ∧ Real.log (3701 : ℕ) ≤ ((410817917/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3702 :
    ((821662849/100000000 : ℚ) : ℝ) ≤ Real.log (3702 : ℕ)
      ∧ Real.log (3702 : ℕ) ≤ ((16433257/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3703 :
    ((410844929/50000000 : ℚ) : ℝ) ≤ Real.log (3703 : ℕ)
      ∧ Real.log (3703 : ℕ) ≤ ((821689859/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3704 :
    ((821716859/100000000 : ℚ) : ℝ) ≤ Real.log (3704 : ℕ)
      ∧ Real.log (3704 : ℕ) ≤ ((41085843/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3705 :
    ((821743853/100000000 : ℚ) : ℝ) ≤ Real.log (3705 : ℕ)
      ∧ Real.log (3705 : ℕ) ≤ ((410871927/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3706 :
    ((20544271/2500000 : ℚ) : ℝ) ≤ Real.log (3706 : ℕ)
      ∧ Real.log (3706 : ℕ) ≤ ((821770841/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3707 :
    ((41089891/5000000 : ℚ) : ℝ) ≤ Real.log (3707 : ℕ)
      ∧ Real.log (3707 : ℕ) ≤ ((821797821/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3708 :
    ((102728099/12500000 : ℚ) : ℝ) ≤ Real.log (3708 : ℕ)
      ∧ Real.log (3708 : ℕ) ≤ ((821824793/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3709 :
    ((821851757/100000000 : ℚ) : ℝ) ≤ Real.log (3709 : ℕ)
      ∧ Real.log (3709 : ℕ) ≤ ((410925879/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3710 :
    ((164375743/20000000 : ℚ) : ℝ) ≤ Real.log (3710 : ℕ)
      ∧ Real.log (3710 : ℕ) ≤ ((205469679/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3711 :
    ((410952833/50000000 : ℚ) : ℝ) ≤ Real.log (3711 : ℕ)
      ∧ Real.log (3711 : ℕ) ≤ ((821905667/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3712 :
    ((821932609/100000000 : ℚ) : ℝ) ≤ Real.log (3712 : ℕ)
      ∧ Real.log (3712 : ℕ) ≤ ((82193261/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3713 :
    ((164391909/20000000 : ℚ) : ℝ) ≤ Real.log (3713 : ℕ)
      ∧ Real.log (3713 : ℕ) ≤ ((410979773/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3714 :
    ((410993237/50000000 : ℚ) : ℝ) ≤ Real.log (3714 : ℕ)
      ∧ Real.log (3714 : ℕ) ≤ ((32879459/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3715 :
    ((164402679/20000000 : ℚ) : ℝ) ≤ Real.log (3715 : ℕ)
      ∧ Real.log (3715 : ℕ) ≤ ((205503349/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3716 :
    ((205510077/25000000 : ℚ) : ℝ) ≤ Real.log (3716 : ℕ)
      ∧ Real.log (3716 : ℕ) ≤ ((822040311/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3717 :
    ((51379201/6250000 : ℚ) : ℝ) ≤ Real.log (3717 : ℕ)
      ∧ Real.log (3717 : ℕ) ≤ ((822067219/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3718 :
    ((205523529/25000000 : ℚ) : ℝ) ≤ Real.log (3718 : ℕ)
      ∧ Real.log (3718 : ℕ) ≤ ((822094117/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3719 :
    ((822121009/100000000 : ℚ) : ℝ) ≤ Real.log (3719 : ℕ)
      ∧ Real.log (3719 : ℕ) ≤ ((82212101/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3720 :
    ((411073947/50000000 : ℚ) : ℝ) ≤ Real.log (3720 : ℕ)
      ∧ Real.log (3720 : ℕ) ≤ ((164429579/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3721 :
    ((205543693/25000000 : ℚ) : ℝ) ≤ Real.log (3721 : ℕ)
      ∧ Real.log (3721 : ℕ) ≤ ((822174773/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3722 :
    ((822201643/100000000 : ℚ) : ℝ) ≤ Real.log (3722 : ℕ)
      ∧ Real.log (3722 : ℕ) ≤ ((205550411/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3723 :
    ((822228507/100000000 : ℚ) : ℝ) ≤ Real.log (3723 : ℕ)
      ∧ Real.log (3723 : ℕ) ≤ ((205557127/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3724 :
    ((822255363/100000000 : ℚ) : ℝ) ≤ Real.log (3724 : ℕ)
      ∧ Real.log (3724 : ℕ) ≤ ((205563841/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3725 :
    ((822282213/100000000 : ℚ) : ℝ) ≤ Real.log (3725 : ℕ)
      ∧ Real.log (3725 : ℕ) ≤ ((411141107/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3726 :
    ((164461811/20000000 : ℚ) : ℝ) ≤ Real.log (3726 : ℕ)
      ∧ Real.log (3726 : ℕ) ≤ ((12848579/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3727 :
    ((822335889/100000000 : ℚ) : ℝ) ≤ Real.log (3727 : ℕ)
      ∧ Real.log (3727 : ℕ) ≤ ((82233589/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3728 :
    ((822362717/100000000 : ℚ) : ℝ) ≤ Real.log (3728 : ℕ)
      ∧ Real.log (3728 : ℕ) ≤ ((411181359/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3729 :
    ((822389537/100000000 : ℚ) : ℝ) ≤ Real.log (3729 : ℕ)
      ∧ Real.log (3729 : ℕ) ≤ ((41119477/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3730 :
    ((822416351/100000000 : ℚ) : ℝ) ≤ Real.log (3730 : ℕ)
      ∧ Real.log (3730 : ℕ) ≤ ((25700511/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3731 :
    ((822443157/100000000 : ℚ) : ℝ) ≤ Real.log (3731 : ℕ)
      ∧ Real.log (3731 : ℕ) ≤ ((411221579/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3732 :
    ((205617489/25000000 : ℚ) : ℝ) ≤ Real.log (3732 : ℕ)
      ∧ Real.log (3732 : ℕ) ≤ ((822469957/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3733 :
    ((822496747/100000000 : ℚ) : ℝ) ≤ Real.log (3733 : ℕ)
      ∧ Real.log (3733 : ℕ) ≤ ((205624187/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3734 :
    ((205630883/25000000 : ℚ) : ℝ) ≤ Real.log (3734 : ℕ)
      ∧ Real.log (3734 : ℕ) ≤ ((822523533/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3735 :
    ((822550309/100000000 : ℚ) : ℝ) ≤ Real.log (3735 : ℕ)
      ∧ Real.log (3735 : ℕ) ≤ ((82255031/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3736 :
    ((822577079/100000000 : ℚ) : ℝ) ≤ Real.log (3736 : ℕ)
      ∧ Real.log (3736 : ℕ) ≤ ((20564427/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3737 :
    ((411301921/50000000 : ℚ) : ℝ) ≤ Real.log (3737 : ℕ)
      ∧ Real.log (3737 : ℕ) ≤ ((822603843/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3738 :
    ((411315299/50000000 : ℚ) : ℝ) ≤ Real.log (3738 : ℕ)
      ∧ Real.log (3738 : ℕ) ≤ ((822630599/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3739 :
    ((822657347/100000000 : ℚ) : ℝ) ≤ Real.log (3739 : ℕ)
      ∧ Real.log (3739 : ℕ) ≤ ((205664337/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3740 :
    ((102835511/12500000 : ℚ) : ℝ) ≤ Real.log (3740 : ℕ)
      ∧ Real.log (3740 : ℕ) ≤ ((822684091/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3741 :
    ((822710823/100000000 : ℚ) : ℝ) ≤ Real.log (3741 : ℕ)
      ∧ Real.log (3741 : ℕ) ≤ ((102838853/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3742 :
    ((16454751/2000000 : ℚ) : ℝ) ≤ Real.log (3742 : ℕ)
      ∧ Real.log (3742 : ℕ) ≤ ((822737551/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3743 :
    ((82276427/10000000 : ℚ) : ℝ) ≤ Real.log (3743 : ℕ)
      ∧ Real.log (3743 : ℕ) ≤ ((822764271/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3744 :
    ((822790983/100000000 : ℚ) : ℝ) ≤ Real.log (3744 : ℕ)
      ∧ Real.log (3744 : ℕ) ≤ ((102848873/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3745 :
    ((822817689/100000000 : ℚ) : ℝ) ≤ Real.log (3745 : ℕ)
      ∧ Real.log (3745 : ℕ) ≤ ((82281769/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3746 :
    ((205711097/25000000 : ℚ) : ℝ) ≤ Real.log (3746 : ℕ)
      ∧ Real.log (3746 : ℕ) ≤ ((822844389/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3747 :
    ((822871079/100000000 : ℚ) : ℝ) ≤ Real.log (3747 : ℕ)
      ∧ Real.log (3747 : ℕ) ≤ ((20571777/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3748 :
    ((205724441/25000000 : ℚ) : ℝ) ≤ Real.log (3748 : ℕ)
      ∧ Real.log (3748 : ℕ) ≤ ((164579553/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3749 :
    ((822924441/100000000 : ℚ) : ℝ) ≤ Real.log (3749 : ℕ)
      ∧ Real.log (3749 : ℕ) ≤ ((411462221/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3750 :
    ((822951111/100000000 : ℚ) : ℝ) ≤ Real.log (3750 : ℕ)
      ∧ Real.log (3750 : ℕ) ≤ ((102868889/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3751 :
    ((411488887/50000000 : ℚ) : ℝ) ≤ Real.log (3751 : ℕ)
      ∧ Real.log (3751 : ℕ) ≤ ((822977777/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3752 :
    ((82300443/10000000 : ℚ) : ℝ) ≤ Real.log (3752 : ℕ)
      ∧ Real.log (3752 : ℕ) ≤ ((823004433/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3753 :
    ((823031079/100000000 : ℚ) : ℝ) ≤ Real.log (3753 : ℕ)
      ∧ Real.log (3753 : ℕ) ≤ ((20575777/2500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3754 :
    ((823057721/100000000 : ℚ) : ℝ) ≤ Real.log (3754 : ℕ)
      ∧ Real.log (3754 : ℕ) ≤ ((411528861/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3755 :
    ((205771089/25000000 : ℚ) : ℝ) ≤ Real.log (3755 : ℕ)
      ∧ Real.log (3755 : ℕ) ≤ ((823084357/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3756 :
    ((823110983/100000000 : ℚ) : ℝ) ≤ Real.log (3756 : ℕ)
      ∧ Real.log (3756 : ℕ) ≤ ((411555493/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3757 :
    ((205784401/25000000 : ℚ) : ℝ) ≤ Real.log (3757 : ℕ)
      ∧ Real.log (3757 : ℕ) ≤ ((164627521/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3758 :
    ((102895527/12500000 : ℚ) : ℝ) ≤ Real.log (3758 : ℕ)
      ∧ Real.log (3758 : ℕ) ≤ ((823164219/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3759 :
    ((102898853/12500000 : ℚ) : ℝ) ≤ Real.log (3759 : ℕ)
      ∧ Real.log (3759 : ℕ) ≤ ((32927633/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3760 :
    ((823217423/100000000 : ℚ) : ℝ) ≤ Real.log (3760 : ℕ)
      ∧ Real.log (3760 : ℕ) ≤ ((51451089/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3761 :
    ((164648803/20000000 : ℚ) : ℝ) ≤ Real.log (3761 : ℕ)
      ∧ Real.log (3761 : ℕ) ≤ ((51452751/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3762 :
    ((823270599/100000000 : ℚ) : ℝ) ≤ Real.log (3762 : ℕ)
      ∧ Real.log (3762 : ℕ) ≤ ((411635301/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3763 :
    ((823297179/100000000 : ℚ) : ℝ) ≤ Real.log (3763 : ℕ)
      ∧ Real.log (3763 : ℕ) ≤ ((41164859/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3764 :
    ((658659/80000 : ℚ) : ℝ) ≤ Real.log (3764 : ℕ)
      ∧ Real.log (3764 : ℕ) ≤ ((823323751/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3765 :
    ((823350313/100000000 : ℚ) : ℝ) ≤ Real.log (3765 : ℕ)
      ∧ Real.log (3765 : ℕ) ≤ ((205837579/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3766 :
    ((82337687/10000000 : ℚ) : ℝ) ≤ Real.log (3766 : ℕ)
      ∧ Real.log (3766 : ℕ) ≤ ((823376871/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3767 :
    ((41170171/5000000 : ℚ) : ℝ) ≤ Real.log (3767 : ℕ)
      ∧ Real.log (3767 : ℕ) ≤ ((823403421/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3768 :
    ((823429963/100000000 : ℚ) : ℝ) ≤ Real.log (3768 : ℕ)
      ∧ Real.log (3768 : ℕ) ≤ ((205857491/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3769 :
    ((823456499/100000000 : ℚ) : ℝ) ≤ Real.log (3769 : ℕ)
      ∧ Real.log (3769 : ℕ) ≤ ((1646913/200000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3770 :
    ((205870757/25000000 : ℚ) : ℝ) ≤ Real.log (3770 : ℕ)
      ∧ Real.log (3770 : ℕ) ≤ ((823483029/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3771 :
    ((823509549/100000000 : ℚ) : ℝ) ≤ Real.log (3771 : ℕ)
      ∧ Real.log (3771 : ℕ) ≤ ((16470191/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3772 :
    ((12867751/1562500 : ℚ) : ℝ) ≤ Real.log (3772 : ℕ)
      ∧ Real.log (3772 : ℕ) ≤ ((164707213/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3773 :
    ((82356257/10000000 : ℚ) : ℝ) ≤ Real.log (3773 : ℕ)
      ∧ Real.log (3773 : ℕ) ≤ ((823562573/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3774 :
    ((51474317/6250000 : ℚ) : ℝ) ≤ Real.log (3774 : ℕ)
      ∧ Real.log (3774 : ℕ) ≤ ((823589073/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3775 :
    ((411807783/50000000 : ℚ) : ℝ) ≤ Real.log (3775 : ℕ)
      ∧ Real.log (3775 : ℕ) ≤ ((823615567/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3776 :
    ((205910513/25000000 : ℚ) : ℝ) ≤ Real.log (3776 : ℕ)
      ∧ Real.log (3776 : ℕ) ≤ ((823642053/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3777 :
    ((205917133/25000000 : ℚ) : ℝ) ≤ Real.log (3777 : ℕ)
      ∧ Real.log (3777 : ℕ) ≤ ((823668533/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3778 :
    ((205923751/25000000 : ℚ) : ℝ) ≤ Real.log (3778 : ℕ)
      ∧ Real.log (3778 : ℕ) ≤ ((164739001/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3779 :
    ((82372147/10000000 : ℚ) : ℝ) ≤ Real.log (3779 : ℕ)
      ∧ Real.log (3779 : ℕ) ≤ ((823721471/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3780 :
    ((102968491/12500000 : ℚ) : ℝ) ≤ Real.log (3780 : ℕ)
      ∧ Real.log (3780 : ℕ) ≤ ((823747929/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3781 :
    ((41188719/5000000 : ℚ) : ℝ) ≤ Real.log (3781 : ℕ)
      ∧ Real.log (3781 : ℕ) ≤ ((823774381/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3782 :
    ((102975103/12500000 : ℚ) : ℝ) ≤ Real.log (3782 : ℕ)
      ∧ Real.log (3782 : ℕ) ≤ ((32952033/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3783 :
    ((411913631/50000000 : ℚ) : ℝ) ≤ Real.log (3783 : ℕ)
      ∧ Real.log (3783 : ℕ) ≤ ((823827263/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3784 :
    ((205963423/25000000 : ℚ) : ℝ) ≤ Real.log (3784 : ℕ)
      ∧ Real.log (3784 : ℕ) ≤ ((164770739/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3785 :
    ((205970029/25000000 : ℚ) : ℝ) ≤ Real.log (3785 : ℕ)
      ∧ Real.log (3785 : ℕ) ≤ ((823880117/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3786 :
    ((823906533/100000000 : ℚ) : ℝ) ≤ Real.log (3786 : ℕ)
      ∧ Real.log (3786 : ℕ) ≤ ((411953267/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3787 :
    ((411966471/50000000 : ℚ) : ℝ) ≤ Real.log (3787 : ℕ)
      ∧ Real.log (3787 : ℕ) ≤ ((823932943/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3788 :
    ((164791869/20000000 : ℚ) : ℝ) ≤ Real.log (3788 : ℕ)
      ∧ Real.log (3788 : ℕ) ≤ ((411979673/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3789 :
    ((823985741/100000000 : ℚ) : ℝ) ≤ Real.log (3789 : ℕ)
      ∧ Real.log (3789 : ℕ) ≤ ((411992871/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3790 :
    ((824012129/100000000 : ℚ) : ℝ) ≤ Real.log (3790 : ℕ)
      ∧ Real.log (3790 : ℕ) ≤ ((82401213/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3791 :
    ((824038511/100000000 : ℚ) : ℝ) ≤ Real.log (3791 : ℕ)
      ∧ Real.log (3791 : ℕ) ≤ ((51502407/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3792 :
    ((412032443/50000000 : ℚ) : ℝ) ≤ Real.log (3792 : ℕ)
      ∧ Real.log (3792 : ℕ) ≤ ((824064887/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3793 :
    ((412045627/50000000 : ℚ) : ℝ) ≤ Real.log (3793 : ℕ)
      ∧ Real.log (3793 : ℕ) ≤ ((164818251/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3794 :
    ((164823523/20000000 : ℚ) : ℝ) ≤ Real.log (3794 : ℕ)
      ∧ Real.log (3794 : ℕ) ≤ ((51507351/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3795 :
    ((824143967/100000000 : ℚ) : ℝ) ≤ Real.log (3795 : ℕ)
      ∧ Real.log (3795 : ℕ) ≤ ((82414397/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3796 :
    ((412085157/50000000 : ℚ) : ℝ) ≤ Real.log (3796 : ℕ)
      ∧ Real.log (3796 : ℕ) ≤ ((824170317/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3797 :
    ((164839331/20000000 : ℚ) : ℝ) ≤ Real.log (3797 : ℕ)
      ∧ Real.log (3797 : ℕ) ≤ ((412098329/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3798 :
    ((824222989/100000000 : ℚ) : ℝ) ≤ Real.log (3798 : ℕ)
      ∧ Real.log (3798 : ℕ) ≤ ((82422299/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3799 :
    ((164849863/20000000 : ℚ) : ℝ) ≤ Real.log (3799 : ℕ)
      ∧ Real.log (3799 : ℕ) ≤ ((206062329/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3800 :
    ((412137817/50000000 : ℚ) : ℝ) ≤ Real.log (3800 : ℕ)
      ∧ Real.log (3800 : ℕ) ≤ ((164855127/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3801 :
    ((412150973/50000000 : ℚ) : ℝ) ≤ Real.log (3801 : ℕ)
      ∧ Real.log (3801 : ℕ) ≤ ((824301947/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3802 :
    ((206082063/25000000 : ℚ) : ℝ) ≤ Real.log (3802 : ℕ)
      ∧ Real.log (3802 : ℕ) ≤ ((824328253/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3803 :
    ((16487091/2000000 : ℚ) : ℝ) ≤ Real.log (3803 : ℕ)
      ∧ Real.log (3803 : ℕ) ≤ ((824354551/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3804 :
    ((412190421/50000000 : ℚ) : ℝ) ≤ Real.log (3804 : ℕ)
      ∧ Real.log (3804 : ℕ) ≤ ((824380843/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3805 :
    ((412203563/50000000 : ℚ) : ℝ) ≤ Real.log (3805 : ℕ)
      ∧ Real.log (3805 : ℕ) ≤ ((824407129/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3806 :
    ((206108351/25000000 : ℚ) : ℝ) ≤ Real.log (3806 : ℕ)
      ∧ Real.log (3806 : ℕ) ≤ ((164886681/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3807 :
    ((32978387/4000000 : ℚ) : ℝ) ≤ Real.log (3807 : ℕ)
      ∧ Real.log (3807 : ℕ) ≤ ((206114919/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3808 :
    ((824485939/100000000 : ℚ) : ℝ) ≤ Real.log (3808 : ℕ)
      ∧ Real.log (3808 : ℕ) ≤ ((41224297/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3809 :
    ((206128049/25000000 : ℚ) : ℝ) ≤ Real.log (3809 : ℕ)
      ∧ Real.log (3809 : ℕ) ≤ ((824512197/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3810 :
    ((412269223/50000000 : ℚ) : ℝ) ≤ Real.log (3810 : ℕ)
      ∧ Real.log (3810 : ℕ) ≤ ((824538447/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3811 :
    ((82456469/10000000 : ℚ) : ℝ) ≤ Real.log (3811 : ℕ)
      ∧ Real.log (3811 : ℕ) ≤ ((824564691/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3812 :
    ((412295463/50000000 : ℚ) : ℝ) ≤ Real.log (3812 : ℕ)
      ∧ Real.log (3812 : ℕ) ≤ ((824590927/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3813 :
    ((412308577/50000000 : ℚ) : ℝ) ≤ Real.log (3813 : ℕ)
      ∧ Real.log (3813 : ℕ) ≤ ((824617157/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3814 :
    ((412321689/50000000 : ℚ) : ℝ) ≤ Real.log (3814 : ℕ)
      ∧ Real.log (3814 : ℕ) ≤ ((824643379/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3815 :
    ((412334797/50000000 : ℚ) : ℝ) ≤ Real.log (3815 : ℕ)
      ∧ Real.log (3815 : ℕ) ≤ ((164933919/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3816 :
    ((824695803/100000000 : ℚ) : ℝ) ≤ Real.log (3816 : ℕ)
      ∧ Real.log (3816 : ℕ) ≤ ((206173951/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3817 :
    ((164944401/20000000 : ℚ) : ℝ) ≤ Real.log (3817 : ℕ)
      ∧ Real.log (3817 : ℕ) ≤ ((412361003/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3818 :
    ((4123741/500000 : ℚ) : ℝ) ≤ Real.log (3818 : ℕ)
      ∧ Real.log (3818 : ℕ) ≤ ((824748201/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3819 :
    ((206193597/25000000 : ℚ) : ℝ) ≤ Real.log (3819 : ℕ)
      ∧ Real.log (3819 : ℕ) ≤ ((824774389/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3820 :
    ((82480057/10000000 : ℚ) : ℝ) ≤ Real.log (3820 : ℕ)
      ∧ Real.log (3820 : ℕ) ≤ ((824800571/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3821 :
    ((103103343/12500000 : ℚ) : ℝ) ≤ Real.log (3821 : ℕ)
      ∧ Real.log (3821 : ℕ) ≤ ((164965349/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3822 :
    ((51553307/6250000 : ℚ) : ℝ) ≤ Real.log (3822 : ℕ)
      ∧ Real.log (3822 : ℕ) ≤ ((824852913/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3823 :
    ((824879073/100000000 : ℚ) : ℝ) ≤ Real.log (3823 : ℕ)
      ∧ Real.log (3823 : ℕ) ≤ ((412439537/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3824 :
    ((824905227/100000000 : ℚ) : ℝ) ≤ Real.log (3824 : ℕ)
      ∧ Real.log (3824 : ℕ) ≤ ((206226307/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3825 :
    ((412465687/50000000 : ℚ) : ℝ) ≤ Real.log (3825 : ℕ)
      ∧ Real.log (3825 : ℕ) ≤ ((6599451/800000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3826 :
    ((412478757/50000000 : ℚ) : ℝ) ≤ Real.log (3826 : ℕ)
      ∧ Real.log (3826 : ℕ) ≤ ((824957517/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3827 :
    ((25780739/3125000 : ℚ) : ℝ) ≤ Real.log (3827 : ℕ)
      ∧ Real.log (3827 : ℕ) ≤ ((824983649/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3828 :
    ((33000391/4000000 : ℚ) : ℝ) ≤ Real.log (3828 : ℕ)
      ∧ Real.log (3828 : ℕ) ≤ ((51563111/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3829 :
    ((165007179/20000000 : ℚ) : ℝ) ≤ Real.log (3829 : ℕ)
      ∧ Real.log (3829 : ℕ) ≤ ((103129487/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3830 :
    ((103132751/12500000 : ℚ) : ℝ) ≤ Real.log (3830 : ℕ)
      ∧ Real.log (3830 : ℕ) ≤ ((825062009/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3831 :
    ((412544057/50000000 : ℚ) : ℝ) ≤ Real.log (3831 : ℕ)
      ∧ Real.log (3831 : ℕ) ≤ ((165017623/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3832 :
    ((825114213/100000000 : ℚ) : ℝ) ≤ Real.log (3832 : ℕ)
      ∧ Real.log (3832 : ℕ) ≤ ((412557107/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3833 :
    ((412570153/50000000 : ℚ) : ℝ) ≤ Real.log (3833 : ℕ)
      ∧ Real.log (3833 : ℕ) ≤ ((825140307/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3834 :
    ((103145799/12500000 : ℚ) : ℝ) ≤ Real.log (3834 : ℕ)
      ∧ Real.log (3834 : ℕ) ≤ ((825166393/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3835 :
    ((825192471/100000000 : ℚ) : ℝ) ≤ Real.log (3835 : ℕ)
      ∧ Real.log (3835 : ℕ) ≤ ((103149059/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3836 :
    ((825218543/100000000 : ℚ) : ℝ) ≤ Real.log (3836 : ℕ)
      ∧ Real.log (3836 : ℕ) ≤ ((51576159/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3837 :
    ((12894447/1562500 : ℚ) : ℝ) ≤ Real.log (3837 : ℕ)
      ∧ Real.log (3837 : ℕ) ≤ ((825244611/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3838 :
    ((825270667/100000000 : ℚ) : ℝ) ≤ Real.log (3838 : ℕ)
      ∧ Real.log (3838 : ℕ) ≤ ((206317667/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3839 :
    ((825296719/100000000 : ℚ) : ℝ) ≤ Real.log (3839 : ℕ)
      ∧ Real.log (3839 : ℕ) ≤ ((10316209/1250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3840 :
    ((206330691/25000000 : ℚ) : ℝ) ≤ Real.log (3840 : ℕ)
      ∧ Real.log (3840 : ℕ) ≤ ((165064553/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3841 :
    ((412674401/50000000 : ℚ) : ℝ) ≤ Real.log (3841 : ℕ)
      ∧ Real.log (3841 : ℕ) ≤ ((825348803/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3842 :
    ((412687417/50000000 : ℚ) : ℝ) ≤ Real.log (3842 : ℕ)
      ∧ Real.log (3842 : ℕ) ≤ ((165074967/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3843 :
    ((825400859/100000000 : ℚ) : ℝ) ≤ Real.log (3843 : ℕ)
      ∧ Real.log (3843 : ℕ) ≤ ((41270043/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3844 :
    ((206356719/25000000 : ℚ) : ℝ) ≤ Real.log (3844 : ℕ)
      ∧ Real.log (3844 : ℕ) ≤ ((825426879/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3845 :
    ((103181611/12500000 : ℚ) : ℝ) ≤ Real.log (3845 : ℕ)
      ∧ Real.log (3845 : ℕ) ≤ ((825452889/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3846 :
    ((206369723/25000000 : ℚ) : ℝ) ≤ Real.log (3846 : ℕ)
      ∧ Real.log (3846 : ℕ) ≤ ((825478893/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3847 :
    ((82550489/10000000 : ℚ) : ℝ) ≤ Real.log (3847 : ℕ)
      ∧ Real.log (3847 : ℕ) ≤ ((825504891/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3848 :
    ((825530881/100000000 : ℚ) : ℝ) ≤ Real.log (3848 : ℕ)
      ∧ Real.log (3848 : ℕ) ≤ ((412765441/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3849 :
    ((165111373/20000000 : ℚ) : ℝ) ≤ Real.log (3849 : ℕ)
      ∧ Real.log (3849 : ℕ) ≤ ((412778433/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3850 :
    ((412791421/50000000 : ℚ) : ℝ) ≤ Real.log (3850 : ℕ)
      ∧ Real.log (3850 : ℕ) ≤ ((825582843/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3851 :
    ((825608813/100000000 : ℚ) : ℝ) ≤ Real.log (3851 : ℕ)
      ∧ Real.log (3851 : ℕ) ≤ ((412804407/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3852 :
    ((825634777/100000000 : ℚ) : ℝ) ≤ Real.log (3852 : ℕ)
      ∧ Real.log (3852 : ℕ) ≤ ((412817389/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3853 :
    ((412830367/50000000 : ℚ) : ℝ) ≤ Real.log (3853 : ℕ)
      ∧ Real.log (3853 : ℕ) ≤ ((165132147/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3854 :
    ((206421671/25000000 : ℚ) : ℝ) ≤ Real.log (3854 : ℕ)
      ∧ Real.log (3854 : ℕ) ≤ ((165137337/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3855 :
    ((206428157/25000000 : ℚ) : ℝ) ≤ Real.log (3855 : ℕ)
      ∧ Real.log (3855 : ℕ) ≤ ((825712629/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3856 :
    ((165147713/20000000 : ℚ) : ℝ) ≤ Real.log (3856 : ℕ)
      ∧ Real.log (3856 : ℕ) ≤ ((412869283/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3857 :
    ((165152899/20000000 : ℚ) : ℝ) ≤ Real.log (3857 : ℕ)
      ∧ Real.log (3857 : ℕ) ≤ ((51610281/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3858 :
    ((825790419/100000000 : ℚ) : ℝ) ≤ Real.log (3858 : ℕ)
      ∧ Real.log (3858 : ℕ) ≤ ((41289521/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3859 :
    ((51613521/6250000 : ℚ) : ℝ) ≤ Real.log (3859 : ℕ)
      ∧ Real.log (3859 : ℕ) ≤ ((825816337/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3860 :
    ((412921123/50000000 : ℚ) : ℝ) ≤ Real.log (3860 : ℕ)
      ∧ Real.log (3860 : ℕ) ≤ ((825842247/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3861 :
    ((825868149/100000000 : ℚ) : ℝ) ≤ Real.log (3861 : ℕ)
      ∧ Real.log (3861 : ℕ) ≤ ((16517363/2000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3862 :
    ((412947023/50000000 : ℚ) : ℝ) ≤ Real.log (3862 : ℕ)
      ∧ Real.log (3862 : ℕ) ≤ ((825894047/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3863 :
    ((12904999/1562500 : ℚ) : ℝ) ≤ Real.log (3863 : ℕ)
      ∧ Real.log (3863 : ℕ) ≤ ((825919937/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3864 :
    ((825945819/100000000 : ℚ) : ℝ) ≤ Real.log (3864 : ℕ)
      ∧ Real.log (3864 : ℕ) ≤ ((41297291/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3865 :
    ((51623231/6250000 : ℚ) : ℝ) ≤ Real.log (3865 : ℕ)
      ∧ Real.log (3865 : ℕ) ≤ ((825971697/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3866 :
    ((206499391/25000000 : ℚ) : ℝ) ≤ Real.log (3866 : ℕ)
      ∧ Real.log (3866 : ℕ) ≤ ((825997567/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3867 :
    ((826023429/100000000 : ℚ) : ℝ) ≤ Real.log (3867 : ℕ)
      ∧ Real.log (3867 : ℕ) ≤ ((82602343/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3868 :
    ((165209857/20000000 : ℚ) : ℝ) ≤ Real.log (3868 : ℕ)
      ∧ Real.log (3868 : ℕ) ≤ ((413024643/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3869 :
    ((165215027/20000000 : ℚ) : ℝ) ≤ Real.log (3869 : ℕ)
      ∧ Real.log (3869 : ℕ) ≤ ((3226856/390625 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3870 :
    ((413050489/50000000 : ℚ) : ℝ) ≤ Real.log (3870 : ℕ)
      ∧ Real.log (3870 : ℕ) ≤ ((826100979/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3871 :
    ((165225363/20000000 : ℚ) : ℝ) ≤ Real.log (3871 : ℕ)
      ∧ Real.log (3871 : ℕ) ≤ ((25816463/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3872 :
    ((206538161/25000000 : ℚ) : ℝ) ≤ Real.log (3872 : ℕ)
      ∧ Real.log (3872 : ℕ) ≤ ((165230529/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3873 :
    ((413089233/50000000 : ℚ) : ℝ) ≤ Real.log (3873 : ℕ)
      ∧ Real.log (3873 : ℕ) ≤ ((826178469/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3874 :
    ((206551071/25000000 : ℚ) : ℝ) ≤ Real.log (3874 : ℕ)
      ∧ Real.log (3874 : ℕ) ≤ ((165240857/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3875 :
    ((413115047/50000000 : ℚ) : ℝ) ≤ Real.log (3875 : ℕ)
      ∧ Real.log (3875 : ℕ) ≤ ((165246019/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3876 :
    ((826255897/100000000 : ℚ) : ℝ) ≤ Real.log (3876 : ℕ)
      ∧ Real.log (3876 : ℕ) ≤ ((413127949/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3877 :
    ((826281693/100000000 : ℚ) : ℝ) ≤ Real.log (3877 : ℕ)
      ∧ Real.log (3877 : ℕ) ≤ ((413140847/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3878 :
    ((826307483/100000000 : ℚ) : ℝ) ≤ Real.log (3878 : ℕ)
      ∧ Real.log (3878 : ℕ) ≤ ((206576871/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3879 :
    ((413166633/50000000 : ℚ) : ℝ) ≤ Real.log (3879 : ℕ)
      ∧ Real.log (3879 : ℕ) ≤ ((826333267/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3880 :
    ((826359043/100000000 : ℚ) : ℝ) ≤ Real.log (3880 : ℕ)
      ∧ Real.log (3880 : ℕ) ≤ ((206589761/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3881 :
    ((826384813/100000000 : ℚ) : ℝ) ≤ Real.log (3881 : ℕ)
      ∧ Real.log (3881 : ℕ) ≤ ((413192407/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3882 :
    ((51650661/6250000 : ℚ) : ℝ) ≤ Real.log (3882 : ℕ)
      ∧ Real.log (3882 : ℕ) ≤ ((826410577/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3883 :
    ((826436331/100000000 : ℚ) : ℝ) ≤ Real.log (3883 : ℕ)
      ∧ Real.log (3883 : ℕ) ≤ ((413218167/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3884 :
    ((413231041/50000000 : ℚ) : ℝ) ≤ Real.log (3884 : ℕ)
      ∧ Real.log (3884 : ℕ) ≤ ((826462083/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3885 :
    ((413243913/50000000 : ℚ) : ℝ) ≤ Real.log (3885 : ℕ)
      ∧ Real.log (3885 : ℕ) ≤ ((826487827/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3886 :
    ((826513561/100000000 : ℚ) : ℝ) ≤ Real.log (3886 : ℕ)
      ∧ Real.log (3886 : ℕ) ≤ ((206628391/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3887 :
    ((826539293/100000000 : ℚ) : ℝ) ≤ Real.log (3887 : ℕ)
      ∧ Real.log (3887 : ℕ) ≤ ((413269647/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3888 :
    ((103320627/12500000 : ℚ) : ℝ) ≤ Real.log (3888 : ℕ)
      ∧ Real.log (3888 : ℕ) ≤ ((826565017/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3889 :
    ((826590733/100000000 : ℚ) : ℝ) ≤ Real.log (3889 : ℕ)
      ∧ Real.log (3889 : ℕ) ≤ ((413295367/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3890 :
    ((826616443/100000000 : ℚ) : ℝ) ≤ Real.log (3890 : ℕ)
      ∧ Real.log (3890 : ℕ) ≤ ((206654111/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3891 :
    ((826642147/100000000 : ℚ) : ℝ) ≤ Real.log (3891 : ℕ)
      ∧ Real.log (3891 : ℕ) ≤ ((206660537/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3892 :
    ((206666961/25000000 : ℚ) : ℝ) ≤ Real.log (3892 : ℕ)
      ∧ Real.log (3892 : ℕ) ≤ ((165333569/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3893 :
    ((413346767/50000000 : ℚ) : ℝ) ≤ Real.log (3893 : ℕ)
      ∧ Real.log (3893 : ℕ) ≤ ((165338707/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3894 :
    ((413359609/50000000 : ℚ) : ℝ) ≤ Real.log (3894 : ℕ)
      ∧ Real.log (3894 : ℕ) ≤ ((826719219/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3895 :
    ((165348979/20000000 : ℚ) : ℝ) ≤ Real.log (3895 : ℕ)
      ∧ Real.log (3895 : ℕ) ≤ ((12917889/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3896 :
    ((413385283/50000000 : ℚ) : ℝ) ≤ Real.log (3896 : ℕ)
      ∧ Real.log (3896 : ℕ) ≤ ((826770567/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3897 :
    ((82679623/10000000 : ℚ) : ℝ) ≤ Real.log (3897 : ℕ)
      ∧ Real.log (3897 : ℕ) ≤ ((826796231/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3898 :
    ((826821887/100000000 : ℚ) : ℝ) ≤ Real.log (3898 : ℕ)
      ∧ Real.log (3898 : ℕ) ≤ ((82682189/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3899 :
    ((413423769/50000000 : ℚ) : ℝ) ≤ Real.log (3899 : ℕ)
      ∧ Real.log (3899 : ℕ) ≤ ((826847539/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3900 :
    ((826873183/100000000 : ℚ) : ℝ) ≤ Real.log (3900 : ℕ)
      ∧ Real.log (3900 : ℕ) ≤ ((25839787/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3901 :
    ((826898819/100000000 : ℚ) : ℝ) ≤ Real.log (3901 : ℕ)
      ∧ Real.log (3901 : ℕ) ≤ ((413449411/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3902 :
    ((206731113/25000000 : ℚ) : ℝ) ≤ Real.log (3902 : ℕ)
      ∧ Real.log (3902 : ℕ) ≤ ((826924453/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3903 :
    ((206737519/25000000 : ℚ) : ℝ) ≤ Real.log (3903 : ℕ)
      ∧ Real.log (3903 : ℕ) ≤ ((826950077/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3904 :
    ((413487847/50000000 : ℚ) : ℝ) ≤ Real.log (3904 : ℕ)
      ∧ Real.log (3904 : ℕ) ≤ ((165395139/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3905 :
    ((413500653/50000000 : ℚ) : ℝ) ≤ Real.log (3905 : ℕ)
      ∧ Real.log (3905 : ℕ) ≤ ((827001307/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3906 :
    ((827026911/100000000 : ℚ) : ℝ) ≤ Real.log (3906 : ℕ)
      ∧ Real.log (3906 : ℕ) ≤ ((25844591/3125000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3907 :
    ((827052509/100000000 : ℚ) : ℝ) ≤ Real.log (3907 : ℕ)
      ∧ Real.log (3907 : ℕ) ≤ ((82705251/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3908 :
    ((827078101/100000000 : ℚ) : ℝ) ≤ Real.log (3908 : ℕ)
      ∧ Real.log (3908 : ℕ) ≤ ((413539051/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3909 :
    ((413551843/50000000 : ℚ) : ℝ) ≤ Real.log (3909 : ℕ)
      ∧ Real.log (3909 : ℕ) ≤ ((827103687/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3910 :
    ((165425853/20000000 : ℚ) : ℝ) ≤ Real.log (3910 : ℕ)
      ∧ Real.log (3910 : ℕ) ≤ ((413564633/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3911 :
    ((827154837/100000000 : ℚ) : ℝ) ≤ Real.log (3911 : ℕ)
      ∧ Real.log (3911 : ℕ) ≤ ((413577419/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3912 :
    ((827180403/100000000 : ℚ) : ℝ) ≤ Real.log (3912 : ℕ)
      ∧ Real.log (3912 : ℕ) ≤ ((206795101/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3913 :
    ((413602981/50000000 : ℚ) : ℝ) ≤ Real.log (3913 : ℕ)
      ∧ Real.log (3913 : ℕ) ≤ ((827205963/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3914 :
    ((413615757/50000000 : ℚ) : ℝ) ≤ Real.log (3914 : ℕ)
      ∧ Real.log (3914 : ℕ) ≤ ((165446303/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3915 :
    ((41362853/5000000 : ℚ) : ℝ) ≤ Real.log (3915 : ℕ)
      ∧ Real.log (3915 : ℕ) ≤ ((827257061/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3916 :
    ((4136413/500000 : ℚ) : ℝ) ≤ Real.log (3916 : ℕ)
      ∧ Real.log (3916 : ℕ) ≤ ((827282601/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3917 :
    ((827308133/100000000 : ℚ) : ℝ) ≤ Real.log (3917 : ℕ)
      ∧ Real.log (3917 : ℕ) ≤ ((413654067/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3918 :
    ((827333659/100000000 : ℚ) : ℝ) ≤ Real.log (3918 : ℕ)
      ∧ Real.log (3918 : ℕ) ≤ ((41366683/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3919 :
    ((827359179/100000000 : ℚ) : ℝ) ≤ Real.log (3919 : ℕ)
      ∧ Real.log (3919 : ℕ) ≤ ((41367959/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3920 :
    ((827384693/100000000 : ℚ) : ℝ) ≤ Real.log (3920 : ℕ)
      ∧ Real.log (3920 : ℕ) ≤ ((413692347/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3921 :
    ((4137051/500000 : ℚ) : ℝ) ≤ Real.log (3921 : ℕ)
      ∧ Real.log (3921 : ℕ) ≤ ((827410201/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3922 :
    ((8274357/1000000 : ℚ) : ℝ) ≤ Real.log (3922 : ℕ)
      ∧ Real.log (3922 : ℕ) ≤ ((827435701/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3923 :
    ((413730597/50000000 : ℚ) : ℝ) ≤ Real.log (3923 : ℕ)
      ∧ Real.log (3923 : ℕ) ≤ ((165492239/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3924 :
    ((413743341/50000000 : ℚ) : ℝ) ≤ Real.log (3924 : ℕ)
      ∧ Real.log (3924 : ℕ) ≤ ((827486683/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3925 :
    ((413756081/50000000 : ℚ) : ℝ) ≤ Real.log (3925 : ℕ)
      ∧ Real.log (3925 : ℕ) ≤ ((165502433/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3926 :
    ((827537637/100000000 : ℚ) : ℝ) ≤ Real.log (3926 : ℕ)
      ∧ Real.log (3926 : ℕ) ≤ ((413768819/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3927 :
    ((165512621/20000000 : ℚ) : ℝ) ≤ Real.log (3927 : ℕ)
      ∧ Real.log (3927 : ℕ) ≤ ((413781553/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3928 :
    ((413794283/50000000 : ℚ) : ℝ) ≤ Real.log (3928 : ℕ)
      ∧ Real.log (3928 : ℕ) ≤ ((827588567/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3929 :
    ((41380701/5000000 : ℚ) : ℝ) ≤ Real.log (3929 : ℕ)
      ∧ Real.log (3929 : ℕ) ≤ ((827614023/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3930 :
    ((82763947/10000000 : ℚ) : ℝ) ≤ Real.log (3930 : ℕ)
      ∧ Real.log (3930 : ℕ) ≤ ((827639471/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3931 :
    ((51729057/6250000 : ℚ) : ℝ) ≤ Real.log (3931 : ℕ)
      ∧ Real.log (3931 : ℕ) ≤ ((827664913/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3932 :
    ((206922587/25000000 : ℚ) : ℝ) ≤ Real.log (3932 : ℕ)
      ∧ Real.log (3932 : ℕ) ≤ ((827690349/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3933 :
    ((827715777/100000000 : ℚ) : ℝ) ≤ Real.log (3933 : ℕ)
      ∧ Real.log (3933 : ℕ) ≤ ((413857889/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3934 :
    ((827741199/100000000 : ℚ) : ℝ) ≤ Real.log (3934 : ℕ)
      ∧ Real.log (3934 : ℕ) ≤ ((2069353/250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3935 :
    ((103470827/12500000 : ℚ) : ℝ) ≤ Real.log (3935 : ℕ)
      ∧ Real.log (3935 : ℕ) ≤ ((827766617/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3936 :
    ((33111681/4000000 : ℚ) : ℝ) ≤ Real.log (3936 : ℕ)
      ∧ Real.log (3936 : ℕ) ≤ ((413896013/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3937 :
    ((827817429/100000000 : ℚ) : ℝ) ≤ Real.log (3937 : ℕ)
      ∧ Real.log (3937 : ℕ) ≤ ((82781743/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3938 :
    ((33113713/4000000 : ℚ) : ℝ) ≤ Real.log (3938 : ℕ)
      ∧ Real.log (3938 : ℕ) ≤ ((413921413/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3939 :
    ((103483527/12500000 : ℚ) : ℝ) ≤ Real.log (3939 : ℕ)
      ∧ Real.log (3939 : ℕ) ≤ ((827868217/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3940 :
    ((1034867/125000 : ℚ) : ℝ) ≤ Real.log (3940 : ℕ)
      ∧ Real.log (3940 : ℕ) ≤ ((827893601/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3941 :
    ((827918977/100000000 : ℚ) : ℝ) ≤ Real.log (3941 : ℕ)
      ∧ Real.log (3941 : ℕ) ≤ ((413959489/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3942 :
    ((206986087/25000000 : ℚ) : ℝ) ≤ Real.log (3942 : ℕ)
      ∧ Real.log (3942 : ℕ) ≤ ((827944349/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3943 :
    ((827969713/100000000 : ℚ) : ℝ) ≤ Real.log (3943 : ℕ)
      ∧ Real.log (3943 : ℕ) ≤ ((413984857/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3944 :
    ((827995071/100000000 : ℚ) : ℝ) ≤ Real.log (3944 : ℕ)
      ∧ Real.log (3944 : ℕ) ≤ ((12937423/1562500 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3945 :
    ((828020423/100000000 : ℚ) : ℝ) ≤ Real.log (3945 : ℕ)
      ∧ Real.log (3945 : ℕ) ≤ ((103502553/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3946 :
    ((103505721/12500000 : ℚ) : ℝ) ≤ Real.log (3946 : ℕ)
      ∧ Real.log (3946 : ℕ) ≤ ((828045769/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3947 :
    ((828071107/100000000 : ℚ) : ℝ) ≤ Real.log (3947 : ℕ)
      ∧ Real.log (3947 : ℕ) ≤ ((207017777/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3948 :
    ((20702411/2500000 : ℚ) : ℝ) ≤ Real.log (3948 : ℕ)
      ∧ Real.log (3948 : ℕ) ≤ ((828096441/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3949 :
    ((414060883/50000000 : ℚ) : ℝ) ≤ Real.log (3949 : ℕ)
      ∧ Real.log (3949 : ℕ) ≤ ((828121767/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3950 :
    ((165629417/20000000 : ℚ) : ℝ) ≤ Real.log (3950 : ℕ)
      ∧ Real.log (3950 : ℕ) ≤ ((414073543/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3951 :
    ((414086199/50000000 : ℚ) : ℝ) ≤ Real.log (3951 : ℕ)
      ∧ Real.log (3951 : ℕ) ≤ ((828172401/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3952 :
    ((165639541/20000000 : ℚ) : ℝ) ≤ Real.log (3952 : ℕ)
      ∧ Real.log (3952 : ℕ) ≤ ((414098853/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3953 :
    ((414111503/50000000 : ℚ) : ℝ) ≤ Real.log (3953 : ℕ)
      ∧ Real.log (3953 : ℕ) ≤ ((828223007/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3954 :
    ((8282483/1000000 : ℚ) : ℝ) ≤ Real.log (3954 : ℕ)
      ∧ Real.log (3954 : ℕ) ≤ ((828248301/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3955 :
    ((828273587/100000000 : ℚ) : ℝ) ≤ Real.log (3955 : ℕ)
      ∧ Real.log (3955 : ℕ) ≤ ((82827359/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3956 :
    ((828298869/100000000 : ℚ) : ℝ) ≤ Real.log (3956 : ℕ)
      ∧ Real.log (3956 : ℕ) ≤ ((82829887/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3957 :
    ((51770259/6250000 : ℚ) : ℝ) ≤ Real.log (3957 : ℕ)
      ∧ Real.log (3957 : ℕ) ≤ ((165664829/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3958 :
    ((207087353/25000000 : ℚ) : ℝ) ≤ Real.log (3958 : ℕ)
      ∧ Real.log (3958 : ℕ) ≤ ((828349413/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3959 :
    ((414187337/50000000 : ℚ) : ℝ) ≤ Real.log (3959 : ℕ)
      ∧ Real.log (3959 : ℕ) ≤ ((33134987/4000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3960 :
    ((82839993/10000000 : ℚ) : ℝ) ≤ Real.log (3960 : ℕ)
      ∧ Real.log (3960 : ℕ) ≤ ((828399931/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3961 :
    ((828425179/100000000 : ℚ) : ℝ) ≤ Real.log (3961 : ℕ)
      ∧ Real.log (3961 : ℕ) ≤ ((41421259/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3962 :
    ((414225211/50000000 : ℚ) : ℝ) ≤ Real.log (3962 : ℕ)
      ∧ Real.log (3962 : ℕ) ≤ ((828450423/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3963 :
    ((828475659/100000000 : ℚ) : ℝ) ≤ Real.log (3963 : ℕ)
      ∧ Real.log (3963 : ℕ) ≤ ((41423783/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3964 :
    ((828500889/100000000 : ℚ) : ℝ) ≤ Real.log (3964 : ℕ)
      ∧ Real.log (3964 : ℕ) ≤ ((82850089/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3965 :
    ((828526113/100000000 : ℚ) : ℝ) ≤ Real.log (3965 : ℕ)
      ∧ Real.log (3965 : ℕ) ≤ ((414263057/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3966 :
    ((82855133/10000000 : ℚ) : ℝ) ≤ Real.log (3966 : ℕ)
      ∧ Real.log (3966 : ℕ) ≤ ((828551331/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3967 :
    ((414288271/50000000 : ℚ) : ℝ) ≤ Real.log (3967 : ℕ)
      ∧ Real.log (3967 : ℕ) ≤ ((828576543/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3968 :
    ((414300873/50000000 : ℚ) : ℝ) ≤ Real.log (3968 : ℕ)
      ∧ Real.log (3968 : ℕ) ≤ ((828601747/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3969 :
    ((165725389/20000000 : ℚ) : ℝ) ≤ Real.log (3969 : ℕ)
      ∧ Real.log (3969 : ℕ) ≤ ((414313473/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3970 :
    ((828652137/100000000 : ℚ) : ℝ) ≤ Real.log (3970 : ℕ)
      ∧ Real.log (3970 : ℕ) ≤ ((414326069/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3971 :
    ((828677323/100000000 : ℚ) : ℝ) ≤ Real.log (3971 : ℕ)
      ∧ Real.log (3971 : ℕ) ≤ ((207169331/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3972 :
    ((414351251/50000000 : ℚ) : ℝ) ≤ Real.log (3972 : ℕ)
      ∧ Real.log (3972 : ℕ) ≤ ((828702503/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3973 :
    ((33149107/4000000 : ℚ) : ℝ) ≤ Real.log (3973 : ℕ)
      ∧ Real.log (3973 : ℕ) ≤ ((207181919/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3974 :
    ((414376421/50000000 : ℚ) : ℝ) ≤ Real.log (3974 : ℕ)
      ∧ Real.log (3974 : ℕ) ≤ ((828752843/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3975 :
    ((414389001/50000000 : ℚ) : ℝ) ≤ Real.log (3975 : ℕ)
      ∧ Real.log (3975 : ℕ) ≤ ((828778003/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3976 :
    ((207200789/25000000 : ℚ) : ℝ) ≤ Real.log (3976 : ℕ)
      ∧ Real.log (3976 : ℕ) ≤ ((828803157/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3977 :
    ((51801769/6250000 : ℚ) : ℝ) ≤ Real.log (3977 : ℕ)
      ∧ Real.log (3977 : ℕ) ≤ ((165765661/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3978 :
    ((165770689/20000000 : ℚ) : ℝ) ≤ Real.log (3978 : ℕ)
      ∧ Real.log (3978 : ℕ) ≤ ((414426723/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3979 :
    ((828878581/100000000 : ℚ) : ℝ) ≤ Real.log (3979 : ℕ)
      ∧ Real.log (3979 : ℕ) ≤ ((414439291/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3980 :
    ((828903709/100000000 : ℚ) : ℝ) ≤ Real.log (3980 : ℕ)
      ∧ Real.log (3980 : ℕ) ≤ ((82890371/10000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3981 :
    ((12952013/1562500 : ℚ) : ℝ) ≤ Real.log (3981 : ℕ)
      ∧ Real.log (3981 : ℕ) ≤ ((828928833/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3982 :
    ((207238487/25000000 : ℚ) : ℝ) ≤ Real.log (3982 : ℕ)
      ∧ Real.log (3982 : ℕ) ≤ ((828953949/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3983 :
    ((414489529/50000000 : ℚ) : ℝ) ≤ Real.log (3983 : ℕ)
      ∧ Real.log (3983 : ℕ) ≤ ((828979059/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3984 :
    ((829004161/100000000 : ℚ) : ℝ) ≤ Real.log (3984 : ℕ)
      ∧ Real.log (3984 : ℕ) ≤ ((414502081/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3985 :
    ((829029259/100000000 : ℚ) : ℝ) ≤ Real.log (3985 : ℕ)
      ∧ Real.log (3985 : ℕ) ≤ ((41451463/5000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3986 :
    ((16581087/2000000 : ℚ) : ℝ) ≤ Real.log (3986 : ℕ)
      ∧ Real.log (3986 : ℕ) ≤ ((829054351/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3987 :
    ((414539717/50000000 : ℚ) : ℝ) ≤ Real.log (3987 : ℕ)
      ∧ Real.log (3987 : ℕ) ≤ ((165815887/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3988 :
    ((829104513/100000000 : ℚ) : ℝ) ≤ Real.log (3988 : ℕ)
      ∧ Real.log (3988 : ℕ) ≤ ((414552257/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3989 :
    ((165825917/20000000 : ℚ) : ℝ) ≤ Real.log (3989 : ℕ)
      ∧ Real.log (3989 : ℕ) ≤ ((414564793/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3990 :
    ((829154649/100000000 : ℚ) : ℝ) ≤ Real.log (3990 : ℕ)
      ∧ Real.log (3990 : ℕ) ≤ ((207288663/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3991 :
    ((82917971/10000000 : ℚ) : ℝ) ≤ Real.log (3991 : ℕ)
      ∧ Real.log (3991 : ℕ) ≤ ((829179711/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3992 :
    ((829204763/100000000 : ℚ) : ℝ) ≤ Real.log (3992 : ℕ)
      ∧ Real.log (3992 : ℕ) ≤ ((207301191/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3993 :
    ((82922981/10000000 : ℚ) : ℝ) ≤ Real.log (3993 : ℕ)
      ∧ Real.log (3993 : ℕ) ≤ ((829229811/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3994 :
    ((829254851/100000000 : ℚ) : ℝ) ≤ Real.log (3994 : ℕ)
      ∧ Real.log (3994 : ℕ) ≤ ((207313713/25000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3995 :
    ((165855977/20000000 : ℚ) : ℝ) ≤ Real.log (3995 : ℕ)
      ∧ Real.log (3995 : ℕ) ≤ ((414639943/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3996 :
    ((51831557/6250000 : ℚ) : ℝ) ≤ Real.log (3996 : ℕ)
      ∧ Real.log (3996 : ℕ) ≤ ((165860983/20000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3997 :
    ((165865987/20000000 : ℚ) : ℝ) ≤ Real.log (3997 : ℕ)
      ∧ Real.log (3997 : ℕ) ≤ ((51833121/6250000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3998 :
    ((829354951/100000000 : ℚ) : ℝ) ≤ Real.log (3998 : ℕ)
      ∧ Real.log (3998 : ℕ) ≤ ((103669369/12500000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_3999 :
    ((20734499/2500000 : ℚ) : ℝ) ≤ Real.log (3999 : ℕ)
      ∧ Real.log (3999 : ℕ) ≤ ((829379961/100000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_4000 :
    ((829404963/100000000 : ℚ) : ℝ) ≤ Real.log (4000 : ℕ)
      ∧ Real.log (4000 : ℕ) ≤ ((414702483/50000000 : ℚ) : ℝ) :=
  log_bracket 8 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_br_4000
end AxiomAudit
