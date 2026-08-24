import RequestProject.DVPLogBracket

/-!
# The `log n` bracket table, `n = 101..200` (rung-81 extension)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_101 :
    ((9230241/2000000 : ℚ) : ℝ) ≤ Real.log (101 : ℕ)
      ∧ Real.log (101 : ℕ) ≤ ((23075603/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_102 :
    ((361326/78125 : ℚ) : ℝ) ≤ Real.log (102 : ℕ)
      ∧ Real.log (102 : ℕ) ≤ ((46249729/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_103 :
    ((46347289/10000000 : ℚ) : ℝ) ≤ Real.log (103 : ℕ)
      ∧ Real.log (103 : ℕ) ≤ ((4634729/1000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_104 :
    ((11610977/2500000 : ℚ) : ℝ) ≤ Real.log (104 : ℕ)
      ∧ Real.log (104 : ℕ) ≤ ((46443909/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_105 :
    ((46539603/10000000 : ℚ) : ℝ) ≤ Real.log (105 : ℕ)
      ∧ Real.log (105 : ℕ) ≤ ((11634901/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_106 :
    ((4663439/1000000 : ℚ) : ℝ) ≤ Real.log (106 : ℕ)
      ∧ Real.log (106 : ℕ) ≤ ((46634391/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_107 :
    ((1460259/312500 : ℚ) : ℝ) ≤ Real.log (107 : ℕ)
      ∧ Real.log (107 : ℕ) ≤ ((46728289/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_108 :
    ((731583/156250 : ℚ) : ℝ) ≤ Real.log (108 : ℕ)
      ∧ Real.log (108 : ℕ) ≤ ((46821313/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_109 :
    ((23456739/5000000 : ℚ) : ℝ) ≤ Real.log (109 : ℕ)
      ∧ Real.log (109 : ℕ) ≤ ((46913479/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_110 :
    ((47004803/10000000 : ℚ) : ℝ) ≤ Real.log (110 : ℕ)
      ∧ Real.log (110 : ℕ) ≤ ((11751201/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_111 :
    ((23547651/5000000 : ℚ) : ℝ) ≤ Real.log (111 : ℕ)
      ∧ Real.log (111 : ℕ) ≤ ((47095303/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_112 :
    ((11796247/2500000 : ℚ) : ℝ) ≤ Real.log (112 : ℕ)
      ∧ Real.log (112 : ℕ) ≤ ((47184989/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_113 :
    ((23636939/5000000 : ℚ) : ℝ) ≤ Real.log (113 : ℕ)
      ∧ Real.log (113 : ℕ) ≤ ((47273879/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_114 :
    ((740031/156250 : ℚ) : ℝ) ≤ Real.log (114 : ℕ)
      ∧ Real.log (114 : ℕ) ≤ ((9472397/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_115 :
    ((47449321/10000000 : ℚ) : ℝ) ≤ Real.log (115 : ℕ)
      ∧ Real.log (115 : ℕ) ≤ ((23724661/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_116 :
    ((47535901/10000000 : ℚ) : ℝ) ≤ Real.log (116 : ℕ)
      ∧ Real.log (116 : ℕ) ≤ ((23767951/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_117 :
    ((47621739/10000000 : ℚ) : ℝ) ≤ Real.log (117 : ℕ)
      ∧ Real.log (117 : ℕ) ≤ ((2381087/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_118 :
    ((23853423/5000000 : ℚ) : ℝ) ≤ Real.log (118 : ℕ)
      ∧ Real.log (118 : ℕ) ≤ ((47706847/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_119 :
    ((23895617/5000000 : ℚ) : ℝ) ≤ Real.log (119 : ℕ)
      ∧ Real.log (119 : ℕ) ≤ ((9558247/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_120 :
    ((47874917/10000000 : ℚ) : ℝ) ≤ Real.log (120 : ℕ)
      ∧ Real.log (120 : ℕ) ≤ ((23937459/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_121 :
    ((9591581/2000000 : ℚ) : ℝ) ≤ Real.log (121 : ℕ)
      ∧ Real.log (121 : ℕ) ≤ ((23978953/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_122 :
    ((4804021/1000000 : ℚ) : ℝ) ≤ Real.log (122 : ℕ)
      ∧ Real.log (122 : ℕ) ≤ ((48040211/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_123 :
    ((48121843/10000000 : ℚ) : ℝ) ≤ Real.log (123 : ℕ)
      ∧ Real.log (123 : ℕ) ≤ ((12030461/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_124 :
    ((9640563/2000000 : ℚ) : ℝ) ≤ Real.log (124 : ℕ)
      ∧ Real.log (124 : ℕ) ≤ ((753169/156250 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_125 :
    ((48283137/10000000 : ℚ) : ℝ) ≤ Real.log (125 : ℕ)
      ∧ Real.log (125 : ℕ) ≤ ((24141569/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_126 :
    ((48362819/10000000 : ℚ) : ℝ) ≤ Real.log (126 : ℕ)
      ∧ Real.log (126 : ℕ) ≤ ((2418141/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_127 :
    ((4844187/1000000 : ℚ) : ℝ) ≤ Real.log (127 : ℕ)
      ∧ Real.log (127 : ℕ) ≤ ((48441871/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_128 :
    ((24260151/5000000 : ℚ) : ℝ) ≤ Real.log (128 : ℕ)
      ∧ Real.log (128 : ℕ) ≤ ((48520303/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_129 :
    ((12149531/2500000 : ℚ) : ℝ) ≤ Real.log (129 : ℕ)
      ∧ Real.log (129 : ℕ) ≤ ((77757/16000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_130 :
    ((3042209/625000 : ℚ) : ℝ) ≤ Real.log (130 : ℕ)
      ∧ Real.log (130 : ℕ) ≤ ((9735069/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_131 :
    ((48751973/10000000 : ℚ) : ℝ) ≤ Real.log (131 : ℕ)
      ∧ Real.log (131 : ℕ) ≤ ((24375987/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_132 :
    ((48828019/10000000 : ℚ) : ℝ) ≤ Real.log (132 : ℕ)
      ∧ Real.log (132 : ℕ) ≤ ((2441401/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_133 :
    ((48903491/10000000 : ℚ) : ℝ) ≤ Real.log (133 : ℕ)
      ∧ Real.log (133 : ℕ) ≤ ((12225873/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_134 :
    ((48978397/10000000 : ℚ) : ℝ) ≤ Real.log (134 : ℕ)
      ∧ Real.log (134 : ℕ) ≤ ((48978399/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_135 :
    ((49052747/10000000 : ℚ) : ℝ) ≤ Real.log (135 : ℕ)
      ∧ Real.log (135 : ℕ) ≤ ((12263187/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_136 :
    ((12281637/2500000 : ℚ) : ℝ) ≤ Real.log (136 : ℕ)
      ∧ Real.log (136 : ℕ) ≤ ((49126549/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_137 :
    ((49199809/10000000 : ℚ) : ℝ) ≤ Real.log (137 : ℕ)
      ∧ Real.log (137 : ℕ) ≤ ((4919981/1000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_138 :
    ((6159067/1250000 : ℚ) : ℝ) ≤ Real.log (138 : ℕ)
      ∧ Real.log (138 : ℕ) ≤ ((49272537/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_139 :
    ((49344739/10000000 : ℚ) : ℝ) ≤ Real.log (139 : ℕ)
      ∧ Real.log (139 : ℕ) ≤ ((2467237/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_140 :
    ((6177053/1250000 : ℚ) : ℝ) ≤ Real.log (140 : ℕ)
      ∧ Real.log (140 : ℕ) ≤ ((1976657/400000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_141 :
    ((24743799/5000000 : ℚ) : ℝ) ≤ Real.log (141 : ℕ)
      ∧ Real.log (141 : ℕ) ≤ ((49487599/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_142 :
    ((4955827/1000000 : ℚ) : ℝ) ≤ Real.log (142 : ℕ)
      ∧ Real.log (142 : ℕ) ≤ ((49558271/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_143 :
    ((24814223/5000000 : ℚ) : ℝ) ≤ Real.log (143 : ℕ)
      ∧ Real.log (143 : ℕ) ≤ ((49628447/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_144 :
    ((12424533/2500000 : ℚ) : ℝ) ≤ Real.log (144 : ℕ)
      ∧ Real.log (144 : ℕ) ≤ ((49698133/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_145 :
    ((49767337/10000000 : ℚ) : ℝ) ≤ Real.log (145 : ℕ)
      ∧ Real.log (145 : ℕ) ≤ ((24883669/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_146 :
    ((24918033/5000000 : ℚ) : ℝ) ≤ Real.log (146 : ℕ)
      ∧ Real.log (146 : ℕ) ≤ ((49836067/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_147 :
    ((1996173/400000 : ℚ) : ℝ) ≤ Real.log (147 : ℕ)
      ∧ Real.log (147 : ℕ) ≤ ((24952163/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_148 :
    ((24986061/5000000 : ℚ) : ℝ) ≤ Real.log (148 : ℕ)
      ∧ Real.log (148 : ℕ) ≤ ((49972123/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_149 :
    ((50039463/10000000 : ℚ) : ℝ) ≤ Real.log (149 : ℕ)
      ∧ Real.log (149 : ℕ) ≤ ((6254933/1250000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_150 :
    ((3131647/625000 : ℚ) : ℝ) ≤ Real.log (150 : ℕ)
      ∧ Real.log (150 : ℕ) ≤ ((50106353/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_151 :
    ((25086399/5000000 : ℚ) : ℝ) ≤ Real.log (151 : ℕ)
      ∧ Real.log (151 : ℕ) ≤ ((50172799/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_152 :
    ((10047761/2000000 : ℚ) : ℝ) ≤ Real.log (152 : ℕ)
      ∧ Real.log (152 : ℕ) ≤ ((25119403/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_153 :
    ((50304379/10000000 : ℚ) : ℝ) ≤ Real.log (153 : ℕ)
      ∧ Real.log (153 : ℕ) ≤ ((2515219/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_154 :
    ((25184763/5000000 : ℚ) : ℝ) ≤ Real.log (154 : ℕ)
      ∧ Real.log (154 : ℕ) ≤ ((50369527/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_155 :
    ((50434251/10000000 : ℚ) : ℝ) ≤ Real.log (155 : ℕ)
      ∧ Real.log (155 : ℕ) ≤ ((12608563/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_156 :
    ((78904/15625 : ℚ) : ℝ) ≤ Real.log (156 : ℕ)
      ∧ Real.log (156 : ℕ) ≤ ((50498561/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_157 :
    ((25281229/5000000 : ℚ) : ℝ) ≤ Real.log (157 : ℕ)
      ∧ Real.log (157 : ℕ) ≤ ((50562459/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_158 :
    ((1012519/200000 : ℚ) : ℝ) ≤ Real.log (158 : ℕ)
      ∧ Real.log (158 : ℕ) ≤ ((50625951/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_159 :
    ((25344521/5000000 : ℚ) : ℝ) ≤ Real.log (159 : ℕ)
      ∧ Real.log (159 : ℕ) ≤ ((50689043/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_160 :
    ((25375869/5000000 : ℚ) : ℝ) ≤ Real.log (160 : ℕ)
      ∧ Real.log (160 : ℕ) ≤ ((50751739/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_161 :
    ((50814043/10000000 : ℚ) : ℝ) ≤ Real.log (161 : ℕ)
      ∧ Real.log (161 : ℕ) ≤ ((12703511/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_162 :
    ((50875963/10000000 : ℚ) : ℝ) ≤ Real.log (162 : ℕ)
      ∧ Real.log (162 : ℕ) ≤ ((12718991/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_163 :
    ((25468751/5000000 : ℚ) : ℝ) ≤ Real.log (163 : ℕ)
      ∧ Real.log (163 : ℕ) ≤ ((50937503/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_164 :
    ((6374833/1250000 : ℚ) : ℝ) ≤ Real.log (164 : ℕ)
      ∧ Real.log (164 : ℕ) ≤ ((10199733/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_165 :
    ((25529727/5000000 : ℚ) : ℝ) ≤ Real.log (165 : ℕ)
      ∧ Real.log (165 : ℕ) ≤ ((10211891/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_166 :
    ((51119877/10000000 : ℚ) : ℝ) ≤ Real.log (166 : ℕ)
      ∧ Real.log (166 : ℕ) ≤ ((25559939/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_167 :
    ((25589969/5000000 : ℚ) : ℝ) ≤ Real.log (167 : ℕ)
      ∧ Real.log (167 : ℕ) ≤ ((51179939/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_168 :
    ((51239639/10000000 : ℚ) : ℝ) ≤ Real.log (168 : ℕ)
      ∧ Real.log (168 : ℕ) ≤ ((1280991/250000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_169 :
    ((51298987/10000000 : ℚ) : ℝ) ≤ Real.log (169 : ℕ)
      ∧ Real.log (169 : ℕ) ≤ ((12824747/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_170 :
    ((1604937/312500 : ℚ) : ℝ) ≤ Real.log (170 : ℕ)
      ∧ Real.log (170 : ℕ) ≤ ((10271597/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_171 :
    ((10283327/2000000 : ℚ) : ℝ) ≤ Real.log (171 : ℕ)
      ∧ Real.log (171 : ℕ) ≤ ((12854159/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_172 :
    ((402148/78125 : ℚ) : ℝ) ≤ Real.log (172 : ℕ)
      ∧ Real.log (172 : ℕ) ≤ ((10294989/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_173 :
    ((10306583/2000000 : ℚ) : ℝ) ≤ Real.log (173 : ℕ)
      ∧ Real.log (173 : ℕ) ≤ ((12883229/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_174 :
    ((6448819/1250000 : ℚ) : ℝ) ≤ Real.log (174 : ℕ)
      ∧ Real.log (174 : ℕ) ≤ ((51590553/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_175 :
    ((51647859/10000000 : ℚ) : ℝ) ≤ Real.log (175 : ℕ)
      ∧ Real.log (175 : ℕ) ≤ ((2582393/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_176 :
    ((51704839/10000000 : ℚ) : ℝ) ≤ Real.log (176 : ℕ)
      ∧ Real.log (176 : ℕ) ≤ ((1292621/250000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_177 :
    ((51761497/10000000 : ℚ) : ℝ) ≤ Real.log (177 : ℕ)
      ∧ Real.log (177 : ℕ) ≤ ((25880749/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_178 :
    ((10363567/2000000 : ℚ) : ℝ) ≤ Real.log (178 : ℕ)
      ∧ Real.log (178 : ℕ) ≤ ((12954459/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_179 :
    ((25936929/5000000 : ℚ) : ℝ) ≤ Real.log (179 : ℕ)
      ∧ Real.log (179 : ℕ) ≤ ((51873859/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_180 :
    ((1622799/312500 : ℚ) : ℝ) ≤ Real.log (180 : ℕ)
      ∧ Real.log (180 : ℕ) ≤ ((51929569/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_181 :
    ((5198497/1000000 : ℚ) : ℝ) ≤ Real.log (181 : ℕ)
      ∧ Real.log (181 : ℕ) ≤ ((51984971/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_182 :
    ((26020033/5000000 : ℚ) : ℝ) ≤ Real.log (182 : ℕ)
      ∧ Real.log (182 : ℕ) ≤ ((52040067/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_183 :
    ((52094861/10000000 : ℚ) : ℝ) ≤ Real.log (183 : ℕ)
      ∧ Real.log (183 : ℕ) ≤ ((26047431/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_184 :
    ((52149357/10000000 : ℚ) : ℝ) ≤ Real.log (184 : ℕ)
      ∧ Real.log (184 : ℕ) ≤ ((26074679/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_185 :
    ((26101779/5000000 : ℚ) : ℝ) ≤ Real.log (185 : ℕ)
      ∧ Real.log (185 : ℕ) ≤ ((52203559/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_186 :
    ((26128733/5000000 : ℚ) : ℝ) ≤ Real.log (186 : ℕ)
      ∧ Real.log (186 : ℕ) ≤ ((52257467/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_187 :
    ((26155543/5000000 : ℚ) : ℝ) ≤ Real.log (187 : ℕ)
      ∧ Real.log (187 : ℕ) ≤ ((52311087/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_188 :
    ((52364419/10000000 : ℚ) : ℝ) ≤ Real.log (188 : ℕ)
      ∧ Real.log (188 : ℕ) ≤ ((2618221/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_189 :
    ((5241747/1000000 : ℚ) : ℝ) ≤ Real.log (189 : ℕ)
      ∧ Real.log (189 : ℕ) ≤ ((52417471/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_190 :
    ((327939/62500 : ℚ) : ℝ) ≤ Real.log (190 : ℕ)
      ∧ Real.log (190 : ℕ) ≤ ((52470241/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_191 :
    ((26261367/5000000 : ℚ) : ℝ) ≤ Real.log (191 : ℕ)
      ∧ Real.log (191 : ℕ) ≤ ((10504547/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_192 :
    ((52574953/10000000 : ℚ) : ℝ) ≤ Real.log (192 : ℕ)
      ∧ Real.log (192 : ℕ) ≤ ((26287477/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_193 :
    ((52626901/10000000 : ℚ) : ℝ) ≤ Real.log (193 : ℕ)
      ∧ Real.log (193 : ℕ) ≤ ((26313451/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_194 :
    ((52678581/10000000 : ℚ) : ℝ) ≤ Real.log (194 : ℕ)
      ∧ Real.log (194 : ℕ) ≤ ((26339291/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_195 :
    ((10545999/2000000 : ℚ) : ℝ) ≤ Real.log (195 : ℕ)
      ∧ Real.log (195 : ℕ) ≤ ((13182499/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_196 :
    ((26390573/5000000 : ℚ) : ℝ) ≤ Real.log (196 : ℕ)
      ∧ Real.log (196 : ℕ) ≤ ((52781147/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_197 :
    ((52832037/10000000 : ℚ) : ℝ) ≤ Real.log (197 : ℕ)
      ∧ Real.log (197 : ℕ) ≤ ((26416019/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_198 :
    ((5288267/1000000 : ℚ) : ℝ) ≤ Real.log (198 : ℕ)
      ∧ Real.log (198 : ℕ) ≤ ((52882671/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_199 :
    ((6616631/1250000 : ℚ) : ℝ) ≤ Real.log (199 : ℕ)
      ∧ Real.log (199 : ℕ) ≤ ((52933049/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_200 :
    ((52983173/10000000 : ℚ) : ℝ) ≤ Real.log (200 : ℕ)
      ∧ Real.log (200 : ℕ) ≤ ((26491587/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_br_200
end AxiomAudit
