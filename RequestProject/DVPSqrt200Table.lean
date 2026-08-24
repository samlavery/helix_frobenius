import RequestProject.DVPSqrtTable

/-!
# `n^{−1/2}` brackets, `n = 101..200` (rung-81 extension)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem sq_br_101 :
    ((995037/10000000 : ℚ) : ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((497519/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_102 :
    ((990147/10000000 : ℚ) : ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((247537/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_103 :
    ((985329/10000000 : ℚ) : ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((98533/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_104 :
    ((49029/500000 : ℚ) : ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((980581/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_105 :
    ((9759/100000 : ℚ) : ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((975901/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_106 :
    ((194257/2000000 : ℚ) : ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((485643/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_107 :
    ((60421/625000 : ℚ) : ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((966737/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_108 :
    ((3849/40000 : ℚ) : ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((962251/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_109 :
    ((478913/5000000 : ℚ) : ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((957827/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_110 :
    ((476731/5000000 : ℚ) : ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((953463/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_111 :
    ((949157/10000000 : ℚ) : ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((474579/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_112 :
    ((944911/10000000 : ℚ) : ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((59057/625000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_113 :
    ((11759/125000 : ℚ) : ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((940721/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_114 :
    ((187317/2000000 : ℚ) : ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((468293/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_115 :
    ((116563/1250000 : ℚ) : ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((186501/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_116 :
    ((232119/2500000 : ℚ) : ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((928477/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_117 :
    ((1849/20000 : ℚ) : ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((924501/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_118 :
    ((460287/5000000 : ℚ) : ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((36823/400000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_119 :
    ((458349/5000000 : ℚ) : ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((916699/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_120 :
    ((91287/1000000 : ℚ) : ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((912871/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_121 :
    ((90909/1000000 : ℚ) : ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((909091/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_122 :
    ((905357/10000000 : ℚ) : ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((452679/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_123 :
    ((901669/10000000 : ℚ) : ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((90167/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_124 :
    ((449013/5000000 : ℚ) : ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((898027/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_125 :
    ((894427/10000000 : ℚ) : ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((223607/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_126 :
    ((89087/1000000 : ℚ) : ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((890871/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_127 :
    ((221839/2500000 : ℚ) : ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((887357/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_128 :
    ((883883/10000000 : ℚ) : ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((220971/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_129 :
    ((17609/200000 : ℚ) : ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((880451/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_130 :
    ((438529/5000000 : ℚ) : ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((877059/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_131 :
    ((109213/1250000 : ℚ) : ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((174741/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_132 :
    ((217597/2500000 : ℚ) : ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((870389/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_133 :
    ((867109/10000000 : ℚ) : ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((86711/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_134 :
    ((215967/2500000 : ℚ) : ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((863869/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_135 :
    ((430331/5000000 : ℚ) : ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((860663/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_136 :
    ((214373/2500000 : ℚ) : ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((857493/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_137 :
    ((854357/10000000 : ℚ) : ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((427179/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_138 :
    ((106407/1250000 : ℚ) : ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((851257/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_139 :
    ((212047/2500000 : ℚ) : ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((848189/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_140 :
    ((422577/5000000 : ℚ) : ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((169031/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_141 :
    ((842151/10000000 : ℚ) : ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((105269/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_142 :
    ((839181/10000000 : ℚ) : ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((419591/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_143 :
    ((418121/5000000 : ℚ) : ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((836243/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_144 :
    ((833333/10000000 : ℚ) : ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((416667/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_145 :
    ((415227/5000000 : ℚ) : ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((166091/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_146 :
    ((165521/2000000 : ℚ) : ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((413803/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_147 :
    ((412393/5000000 : ℚ) : ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((824787/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_148 :
    ((410997/5000000 : ℚ) : ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((164399/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_149 :
    ((819231/10000000 : ℚ) : ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((25601/312500 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_150 :
    ((51031/625000 : ℚ) : ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((816497/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_151 :
    ((203447/2500000 : ℚ) : ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((813789/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_152 :
    ((811107/10000000 : ℚ) : ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((202777/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_153 :
    ((202113/2500000 : ℚ) : ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((808453/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_154 :
    ((402911/5000000 : ℚ) : ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((805823/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_155 :
    ((803219/10000000 : ℚ) : ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((40161/500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_156 :
    ((1251/15625 : ℚ) : ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((800641/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_157 :
    ((399043/5000000 : ℚ) : ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((798087/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_158 :
    ((795557/10000000 : ℚ) : ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((397779/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_159 :
    ((793051/10000000 : ℚ) : ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((198263/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_160 :
    ((790569/10000000 : ℚ) : ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((79057/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_161 :
    ((78811/1000000 : ℚ) : ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((788111/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_162 :
    ((392837/5000000 : ℚ) : ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((31427/400000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_163 :
    ((39163/500000 : ℚ) : ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((783261/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_164 :
    ((195217/2500000 : ℚ) : ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((780869/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_165 :
    ((389249/5000000 : ℚ) : ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((778499/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_166 :
    ((15523/200000 : ℚ) : ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((776151/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_167 :
    ((773823/10000000 : ℚ) : ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((12091/156250 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_168 :
    ((192879/2500000 : ℚ) : ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((771517/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_169 :
    ((76923/1000000 : ℚ) : ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((769231/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_170 :
    ((191741/2500000 : ℚ) : ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((153393/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_171 :
    ((764719/10000000 : ℚ) : ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((9559/125000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_172 :
    ((190623/2500000 : ℚ) : ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((762493/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_173 :
    ((152057/2000000 : ℚ) : ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((380143/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_174 :
    ((379049/5000000 : ℚ) : ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((758099/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_175 :
    ((94491/1250000 : ℚ) : ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((755929/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_176 :
    ((376889/5000000 : ℚ) : ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((753779/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_177 :
    ((375823/5000000 : ℚ) : ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((751647/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_178 :
    ((749531/10000000 : ℚ) : ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((187383/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_179 :
    ((149487/2000000 : ℚ) : ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((186859/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_180 :
    ((149071/2000000 : ℚ) : ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((186339/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_181 :
    ((371647/5000000 : ℚ) : ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((148659/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_182 :
    ((741249/10000000 : ℚ) : ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((593/8000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_183 :
    ((739221/10000000 : ℚ) : ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((369611/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_184 :
    ((737209/10000000 : ℚ) : ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((73721/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_185 :
    ((367607/5000000 : ℚ) : ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((147043/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_186 :
    ((146647/2000000 : ℚ) : ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((183309/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_187 :
    ((91409/1250000 : ℚ) : ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((731273/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_188 :
    ((182331/2500000 : ℚ) : ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((29173/400000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_189 :
    ((22731/312500 : ℚ) : ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((727393/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_190 :
    ((181369/2500000 : ℚ) : ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((725477/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_191 :
    ((361787/5000000 : ℚ) : ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((28943/400000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_192 :
    ((721687/10000000 : ℚ) : ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((90211/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_193 :
    ((143963/2000000 : ℚ) : ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((89977/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_194 :
    ((358979/5000000 : ℚ) : ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((717959/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_195 :
    ((358057/5000000 : ℚ) : ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((143223/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_196 :
    ((142857/2000000 : ℚ) : ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((357143/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_197 :
    ((71247/1000000 : ℚ) : ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((712471/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_198 :
    ((710669/10000000 : ℚ) : ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((71067/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_199 :
    ((708881/10000000 : ℚ) : ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((354441/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_200 :
    ((353553/5000000 : ℚ) : ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((707107/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.sq_br_200
end AxiomAudit
