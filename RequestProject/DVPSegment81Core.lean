import RequestProject.DVPCos81Psum
import RequestProject.DVPWeights58

/-!
# The segment core at `t = 81` (rung-74)

The single Euler–Maclaurin extraction all six σ-intervals consume:

`Re ζ(σ+58i) ≥ 1 + ∑_{n=2}^{100} n^{−σ}·cos(58 log n)
  − 100^{−σ}·(100/81 + 1/2) − 458·(100^{−σ−2} + 100^{−σ−1}/(σ+1))`

for `1/2 ≤ σ ≤ 2` — plus the antitone-weight helper for the Abel tail.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- Antitonicity of `x ↦ x^{−σ}` on `[1, ∞)` for `σ ≥ 0`. -/
theorem rpow_neg_anti {x y σ : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hσ : 0 ≤ σ) :
    y ^ (-σ) ≤ x ^ (-σ) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le hx0 hxy
  rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
  have h1 : x ^ σ ≤ y ^ σ := Real.rpow_le_rpow hx0.le hxy hσ
  have h2 : (0:ℝ) < x ^ σ := Real.rpow_pos_of_pos hx0 _
  exact inv_anti₀ h2 h1

/-- **The segment core bound.** -/
theorem re_zeta81_lower {σ : ℝ} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 2) :
    1 + (∑ n ∈ Finset.Icc (2:ℕ) 100, ((n : ℝ) ^ (-σ) * cos81c n))
      - (100 : ℝ) ^ (-σ) * (100/81 + 1/2)
      - 872 * ((100 : ℝ) ^ (-σ - 2) + (100 : ℝ) ^ (-σ - 1) / (σ + 1))
    ≤ (riemannZeta (↑σ + ((81:ℕ):ℝ) * Complex.I)).re := by
  set s : ℂ := ↑σ + ((81:ℕ):ℝ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = 81 := by rw [hsdef]; simp
  have hσ0 : 0 < s.re := by rw [hsre]; linarith
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    rw [hsim] at him
    simp at him
  have hEM := zeta_EM_enclosure_numeric (N := 100) (by norm_num) hσ0 hs1
  set EMval : ℂ := (∑ n ∈ Finset.range (100 + 1), (((n : ℝ)) : ℂ) ^ (-s))
      + (((100 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      - (((100 : ℕ) : ℝ) : ℂ) ^ (-s) / 2 with hEMdef
  -- re ζ from re EMval and the enclosure
  have habs := Complex.abs_re_le_norm (riemannZeta s - EMval)
  have hsubre : (riemannZeta s - EMval).re
      = (riemannZeta s).re - EMval.re := by simp
  have hre_ge : EMval.re - ‖riemannZeta s - EMval‖ ≤ (riemannZeta s).re := by
    rw [hsubre] at habs
    have := abs_le.mp habs
    linarith [this.1]
  -- the error majorant
  have hprod : ‖s‖ * ‖s + 1‖ ≤ 6972 := by
    have hns : ‖s‖ ≤ 83 := by
      calc ‖s‖ ≤ ‖(↑σ : ℂ)‖ + ‖(((81:ℕ):ℝ) : ℂ) * Complex.I‖ := by
            rw [hsdef]; exact norm_add_le _ _
        _ = |σ| + 81 := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
              Complex.norm_I, mul_one]
            norm_num
        _ ≤ 83 := by
            rw [abs_of_pos (by linarith)]
            linarith
    have hns1 : ‖s + 1‖ ≤ 84 := by
      calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 84 := by rw [norm_one]; linarith
    calc ‖s‖ * ‖s + 1‖ ≤ 83 * 84 :=
          mul_le_mul hns hns1 (norm_nonneg _) (by norm_num)
      _ = 6972 := by norm_num
  have herr : ‖s‖ * ‖s + 1‖ * (1/8)
      * ((((100 : ℕ) : ℝ)) ^ (-s.re - 2)
        + (((100 : ℕ) : ℝ)) ^ (-s.re - 1) / (s.re + 1))
      ≤ 872 * ((100 : ℝ) ^ (-σ - 2) + (100 : ℝ) ^ (-σ - 1) / (σ + 1)) := by
    have hcast : ((100 : ℕ) : ℝ) = (100 : ℝ) := by norm_num
    rw [hcast, hsre]
    have hX : (0:ℝ) ≤ (100 : ℝ) ^ (-σ - 2)
        + (100 : ℝ) ^ (-σ - 1) / (σ + 1) := by
      have hr1 := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 100) (-σ - 2)
      have hr2 := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 100) (-σ - 1)
      have hd : (0:ℝ) < σ + 1 := by linarith
      positivity
    nlinarith [hprod, hX, norm_nonneg s, norm_nonneg (s + 1),
      mul_nonneg (norm_nonneg s) (norm_nonneg (s + 1))]
  -- the head real part
  have hhead_re : (∑ n ∈ Finset.range (100 + 1), (((n : ℝ)) : ℂ) ^ (-s)).re
      = 1 + ∑ n ∈ Finset.Icc (2:ℕ) 100, ((n : ℝ) ^ (-σ) * cos81c n) := by
    rw [Complex.re_sum]
    have hset : Finset.range (100 + 1)
        = insert 0 (insert 1 (Finset.Icc (2:ℕ) 100)) := by decide
    rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
    have h0re : (((((0:ℕ) : ℝ)) : ℂ) ^ (-s)).re = 0 := by
      have hterm0 : ((((0:ℕ) : ℝ)) : ℂ) ^ (-s) = 0 := by
        rw [show ((((0:ℕ) : ℝ)) : ℂ) = 0 by norm_num]
        refine Complex.zero_cpow ?_
        intro h
        have hs0 : s = 0 := neg_eq_zero.mp h
        rw [hs0] at hsim
        simp at hsim
      rw [hterm0]
      simp
    have h1re : (((((1:ℕ) : ℝ)) : ℂ) ^ (-s)).re = 1 := by
      have hterm1 : ((((1:ℕ) : ℝ)) : ℂ) ^ (-s) = 1 := by
        rw [show ((((1:ℕ) : ℝ)) : ℂ) = 1 by norm_num]
        exact Complex.one_cpow _
      rw [hterm1]
      simp
    rw [h0re, h1re]
    have hcong : ∑ n ∈ Finset.Icc (2:ℕ) 100, ((((n : ℝ)) : ℂ) ^ (-s)).re
        = ∑ n ∈ Finset.Icc (2:ℕ) 100, ((n : ℝ) ^ (-σ) * cos81c n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have h81 : -s = -(↑σ + ↑(((81:ℕ)):ℝ) * Complex.I) := by
        rw [hsdef]
      rw [h81, (nat_cpow_neg_split (n := n) (by omega) σ (((81:ℕ)):ℝ)).1]
      simp only [cos81c]
    rw [hcong]
    ring
  -- the boundary term
  have hbdy : ‖(((100 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ (100 : ℝ) ^ (-σ) * (100/81) := by
    rw [norm_div]
    have hb1 : ‖(((100 : ℕ) : ℝ) : ℂ) ^ (1 - s)‖
        = ((100 : ℕ) : ℝ) ^ ((1 - s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
    have hre1s : (1 - s).re = 1 - σ := by
      simp [hsre]
    have hb2 : ((100 : ℕ) : ℝ) ^ ((1 - s).re) = (100 : ℝ) ^ (1 - σ) := by
      rw [hre1s]
      norm_num
    have hsplitp : (100 : ℝ) ^ (1 - σ) = 100 * (100 : ℝ) ^ (-σ) := by
      rw [show (1 - σ) = 1 + (-σ) by ring,
        Real.rpow_add (by norm_num : (0:ℝ) < 100), Real.rpow_one]
    have hden : (81 : ℝ) ≤ ‖s - 1‖ := by
      have habsim := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = 81 := by simp [hsim]
      rw [him] at habsim
      calc (81 : ℝ) = |(81 : ℝ)| := by norm_num
        _ ≤ ‖s - 1‖ := habsim
    have hnum0 : (0:ℝ) ≤ 100 * (100 : ℝ) ^ (-σ) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 100) (-σ)
      positivity
    calc ‖(((100 : ℕ) : ℝ) : ℂ) ^ (1 - s)‖ / ‖s - 1‖
        = (100 * (100 : ℝ) ^ (-σ)) / ‖s - 1‖ := by
          rw [hb1, hb2, hsplitp]
      _ ≤ (100 * (100 : ℝ) ^ (-σ)) / 81 :=
          div_le_div_of_nonneg_left hnum0 (by norm_num) hden
      _ = (100 : ℝ) ^ (-σ) * (100/81) := by ring
  -- the half term
  have hhalf : ‖(((100 : ℕ) : ℝ) : ℂ) ^ (-s) / 2‖
      ≤ (100 : ℝ) ^ (-σ) * (1/2) := by
    rw [norm_div]
    have hb1 : ‖(((100 : ℕ) : ℝ) : ℂ) ^ (-s)‖
        = ((100 : ℕ) : ℝ) ^ ((-s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
    have hres : (-s).re = -σ := by simp [hsre]
    rw [hb1, hres]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    have hc : ((100 : ℕ) : ℝ) = (100 : ℝ) := by norm_num
    rw [hc]
    linarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 100) (-σ)]
  -- re EMval from the three pieces
  have hEMre : (1 + ∑ n ∈ Finset.Icc (2:ℕ) 100, ((n : ℝ) ^ (-σ) * cos81c n))
      - (100 : ℝ) ^ (-σ) * (100/81) - (100 : ℝ) ^ (-σ) * (1/2)
      ≤ EMval.re := by
    rw [hEMdef]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hhead_re]
    have hb := Complex.abs_re_le_norm
      ((((100 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1))
    have hh := Complex.abs_re_le_norm ((((100 : ℕ) : ℝ) : ℂ) ^ (-s) / 2)
    have hb' := abs_le.mp hb
    have hh' := abs_le.mp hh
    linarith [hb'.1, hh'.2, hbdy, hhalf]
  -- assembly
  have hEMbound := le_trans hEM herr
  have hgoal := le_trans (by linarith [hEMre, hEMbound] :
      (1 + ∑ n ∈ Finset.Icc (2:ℕ) 100, ((n : ℝ) ^ (-σ) * cos81c n))
        - (100 : ℝ) ^ (-σ) * (100/81 + 1/2)
        - 872 * ((100 : ℝ) ^ (-σ - 2) + (100 : ℝ) ^ (-σ - 1) / (σ + 1))
      ≤ EMval.re - ‖riemannZeta s - EMval‖) hre_ge
  linarith [hgoal]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.rpow_neg_anti
#print axioms CriticalLinePhasor.DVP.re_zeta81_lower
end AxiomAudit
