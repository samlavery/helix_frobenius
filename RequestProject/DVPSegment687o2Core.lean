import RequestProject.DVPCos687o2Psum
import RequestProject.DVPSegment126Core

/-!
# The segment core at `t = 687/2` (rung-343.5; N = 500)

The single Euler–Maclaurin extraction all seven σ-intervals consume:

`Re ζ(σ+(687/2)i) ≥ 1 + ∑_{n=2}^{500} n^{−σ}·cos(687·(log n)/2)
  − 500^{−σ}·(1000/687 + 1/2) − 14966·(500^{−σ−2} + 500^{−σ−1}/(σ+1))`

for `1/2 ≤ σ ≤ 2`.  The `rpow_neg_anti` helper is imported from the
integer core.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 16384 in
/-- **The segment core bound at the half-integer anchor.** -/
theorem re_zeta687o2_lower {σ : ℝ} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 2) :
    1 + (∑ n ∈ Finset.Icc (2:ℕ) 500, ((n : ℝ) ^ (-σ) * cos687o2c n))
      - (500 : ℝ) ^ (-σ) * (1000/687 + 1/2)
      - 14966 * ((500 : ℝ) ^ (-σ - 2) + (500 : ℝ) ^ (-σ - 1) / (σ + 1))
    ≤ (riemannZeta (↑σ + ↑((((687:ℕ)):ℝ)/2) * Complex.I)).re := by
  set s : ℂ := ↑σ + ↑((((687:ℕ)):ℝ)/2) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hsim : s.im = ((687:ℕ):ℝ)/2 := by rw [hsdef]; simp
  have hσ0 : 0 < s.re := by rw [hsre]; linarith
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    rw [hsim] at him
    norm_num at him
  have hEM := zeta_EM_enclosure_numeric (N := 500) (by norm_num) hσ0 hs1
  set EMval : ℂ := (∑ n ∈ Finset.range (500 + 1), (((n : ℝ)) : ℂ) ^ (-s))
      + (((500 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)
      - (((500 : ℕ) : ℝ) : ℂ) ^ (-s) / 2 with hEMdef
  have habs := Complex.abs_re_le_norm (riemannZeta s - EMval)
  have hsubre : (riemannZeta s - EMval).re
      = (riemannZeta s).re - EMval.re := by simp
  have hre_ge : EMval.re - ‖riemannZeta s - EMval‖ ≤ (riemannZeta s).re := by
    rw [hsubre] at habs
    have := abs_le.mp habs
    linarith [this.1]
  have hprod : ‖s‖ * ‖s + 1‖ ≤ 478863/4 := by
    have hns : ‖s‖ ≤ 691/2 := by
      calc ‖s‖ ≤ ‖(↑σ : ℂ)‖ + ‖↑((((687:ℕ)):ℝ)/2) * Complex.I‖ := by
            rw [hsdef]; exact norm_add_le _ _
        _ = |σ| + 687/2 := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul,
              Complex.norm_I, mul_one]
            norm_num
        _ ≤ 691/2 := by
            rw [abs_of_pos (by linarith)]
            linarith
    have hns1 : ‖s + 1‖ ≤ 693/2 := by
      calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 693/2 := by rw [norm_one]; linarith
    calc ‖s‖ * ‖s + 1‖ ≤ (691/2) * (693/2) :=
          mul_le_mul hns hns1 (norm_nonneg _) (by norm_num)
      _ = 478863/4 := by norm_num
  have herr : ‖s‖ * ‖s + 1‖ * (1/8)
      * ((((500 : ℕ) : ℝ)) ^ (-s.re - 2)
        + (((500 : ℕ) : ℝ)) ^ (-s.re - 1) / (s.re + 1))
      ≤ 14966 * ((500 : ℝ) ^ (-σ - 2) + (500 : ℝ) ^ (-σ - 1) / (σ + 1)) := by
    have hcast : ((500 : ℕ) : ℝ) = (500 : ℝ) := by norm_num
    rw [hcast, hsre]
    have hX : (0:ℝ) ≤ (500 : ℝ) ^ (-σ - 2)
        + (500 : ℝ) ^ (-σ - 1) / (σ + 1) := by
      have hr1 := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 500) (-σ - 2)
      have hr2 := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 500) (-σ - 1)
      have hd : (0:ℝ) < σ + 1 := by linarith
      positivity
    nlinarith [hprod, hX, norm_nonneg s, norm_nonneg (s + 1),
      mul_nonneg (norm_nonneg s) (norm_nonneg (s + 1))]
  have hhead_re : (∑ n ∈ Finset.range (500 + 1), (((n : ℝ)) : ℂ) ^ (-s)).re
      = 1 + ∑ n ∈ Finset.Icc (2:ℕ) 500, ((n : ℝ) ^ (-σ) * cos687o2c n) := by
    rw [Complex.re_sum]
    have hset : Finset.range (500 + 1)
        = insert 0 (insert 1 (Finset.Icc (2:ℕ) 500)) := by decide
    rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
    have h0re : (((((0:ℕ) : ℝ)) : ℂ) ^ (-s)).re = 0 := by
      have hterm0 : ((((0:ℕ) : ℝ)) : ℂ) ^ (-s) = 0 := by
        rw [show ((((0:ℕ) : ℝ)) : ℂ) = 0 by norm_num]
        refine Complex.zero_cpow ?_
        intro h
        have hs0 : s = 0 := neg_eq_zero.mp h
        rw [hs0] at hsim
        norm_num at hsim
      rw [hterm0]
      simp
    have h1re : (((((1:ℕ) : ℝ)) : ℂ) ^ (-s)).re = 1 := by
      have hterm1 : ((((1:ℕ) : ℝ)) : ℂ) ^ (-s) = 1 := by
        rw [show ((((1:ℕ) : ℝ)) : ℂ) = 1 by norm_num]
        exact Complex.one_cpow _
      rw [hterm1]
      simp
    rw [h0re, h1re]
    have hcong : ∑ n ∈ Finset.Icc (2:ℕ) 500, ((((n : ℝ)) : ℂ) ^ (-s)).re
        = ∑ n ∈ Finset.Icc (2:ℕ) 500, ((n : ℝ) ^ (-σ) * cos687o2c n) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have h687 : -s = -(↑σ + ↑((((687:ℕ)):ℝ)/2) * Complex.I) := by
        rw [hsdef]
      rw [h687, (nat_cpow_neg_split (n := n) (by omega) σ ((((687:ℕ)):ℝ)/2)).1]
      rw [show ((((687:ℕ)):ℝ)/2) * Real.log ((n:ℕ))
          = (((687:ℕ)):ℝ) * (Real.log ((n:ℕ)) / 2) by ring]
      simp only [cos687o2c]
    rw [hcong]
    ring
  have hbdy : ‖(((500 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1)‖
      ≤ (500 : ℝ) ^ (-σ) * (1000/687) := by
    rw [norm_div]
    have hb1 : ‖(((500 : ℕ) : ℝ) : ℂ) ^ (1 - s)‖
        = ((500 : ℕ) : ℝ) ^ ((1 - s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
    have hre1s : (1 - s).re = 1 - σ := by
      simp [hsre]
    have hb2 : ((500 : ℕ) : ℝ) ^ ((1 - s).re) = (500 : ℝ) ^ (1 - σ) := by
      rw [hre1s]
      norm_num
    have hsplitp : (500 : ℝ) ^ (1 - σ) = 500 * (500 : ℝ) ^ (-σ) := by
      rw [show (1 - σ) = 1 + (-σ) by ring,
        Real.rpow_add (by norm_num : (0:ℝ) < 500), Real.rpow_one]
    have hden : (687/2 : ℝ) ≤ ‖s - 1‖ := by
      have habsim := Complex.abs_im_le_norm (s - 1)
      have him : (s - 1).im = ((687:ℕ):ℝ)/2 := by simp [hsim]
      rw [him] at habsim
      calc (687/2 : ℝ) = |((687:ℕ):ℝ)/2| := by norm_num
        _ ≤ ‖s - 1‖ := habsim
    have hnum0 : (0:ℝ) ≤ 500 * (500 : ℝ) ^ (-σ) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 500) (-σ)
      positivity
    calc ‖(((500 : ℕ) : ℝ) : ℂ) ^ (1 - s)‖ / ‖s - 1‖
        = (500 * (500 : ℝ) ^ (-σ)) / ‖s - 1‖ := by
          rw [hb1, hb2, hsplitp]
      _ ≤ (500 * (500 : ℝ) ^ (-σ)) / (687/2) :=
          div_le_div_of_nonneg_left hnum0 (by norm_num) hden
      _ = (500 : ℝ) ^ (-σ) * (1000/687) := by ring
  have hhalf : ‖(((500 : ℕ) : ℝ) : ℂ) ^ (-s) / 2‖
      ≤ (500 : ℝ) ^ (-σ) * (1/2) := by
    rw [norm_div]
    have hb1 : ‖(((500 : ℕ) : ℝ) : ℂ) ^ (-s)‖
        = ((500 : ℕ) : ℝ) ^ ((-s).re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
    have hres : (-s).re = -σ := by simp [hsre]
    rw [hb1, hres]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    have hc : ((500 : ℕ) : ℝ) = (500 : ℝ) := by norm_num
    rw [hc]
    linarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 500) (-σ)]
  have hEMre : (1 + ∑ n ∈ Finset.Icc (2:ℕ) 500, ((n : ℝ) ^ (-σ) * cos687o2c n))
      - (500 : ℝ) ^ (-σ) * (1000/687) - (500 : ℝ) ^ (-σ) * (1/2)
      ≤ EMval.re := by
    rw [hEMdef]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hhead_re]
    have hb := Complex.abs_re_le_norm
      ((((500 : ℕ) : ℝ) : ℂ) ^ (1 - s) / (s - 1))
    have hh := Complex.abs_re_le_norm ((((500 : ℕ) : ℝ) : ℂ) ^ (-s) / 2)
    have hb' := abs_le.mp hb
    have hh' := abs_le.mp hh
    linarith [hb'.1, hh'.2, hbdy, hhalf]
  have hEMbound := le_trans hEM herr
  have hgoal := le_trans (by linarith [hEMre, hEMbound] :
      (1 + ∑ n ∈ Finset.Icc (2:ℕ) 500, ((n : ℝ) ^ (-σ) * cos687o2c n))
        - (500 : ℝ) ^ (-σ) * (1000/687 + 1/2)
        - 14966 * ((500 : ℝ) ^ (-σ - 2) + (500 : ℝ) ^ (-σ - 1) / (σ + 1))
      ≤ EMval.re - ‖riemannZeta s - EMval‖) hre_ge
  linarith [hgoal]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.re_zeta687o2_lower
end AxiomAudit
