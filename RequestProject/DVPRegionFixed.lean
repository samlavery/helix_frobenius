import RequestProject.DVPWeightedCount

/-!
# The exponent-1 zero-free region at the FIXED center — threshold e⁴

The moving-center artifact removed (ledgers 336–338): every zero with
`|γ| ≥ e⁴ ≈ 55` obeys `β ≤ 1 − (1/50000)/log|γ|`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxHeartbeats 3200000 in
/-- The positive-ordinate exponent-1 region, FIXED-CENTER version:
threshold `e⁴` (the moving-center artifact removed, ledger 336–338). -/
theorem zero_free_region_exponent_one_aux' {ρ : ℂ}
    (hζρ : riemannZeta ρ = 0) (hT4 : Real.exp 4 ≤ ρ.im) :
    ρ.re ≤ 1 - (1/50000) / Real.log ρ.im := by
  set T : ℝ := ρ.im with hTdef
  set β : ℝ := ρ.re with hβdef
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 4) hT4
  have hL4 : (4:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 4) hT4
    rwa [Real.log_exp] at this
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  have hT50 : (50:ℝ) ≤ T := by
    have he2 : (7.38:ℝ) ≤ Real.exp 1 * Real.exp 1 := by
      nlinarith [Real.exp_one_gt_d9]
    have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1
        * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    nlinarith [he2, Real.exp_pos 1]
  have hβ1 : β < 1 := by
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re (by rw [← hβdef]; exact hc) hζρ
  by_cases hβtriv : β ≤ 1 - 3/32
  · have hc0 : (1/50000 : ℝ) / L ≤ 3/32 := by
      have h1 : (1/50000 : ℝ) / L ≤ (1/50000 : ℝ) / 4 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL4
      calc (1/50000 : ℝ) / L ≤ (1/50000 : ℝ) / 4 := h1
        _ ≤ 3/32 := by norm_num
    linarith
  push_neg at hβtriv
  set σ : ℝ := 1 + 1/(10000*L) with hσdef
  have hinv : (0:ℝ) < 1/(10000*L) := by positivity
  have hσ1 : 1 < σ := by
    rw [hσdef]
    linarith
  have hσ98 : σ ≤ 9/8 := by
    rw [hσdef]
    have : (1:ℝ)/(10000*L) ≤ 1/8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    linarith
  have hΦ0 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
      ≤ 10000*L + 3 := by
    rw [vonMangoldt_re_eq_neg_logDeriv (by simp; linarith)]
    have h1 := zeta_logDeriv_rung_sharp hσ1 hσ98
    have h2 : -(logDeriv riemannZeta ((σ:ℝ):ℂ)).re
        ≤ ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ := by
      have := Complex.abs_re_le_norm (logDeriv riemannZeta ((σ:ℝ):ℂ))
      have := neg_abs_le (logDeriv riemannZeta ((σ:ℝ):ℂ)).re
      linarith
    have h3 : 1/(σ-1) = 10000*L := by
      rw [hσdef, show (1 + 1/(10000*L) - 1) = 1/(10000*L) by ring,
        one_div_one_div]
    linarith
  obtain ⟨S, n, hS_mem, hcert, hcomp, hbound⟩ := zeta_partial_fraction_fixed hT4
  set c : ℂ := ((1 + 1/32 : ℝ) : ℂ) + T * Complex.I with hcdef
  set s₁ : ℂ := ((σ:ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I with hs₁def
  have hs₁re : s₁.re = σ := by
    rw [hs₁def]
    simp
  have hs₁im : s₁.im = T := by
    rw [hs₁def]
    simp
  have hζs₁ : riemannZeta s₁ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₁re]; exact hσ1)
  have hδ32 : (1:ℝ)/(10000*L) ≤ 1/32 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hs₁c : s₁ - c = (((σ - (1 + 1/32) : ℝ)):ℂ) := by
    rw [hs₁def, hcdef]
    push_cast
    ring
  have hs₁mem : s₁ ∈ Metric.closedBall c (1/32) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hs₁c, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor
    · rw [hσdef]
      linarith [hinv]
    · rw [hσdef]
      linarith [hδ32]
  have hb₁ := hbound s₁ hs₁mem hζs₁
  have hρc : ρ - c = (((β - (1 + 1/32) : ℝ)):ℂ) := by
    rw [hcdef]
    apply Complex.ext
    · simp [hβdef]
    · simp [hTdef]
  have hρmem : ρ ∈ Metric.closedBall c (1/8) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hρc, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor
    · linarith
    · linarith
  obtain ⟨hρS, hnρ⟩ := hcomp ρ hρmem hζρ
  have hure : ∀ u ∈ S, 1 ≤ n u → u.re < 1 := by
    intro u hu hnu
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re hc (hcert u hu hnu)
  have hterm_nonneg : ∀ u ∈ S,
      0 ≤ ((n u : ℂ) / (s₁ - u)).re := by
    intro u hu
    rcases Nat.eq_zero_or_pos (n u) with h0 | hpos
    · rw [h0]
      simp
    · have hlt := hure u hu hpos
      rw [pf_term_re]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply div_nonneg _ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hs₁re]
      linarith
  have hρ_term : 1/(σ - β) ≤ ((n ρ : ℂ) / (s₁ - ρ)).re := by
    have hs₁ρ : s₁ - ρ = (((σ - β : ℝ)):ℂ) := by
      apply Complex.ext
      · simp [hs₁re, hβdef]
      · simp [hs₁im, hTdef]
    rw [pf_term_re, hs₁ρ]
    rw [Complex.normSq_ofReal, Complex.ofReal_re]
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hval : (σ - β) / ((σ - β) * (σ - β)) = 1/(σ - β) := by
      field_simp
    rw [hval]
    have h1n : (1:ℝ) ≤ (n ρ : ℝ) := by exact_mod_cast hnρ
    nlinarith [one_div_pos.mpr hσβ]
  have hsum_ge : 1/(σ - β) ≤ (∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re := by
    rw [Complex.re_sum]
    calc 1/(σ - β) ≤ ((n ρ : ℂ) / (s₁ - ρ)).re := hρ_term
      _ ≤ ∑ u ∈ S, ((n u : ℂ) / (s₁ - u)).re :=
          Finset.single_le_sum hterm_nonneg hρS
  have hΦ1 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
      ≤ -(1/(σ - β)) + 300*L := by
    have hbr := vonMangoldt_re_eq_neg_logDeriv
      (s := s₁) (by rw [hs₁re]; exact hσ1)
    rw [hbr]
    have hsplit : -(logDeriv riemannZeta s₁).re
        = -((logDeriv riemannZeta s₁
            - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re)
          - (∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re := by
      rw [Complex.sub_re]
      ring
    rw [hsplit]
    have h1 : -((logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re) ≤ 300*L := by
      have habs := Complex.abs_re_le_norm (logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u))
      have hneg := neg_abs_le (logDeriv riemannZeta s₁
        - ∑ u ∈ S, (n u : ℂ) / (s₁ - u)).re
      rw [hLdef]
      linarith
    linarith [hsum_ge]
  have hexp2T2 : Real.exp 4 ≤ 2*T := by linarith
  obtain ⟨S₂, n₂, hS₂_mem, hcert₂, _, hbound₂⟩ :=
    zeta_partial_fraction_fixed hexp2T2
  set s₂ : ℂ := ((σ:ℝ):ℂ) + ((2*T:ℝ):ℂ) * Complex.I with hs₂def
  have hL₂ : L ≤ Real.log (2*T) := by
    rw [hLdef]
    apply Real.log_le_log hTpos
    linarith
  have hs₂re : s₂.re = σ := by
    rw [hs₂def]
    simp
  have hζs₂ : riemannZeta s₂ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₂re]; exact hσ1)
  have hs₂mem : s₂ ∈ Metric.closedBall
      (((1 + 1/32 : ℝ) : ℂ) + ((2*T : ℝ) : ℂ) * Complex.I) (1/32) := by
    have hs₂c : s₂ - (((1 + 1/32 : ℝ) : ℂ) + ((2*T : ℝ) : ℂ) * Complex.I)
        = (((σ - (1 + 1/32) : ℝ)):ℂ) := by
      rw [hs₂def]
      push_cast
      ring
    rw [Metric.mem_closedBall, dist_eq_norm, hs₂c, Complex.norm_real,
      Real.norm_eq_abs, abs_le]
    constructor
    · rw [hσdef]
      linarith [hinv]
    · rw [hσdef]
      linarith [hδ32]
  have hb₂ := hbound₂ s₂ hs₂mem hζs₂
  have hure₂ : ∀ u ∈ S₂, 1 ≤ n₂ u → u.re < 1 := by
    intro u hu hnu
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re hc (hcert₂ u hu hnu)
  have hterm₂_nonneg : ∀ u ∈ S₂,
      0 ≤ ((n₂ u : ℂ) / (s₂ - u)).re := by
    intro u hu
    rcases Nat.eq_zero_or_pos (n₂ u) with h0 | hpos
    · rw [h0]
      simp
    · have hlt := hure₂ u hu hpos
      rw [pf_term_re]
      apply mul_nonneg (Nat.cast_nonneg _)
      apply div_nonneg _ (Complex.normSq_nonneg _)
      rw [Complex.sub_re, hs₂re]
      linarith
  have hΦ2 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re
      ≤ 300*L + 208 := by
    have hbr := vonMangoldt_re_eq_neg_logDeriv
      (s := s₂) (by rw [hs₂re]; exact hσ1)
    rw [hbr]
    have hsplit : -(logDeriv riemannZeta s₂).re
        = -((logDeriv riemannZeta s₂
            - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re)
          - (∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re := by
      rw [Complex.sub_re]
      ring
    rw [hsplit]
    have h1 : -((logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re)
        ≤ 300 * Real.log (2*T) := by
      have habs := Complex.abs_re_le_norm (logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u))
      have hneg := neg_abs_le (logDeriv riemannZeta s₂
        - ∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re
      linarith
    have h2 : (0:ℝ) ≤ (∑ u ∈ S₂, (n₂ u : ℂ) / (s₂ - u)).re := by
      rw [Complex.re_sum]
      exact Finset.sum_nonneg hterm₂_nonneg
    have h3 : Real.log (2*T) = Real.log 2 + L := by
      rw [hLdef, Real.log_mul (by norm_num) hTpos.ne']
    have h4 : Real.log 2 ≤ 0.6932 := by
      nlinarith [Real.log_two_lt_d9]
    have h5 : 300 * Real.log (2*T) ≤ 300*L + 208 := by
      rw [h3]
      nlinarith
    linarith
  have h341 := three_four_one (σ := σ) (t := T) hσ1
  have hkey : 4/(σ - β) ≤ 32000*L := by
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hc1 : 0 ≤ 3 * (10000*L + 3)
        + 4 * (-(1/(σ - β)) + 300*L) + (300*L + 208) := by
      calc (0:ℝ) ≤ 3 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
          + 4 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
          + (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re := h341
        _ ≤ 3 * (10000*L + 3)
            + 4 * (-(1/(σ - β)) + 300*L) + (300*L + 208) := by
            have := hΦ0
            have := hΦ1
            have := hΦ2
            linarith
    have h4d : 4/(σ - β) = 4*(1/(σ - β)) := by ring
    rw [h4d]
    nlinarith
  have hσβ : (0:ℝ) < σ - β := by linarith
  have hx : 4/(32000*L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 32000*L)]
    rw [div_le_iff₀ hσβ] at hkey
    nlinarith [hkey]
  have hfinal : β ≤ 1 - (1/50000)/L := by
    have hnum : (1:ℝ)/10000 + 1/50000 ≤ 4/32000 := by norm_num
    have hkey2 : 1/(10000*L) + (1/50000)/L ≤ 4/(32000*L) := by
      have e1 : (1:ℝ)/(10000*L) = (1/10000)/L := (div_div 1 10000 L).symm
      have e2 : (4:ℝ)/(32000*L) = (4/32000)/L := (div_div 4 32000 L).symm
      rw [e1, e2, ← add_div]
      exact div_le_div_of_nonneg_right hnum hLpos.le
    rw [hσdef] at hx
    linarith
  rw [← hLdef, ← hβdef] at *
  exact hfinal

/-- **The exponent-1 region, threshold e⁴** — the fixed-center payoff:
every zero with `|γ| ≥ e⁴ ≈ 55` has `β ≤ 1 − (1/50000)/log|γ|`. -/
theorem zero_free_region_exponent_one' :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 4 ≤ |ρ.im| → ρ.re ≤ 1 - c₀ / Real.log |ρ.im| := by
  refine ⟨1/50000, by norm_num, ?_⟩
  intro ρ hζρ him
  rcases abs_cases ρ.im with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at him ⊢
    exact zero_free_region_exponent_one_aux' hζρ him
  · have hζρ' : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hζρ, map_zero]
    have hconj_im : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have him' : Real.exp 4 ≤ ((starRingEnd ℂ) ρ).im := by
      rw [hconj_im]
      rw [heq] at him
      linarith
    have haux := zero_free_region_exponent_one_aux' hζρ' him'
    rw [Complex.conj_re, hconj_im] at haux
    rw [heq]
    exact haux

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.zero_free_region_exponent_one'
end AxiomAudit
