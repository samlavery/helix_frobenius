import RequestProject.DVPZeroFreeXi

/-!
# The Hadamard-route region with the anchor re-optimised: `c₀ = 1/42` (ledger 1355)

1354 used the anchor `σ = 1 + 1/(5L)`. With `σ = 1 + a/L` the same three rungs give
`4/(σ−β) ≤ (3/a + 5/2)·L + 15.35`, and for `L ≥ 32` the optimum of `4/(3/a + 2.98) − a` is at `a ≈ 0.156`,
i.e. `a = 5/32` (Chatbibibi via Sam, 2026-10-15). Then `21.7L + 15.35 ≤ 22.2L`, so `σ − β ≥ 4/(22.2L)` and
`1 − β ≥ (4/22.2 − 5/32)/L > 1/(42L)`. Same lemmas as 1354; only the arithmetic changes.
-/

open Real Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale CriticalLinePhasor.SeatingLedger
open CriticalLinePhasor.HelixPencilDegreeOne CriticalLinePhasor.HelixWeilWitness

set_option maxHeartbeats 3200000 in
/-- The positive-ordinate case with the anchor `σ = 1 + (5/32)/L`: `Re ρ ≤ 1 − (1/42)/log(Im ρ)`. -/
theorem zero_free_region_xi_42_aux {ρ : ℂ}
    (hζρ : riemannZeta ρ = 0) (hT32 : Real.exp 32 ≤ ρ.im) :
    ρ.re ≤ 1 - (1/42) / Real.log ρ.im := by
  set T : ℝ := ρ.im with hTdef
  set β : ℝ := ρ.re with hβdef
  have hTpos : (0:ℝ) < T := lt_of_lt_of_le (Real.exp_pos 32) hT32
  have hL32 : (32:ℝ) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 32) hT32
    rwa [Real.log_exp] at this
  set L : ℝ := Real.log T with hLdef
  have hLpos : (0:ℝ) < L := by linarith
  have hT20 : (20 : ℝ) ≤ T := by
    have h : Real.exp 32 ≥ 20 := by
      have := Real.add_one_le_exp (32 : ℝ); linarith
    linarith
  have hβ1 : β < 1 := by
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re (by rw [← hβdef]; exact hc) hζρ
  by_cases hβtriv : β ≤ 1 - 3/32
  · have hc0 : (1/42 : ℝ) / L ≤ 3/32 := by
      have h1 : (1/42 : ℝ) / L ≤ (1/42 : ℝ) / 32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      calc (1/42 : ℝ) / L ≤ (1/42 : ℝ) / 32 := h1
        _ ≤ 3/32 := by norm_num
    linarith
  push_neg at hβtriv
  have hβ0 : (0 : ℝ) < β := by linarith
  have hρmem : ρ ∈ ZD.NontrivialZeros := ⟨hβ0, hβ1, hζρ⟩
  let ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρ, hρmem⟩
  have hβhalf : ρ₀.val.re ≠ 1/2 := by show ρ.re ≠ 1/2; intro h; linarith
  -- the anchor
  set σ : ℝ := 1 + (5/32)/L with hσdef
  have hinv : (0:ℝ) < (5/32)/L := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ98 : σ ≤ 9/8 := by
    rw [hσdef]
    have : (5/32 : ℝ)/L ≤ 1/8 := by
      rw [div_le_iff₀ hLpos]; linarith
    linarith
  -- (B) the real-axis rung
  have hΦ0 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re ≤ (32/5)*L + 3 := by
    rw [vonMangoldt_re_eq_neg_logDeriv (by simp; linarith)]
    have h1 := zeta_logDeriv_rung_sharp hσ1 hσ98
    have h2 : -(logDeriv riemannZeta ((σ:ℝ):ℂ)).re ≤ ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ := by
      have := Complex.abs_re_le_norm (logDeriv riemannZeta ((σ:ℝ):ℂ))
      have := neg_abs_le (logDeriv riemannZeta ((σ:ℝ):ℂ)).re
      linarith
    have h3 : 1/(σ-1) = (32/5)*L := by
      rw [hσdef, show (1 + (5/32)/L - 1) = (5/32)/L by ring]
      field_simp
    linarith
  -- (C) the height-`T` rung through ξ
  set s₁ : ℂ := ((σ:ℝ):ℂ) + ((T:ℝ):ℂ) * Complex.I with hs₁def
  have hs₁re : s₁.re = σ := by rw [hs₁def]; simp
  have hΦ1 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re ≤ -(1/(σ - β)) + ((1/2) * L + 1.2) := by
    have hid := logDeriv_xi_eq_arch_sub_lseries (s := s₁) (by rw [hs₁re]; exact hσ1)
    have hL : LSeries (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁
        = weilArch s₁ - logDeriv ZD.riemannXi s₁ := by
      change LSeries vonMangoldtC s₁ = _
      rw [hid]; ring
    rw [hL, Complex.sub_re]
    have hA := re_weilArch_le hσ1 hσ98 hT20
    have hX := re_logDeriv_xi_ge_at_height hσ1 ρ₀ hβhalf
    rw [hLdef, hTdef]
    show (weilArch ((σ : ℂ) + (ρ.im : ℂ) * I)).re - (logDeriv ZD.riemannXi ((σ : ℂ) + (ρ.im : ℂ) * I)).re
      ≤ -(1/(σ - ρ.re)) + ((1/2) * Real.log ρ.im + 1.2)
    linarith [hA, hX]
  -- (D) the height-`2T` rung through ξ
  set s₂ : ℂ := ((σ:ℝ):ℂ) + ((2*T:ℝ):ℂ) * Complex.I with hs₂def
  have hs₂re : s₂.re = σ := by rw [hs₂def]; simp
  have hΦ2 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re ≤ (1/2) * L + 1.55 := by
    have hid := logDeriv_xi_eq_arch_sub_lseries (s := s₂) (by rw [hs₂re]; exact hσ1)
    have hL : LSeries (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂
        = weilArch s₂ - logDeriv ZD.riemannXi s₂ := by
      change LSeries vonMangoldtC s₂ = _
      rw [hid]; ring
    rw [hL, Complex.sub_re]
    have hA := re_weilArch_le hσ1 hσ98 (t := 2*T) (by linarith)
    have hX : 0 ≤ (logDeriv ZD.riemannXi s₂).re := by
      rw [logDeriv_apply]
      exact re_logDeriv_xi_nonneg_of_one_le_re (by rw [hs₂re]; exact hσ1.le)
    have hlog2T : Real.log (2*T) = Real.log 2 + L := by
      rw [hLdef, Real.log_mul (by norm_num) hTpos.ne']
    have hlog2 : Real.log 2 ≤ 0.7 := by nlinarith [Real.log_two_lt_d9]
    have hA' : (weilArch s₂).re ≤ (1/2) * L + 1.55 := by
      rw [hs₂def]
      push_cast at hA ⊢
      rw [hlog2T] at hA
      linarith
    linarith
  -- (E) the 3-4-1 assembly: `4/(σ−β) ≤ 21.7L + 15.35 ≤ 22.2L`
  have h341 := three_four_one (σ := σ) (t := T) hσ1
  have hkey : 4/(σ - β) ≤ 22.2*L := by
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hc1 : 0 ≤ 3 * ((32/5)*L + 3) + 4 * (-(1/(σ - β)) + ((1/2) * L + 1.2)) + ((1/2) * L + 1.55) := by
      calc (0:ℝ) ≤ 3 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
          + 4 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
          + (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re := h341
        _ ≤ 3 * ((32/5)*L + 3) + 4 * (-(1/(σ - β)) + ((1/2) * L + 1.2)) + ((1/2) * L + 1.55) := by
            linarith [hΦ0, hΦ1, hΦ2]
    have h4d : 4/(σ - β) = 4*(1/(σ - β)) := by ring
    rw [h4d]
    linarith
  -- extract β
  have hσβ : (0:ℝ) < σ - β := by linarith
  have hx : 4/(22.2*L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 22.2*L)]
    rw [div_le_iff₀ hσβ] at hkey
    nlinarith [hkey]
  have hfinal : β ≤ 1 - (1/42)/L := by
    have hnum : (5/32 : ℝ) + 1/42 ≤ 4/22.2 := by norm_num
    have hkey2 : (5/32)/L + (1/42)/L ≤ 4/(22.2*L) := by
      have e2 : (4:ℝ)/(22.2*L) = (4/22.2)/L := (div_div 4 22.2 L).symm
      rw [e2, ← add_div]
      exact div_le_div_of_nonneg_right hnum hLpos.le
    rw [hσdef] at hx
    linarith
  rw [← hLdef, ← hβdef] at *
  exact hfinal

/-- **The exponent-1 zero-free region with the explicit constant `1/42`.** -/
theorem zero_free_region_xi_42' :
    ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - (1/42) / Real.log |ρ.im| := by
  intro ρ hζρ him
  rcases abs_cases ρ.im with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at him ⊢
    exact zero_free_region_xi_42_aux hζρ him
  · have hζρ' : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hζρ, map_zero]
    have hconj_im : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have him' : Real.exp 32 ≤ ((starRingEnd ℂ) ρ).im := by
      rw [hconj_im]
      rw [heq] at him
      linarith
    have haux := zero_free_region_xi_42_aux hζρ' him'
    rw [Complex.conj_re, hconj_im] at haux
    rw [heq]
    exact haux

/-- **The exponent-1 zero-free region, `c₀ = 1/42`.** -/
theorem zero_free_region_xi_42 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - c₀ / Real.log |ρ.im| :=
  ⟨1/42, by norm_num, zero_free_region_xi_42'⟩

end CriticalLinePhasor.DVP

end

#print axioms CriticalLinePhasor.DVP.zero_free_region_xi_42
