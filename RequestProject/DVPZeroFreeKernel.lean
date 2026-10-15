import RequestProject.DVPZeroFreeXi

/-!
# The Hadamard-route region with the kernel `(3 + 4cos θ)²`: `c₀ = 1/32` (ledger 1356)

1354–1355 used the classical kernel `3 + 4cos θ + cos 2θ = 2(1 + cos θ)²`. The kernel
`17 + 24cos θ + 8cos 2θ = (3 + 4cos θ)²` is also nonnegative, and its weights are more favourable: with the same
three rungs (real axis `1/(σ−1) + 3`; height `T`: `½L + 1.2 − 1/(σ−β)`; height `2T`: `½L + 1.55`) and the anchor
`σ = 1 + 1/(6L)`,

`24/(σ−β) ≤ 17(6L+3) + 24(½L+1.2) + 8(½L+1.55) = 118L + 92.2 ≤ 121L`   (`L ≥ 32`),

so `1 − β ≥ (24/121 − 1/6)/L = 23/(726 L) > 1/(32 L)` (Chatbibibi via Sam, 2026-10-15; checked). The kernel
inequality `seventeen_twentyfour_eight` mirrors the compiled `three_four_one` termwise. No new analytic estimate.
-/

open Real Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale CriticalLinePhasor.SeatingLedger
open CriticalLinePhasor.HelixPencilDegreeOne CriticalLinePhasor.HelixWeilWitness

set_option maxHeartbeats 1600000 in
/-- **The `(3 + 4cos θ)²` inequality.** For `σ > 1` and any `t`:
`0 ≤ 17·Re L(Λ,σ) + 24·Re L(Λ,σ+it) + 8·Re L(Λ,σ+2it)`. -/
theorem seventeen_twentyfour_eight {σ t : ℝ} (hσ : 1 < σ) :
    0 ≤ 17 * (LSeries (fun k =>
          ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
      + 24 * (LSeries (fun k =>
          ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
            (((σ:ℝ):ℂ) + (t:ℝ) * Complex.I)).re
      + 8 * (LSeries (fun k =>
          ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
            (((σ:ℝ):ℂ) + (2*t:ℝ) * Complex.I)).re := by
  have hre : ∀ u : ℝ, ((((σ:ℝ):ℂ)) + (u:ℝ) * Complex.I).re = σ := by
    intro u
    simp
  have hsum : ∀ u : ℝ, LSeriesSummable (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
      (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I) := by
    intro u
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    rw [hre u]
    exact hσ
  have hzero : ((σ:ℝ):ℂ) = ((σ:ℝ):ℂ) + ((0:ℝ):ℝ) * Complex.I := by
    simp
  have hre_ser : ∀ u : ℝ,
      (LSeries (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I)).re
      = ∑' n : ℕ, (if n = 0 then (0:ℝ) else
          ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
            * Real.cos (u * Real.log n)) := by
    intro u
    rw [show LSeries (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
        (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I)
        = ∑' n, LSeries.term
            (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
            (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I) n from rfl]
    rw [Complex.re_tsum (hsum u)]
    exact tsum_congr (vonMangoldt_term_re σ u)
  have hsum_re : ∀ u : ℝ, Summable (fun n : ℕ =>
      (if n = 0 then (0:ℝ) else
        ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
          * Real.cos (u * Real.log n))) := by
    intro u
    have h1 : Summable (fun n : ℕ =>
        (LSeries.term (fun k => ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ))
          (((σ:ℝ):ℂ) + (u:ℝ) * Complex.I) n).re) :=
      ⟨_, (hsum u).hasSum.mapL Complex.reCLM⟩
    apply Summable.congr h1
    exact vonMangoldt_term_re σ u
  have h0ser : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
      = ∑' n : ℕ, (if n = 0 then (0:ℝ) else
          ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
            * Real.cos (0 * Real.log n)) := by
    rw [hzero]
    exact hre_ser 0
  rw [h0ser, hre_ser t, hre_ser (2*t)]
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← ((hsum_re 0).mul_left 17).tsum_add ((hsum_re t).mul_left 24),
    ← (((hsum_re 0).mul_left 17).add ((hsum_re t).mul_left 24)).tsum_add
      ((hsum_re (2*t)).mul_left 8)]
  apply tsum_nonneg
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp
  · have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    simp only [if_neg hne]
    have hΛ : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt n :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hnσ : (0:ℝ) < ((n:ℝ)) ^ (-σ) := by
      have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hpos
      positivity
    set x : ℝ := Real.cos (t * Real.log n) with hx
    have hcos2 : Real.cos ((2*t) * Real.log n) = 2 * x^2 - 1 := by
      rw [show (2*t) * Real.log n = 2 * (t * Real.log n) by ring]
      rw [Real.cos_two_mul, hx]
    rw [hcos2]
    have hfactor : 17 * (ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ) * 1)
        + 24 * (ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ) * x)
        + 8 * (ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ) * (2*x^2 - 1))
        = ArithmeticFunction.vonMangoldt n * ((n:ℝ)) ^ (-σ)
            * ((3 + 4*x)^2) := by
      ring
    have hcos0 : Real.cos (0 * Real.log n) = 1 := by
      rw [zero_mul, Real.cos_zero]
    rw [hcos0, hfactor]
    positivity

set_option maxHeartbeats 3200000 in
/-- The positive-ordinate case with the kernel `(3 + 4cos θ)²` and the anchor `σ = 1 + 1/(6L)`:
`Re ρ ≤ 1 − (1/32)/log(Im ρ)`. -/
theorem zero_free_region_kernel_aux {ρ : ℂ}
    (hζρ : riemannZeta ρ = 0) (hT32 : Real.exp 32 ≤ ρ.im) :
    ρ.re ≤ 1 - (1/32) / Real.log ρ.im := by
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
  · have hc0 : (1/32 : ℝ) / L ≤ 3/32 := by
      have h1 : (1/32 : ℝ) / L ≤ (1/32 : ℝ) / 32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      calc (1/32 : ℝ) / L ≤ (1/32 : ℝ) / 32 := h1
        _ ≤ 3/32 := by norm_num
    linarith
  push_neg at hβtriv
  have hβ0 : (0 : ℝ) < β := by linarith
  have hρmem : ρ ∈ ZD.NontrivialZeros := ⟨hβ0, hβ1, hζρ⟩
  let ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρ, hρmem⟩
  have hβhalf : ρ₀.val.re ≠ 1/2 := by show ρ.re ≠ 1/2; intro h; linarith
  -- the anchor
  set σ : ℝ := 1 + 1/(6*L) with hσdef
  have hinv : (0:ℝ) < 1/(6*L) := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ98 : σ ≤ 9/8 := by
    rw [hσdef]
    have : (1:ℝ)/(6*L) ≤ 1/8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    linarith
  -- (B) the real-axis rung
  have hΦ0 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re ≤ 6*L + 3 := by
    rw [vonMangoldt_re_eq_neg_logDeriv (by simp; linarith)]
    have h1 := zeta_logDeriv_rung_sharp hσ1 hσ98
    have h2 : -(logDeriv riemannZeta ((σ:ℝ):ℂ)).re ≤ ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ := by
      have := Complex.abs_re_le_norm (logDeriv riemannZeta ((σ:ℝ):ℂ))
      have := neg_abs_le (logDeriv riemannZeta ((σ:ℝ):ℂ)).re
      linarith
    have h3 : 1/(σ-1) = 6*L := by
      rw [hσdef, show (1 + 1/(6*L) - 1) = 1/(6*L) by ring, one_div_one_div]
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
  -- (E) the kernel assembly: `24/(σ−β) ≤ 118L + 92.2 ≤ 121L`
  have hker := seventeen_twentyfour_eight (σ := σ) (t := T) hσ1
  have hkey : 24/(σ - β) ≤ 121*L := by
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hc1 : 0 ≤ 17 * (6*L + 3) + 24 * (-(1/(σ - β)) + ((1/2) * L + 1.2)) + 8 * ((1/2) * L + 1.55) := by
      calc (0:ℝ) ≤ 17 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
          + 24 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
          + 8 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re := hker
        _ ≤ 17 * (6*L + 3) + 24 * (-(1/(σ - β)) + ((1/2) * L + 1.2)) + 8 * ((1/2) * L + 1.55) := by
            linarith [hΦ0, hΦ1, hΦ2]
    have h4d : 24/(σ - β) = 24*(1/(σ - β)) := by ring
    rw [h4d]
    linarith
  -- extract β
  have hσβ : (0:ℝ) < σ - β := by linarith
  have hx : 24/(121*L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 121*L)]
    rw [div_le_iff₀ hσβ] at hkey
    nlinarith [hkey]
  have hfinal : β ≤ 1 - (1/32)/L := by
    have hnum : (1:ℝ)/6 + 1/32 ≤ 24/121 := by norm_num
    have hkey2 : 1/(6*L) + (1/32)/L ≤ 24/(121*L) := by
      have e1 : (1:ℝ)/(6*L) = (1/6)/L := (div_div 1 6 L).symm
      have e2 : (24:ℝ)/(121*L) = (24/121)/L := (div_div 24 121 L).symm
      rw [e1, e2, ← add_div]
      exact div_le_div_of_nonneg_right hnum hLpos.le
    rw [hσdef] at hx
    linarith
  rw [← hLdef, ← hβdef] at *
  exact hfinal

/-- **The exponent-1 zero-free region with the explicit constant `1/32`.** -/
theorem zero_free_region_kernel' :
    ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - (1/32) / Real.log |ρ.im| := by
  intro ρ hζρ him
  rcases abs_cases ρ.im with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at him ⊢
    exact zero_free_region_kernel_aux hζρ him
  · have hζρ' : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hζρ, map_zero]
    have hconj_im : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have him' : Real.exp 32 ≤ ((starRingEnd ℂ) ρ).im := by
      rw [hconj_im]
      rw [heq] at him
      linarith
    have haux := zero_free_region_kernel_aux hζρ' him'
    rw [Complex.conj_re, hconj_im] at haux
    rw [heq]
    exact haux

/-- **The exponent-1 zero-free region with the kernel `(3 + 4cos θ)²`, `c₀ = 1/32`.** -/
theorem zero_free_region_kernel :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - c₀ / Real.log |ρ.im| :=
  ⟨1/32, by norm_num, zero_free_region_kernel'⟩

end CriticalLinePhasor.DVP

end

#print axioms CriticalLinePhasor.DVP.seventeen_twentyfour_eight
#print axioms CriticalLinePhasor.DVP.zero_free_region_kernel
