import RequestProject.DVPWeightedCount
import RequestProject.DVPWindowCount
import RequestProject.HelixPencilDegreeOne
import RequestProject.WeilExplicitFormula
import RequestProject.SeatMassEtaForm
import RequestProject.GammaJetsSeries
import RequestProject.HelixWeilWitnessNear

/-!
# The exponent-one zero-free region through the Hadamard product: `c₀ = 1/45` (ledger 1354)

1353 sharpened the compiled de la Vallée Poussin constant from `1/50000` to `1/3000` inside the partial-fraction
route. The dominant remaining loss is that route itself: Landau's lemma replaces `−Re ζ′/ζ(σ+it)` by
`A·log t − 1/(σ−β)` with `A = 40`. The classical value is `A = ½`, and the repository already has the two
identities that give it:

* `logDeriv_xi_eq_arch_sub_lseries` (`Re s > 1`): `ξ′/ξ(s) = weilArch(s) − Σ Λ(n) n^{−s}`;
* the seat identity (1329): `Re ξ′/ξ(s) = (σ − ½) Σ_ρ m_ρ Re seatTerm(s,ρ)` with every term `≥ 0` for `σ ≥ 1`.

So `−Re ζ′/ζ(s) = Re weilArch(s) − Re ξ′/ξ(s)`, and keeping only the zero's own pair in the seat sum gives
`−Re ζ′/ζ(σ+iγ₀) ≤ Re weilArch(σ+iγ₀) − 1/(σ−β₀)`. The archimedean term is bounded from the compiled line bound
`clockRate t ≤ ½ log t` (`clockRate_upper`) by shifting `ψ` from `Re = ¼` to `Re = σ/2` with
`‖ψ′‖ ≤ 7` at height `≥ 10` (`norm_deriv_digamma_le`, from the compiled polygamma series). The 3-4-1 budget is
then `4/(σ−β) ≤ 3(5L + 3) + 4(½L + 1.2) + (½L + 1.55) ≤ 18L` at the anchor `σ = 1 + 1/(5L)`, and
`c₀ = 4/18 − 1/5 = 1/45`.

Unconditional, standard axioms, no `sorry`. An improvement within the repository (the published constant is
about `1/4.9`, Bellotti–Trudgian–Yang 2026, as reported); this is the textbook de la Vallée Poussin constant
with the `O(1)` terms kept explicit at `L ≥ 32`.
-/

open Real Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale CriticalLinePhasor.SeatingLedger
open CriticalLinePhasor.HelixPencilDegreeOne CriticalLinePhasor.HelixWeilWitness

/-! ## 1. The digamma derivative at height `≥ 10` -/

theorem mem_integerComplement_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : z ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  apply hz
  rw [← hn]
  simp

/-- The Basel sum shifted by one: `Σ_{n≥0} 1/(n+1)² = π²/6`. -/
theorem hasSum_inv_succ_sq : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- `‖ψ′(w)‖ ≤ 7` for `Re w ≥ 1/4`, `Im w ≥ 10`: the polygamma series termwise, `‖w+n‖² ≥ (n+1)²/4`. -/
theorem norm_deriv_digamma_le {w : ℂ} (hre : 1/4 ≤ w.re) (him : 10 ≤ w.im) :
    ‖iteratedDeriv 1 Complex.digamma w‖ ≤ 7 := by
  have hw : w ∈ Complex.integerComplement := mem_integerComplement_of_im_ne_zero (by linarith)
  rw [iteratedDeriv_digamma_series hw le_rfl]
  have hcoef : ((-1 : ℂ) ^ (1 + 1) * ((Nat.factorial 1 : ℕ) : ℂ)) = 1 := by norm_num
  rw [hcoef, one_mul]
  -- termwise bound
  have hi2 : (100 : ℝ) ≤ w.im ^ 2 := by nlinarith
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (w + n) ^ (1 + 1)‖ ≤ 4 * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    rw [norm_div, norm_one, norm_pow]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq : ‖w + n‖ ^ 2 = (w.re + n) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, add_zero]
      ring
    have hpos : (0 : ℝ) < ‖w + n‖ ^ 2 := by rw [hsq]; positivity
    have hkey : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * ‖w + n‖ ^ 2 := by
      rw [hsq]
      push_cast
      nlinarith [mul_nonneg hn0 (by linarith : (0:ℝ) ≤ w.re - 1/4), sq_nonneg (w.re - 1/4)]
    rw [show ‖w + n‖ ^ (1 + 1) = ‖w + n‖ ^ 2 by norm_num]
    rw [div_le_iff₀ hpos]
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    rw [show (4 : ℝ) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) * ‖w + n‖ ^ 2 = 4 * ‖w + n‖ ^ 2 / ((n + 1 : ℕ) : ℝ) ^ 2 by ring]
    rw [le_div_iff₀ hn1]
    linarith
  have hsum4 : Summable (fun n : ℕ => 4 * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    hasSum_inv_succ_sq.summable.mul_left 4
  have hnormsum : Summable (fun n : ℕ => ‖(1 : ℂ) / (w + n) ^ (1 + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum4
  calc ‖∑' n : ℕ, (1 : ℂ) / (w + n) ^ (1 + 1)‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / (w + n) ^ (1 + 1)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, 4 * ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := Summable.tsum_le_tsum hterm hnormsum hsum4
    _ = 4 * (π ^ 2 / 6) := by rw [tsum_mul_left, hasSum_inv_succ_sq.tsum_eq]
    _ ≤ 7 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- **The digamma shift from the line**: for `t ≥ 20` and `1/4 ≤ x ≤ 9/16`,
`‖ψ(x + it/2) − ψ(1/4 + it/2)‖ ≤ 7(x − 1/4)`. -/
theorem digamma_shift_le {t : ℝ} (ht : 20 ≤ t) {x : ℝ} (hx0 : 1/4 ≤ x) (hx1 : x ≤ 9/16) :
    ‖Complex.digamma ((x : ℂ) + ((t/2 : ℝ) : ℂ) * I)
      - Complex.digamma (((1/4 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)‖ ≤ 7 * (x - 1/4) := by
  set f : ℝ → ℂ := fun y => Complex.digamma ((y : ℂ) + ((t/2 : ℝ) : ℂ) * I) with hf
  have hderiv : ∀ y ∈ Icc (1/4 : ℝ) (9/16),
      HasDerivWithinAt f (iteratedDeriv 1 Complex.digamma ((y : ℂ) + ((t/2 : ℝ) : ℂ) * I))
        (Icc (1/4 : ℝ) (9/16)) y := by
    intro y _
    have hz : ((y : ℂ) + ((t/2 : ℝ) : ℂ) * I) ∈ Complex.integerComplement := by
      apply mem_integerComplement_of_im_ne_zero
      simp
      linarith
    have h1 := iteratedDeriv_digamma_hasDerivAt 0 hz
    rw [iteratedDeriv_zero] at h1
    have h2 : HasDerivAt (fun y : ℝ => ((y : ℂ) + ((t/2 : ℝ) : ℂ) * I)) 1 y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.add_const (((t/2 : ℝ) : ℂ) * I))
    have h3 := h1.comp y h2
    rw [mul_one] at h3
    exact h3.hasDerivWithinAt
  have hbound : ∀ y ∈ Ico (1/4 : ℝ) (9/16),
      ‖iteratedDeriv 1 Complex.digamma ((y : ℂ) + ((t/2 : ℝ) : ℂ) * I)‖ ≤ 7 := by
    intro y hy
    apply norm_deriv_digamma_le
    · simp; linarith [hy.1]
    · simp; linarith
  have := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound x ⟨hx0, hx1⟩
  simpa [hf] using this

/-! ## 2. The archimedean term off the line -/

/-- `Re weilArch(σ + it) ≤ ½ log t + 1.2` for `1 < σ ≤ 9/8`, `t ≥ 20`, from the compiled line bound
`clockRate t ≤ ½ log t` and the digamma shift. -/
theorem re_weilArch_le {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 9/8) (ht : 20 ≤ t) :
    (weilArch ((σ : ℂ) + (t : ℂ) * I)).re ≤ (1/2) * Real.log t + 1.2 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have ht0 : (0 : ℝ) < t := by linarith
  have ht2 : (400 : ℝ) ≤ t ^ 2 := by nlinarith
  -- the two pole terms
  have h1 : (1 / s).re ≤ 0.003 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hsre, hsim]
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have h2 : (1 / (s - 1)).re ≤ 0.001 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hsre, hsim, sub_zero]
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  -- the digamma term
  have hψ : (logDeriv Complex.Gamma (s / 2)).re ≤ Real.log t + Real.log Real.pi + 2.2 := by
    have hs2 : s / 2 = ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
    have hline : (Complex.digamma (((1/4 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).re
        = 2 * clockRate t + Real.log Real.pi := by
      have hre0 : (0 : ℝ) < (line t).re := by simp [line_def]
      have hG := logDeriv_Gammaℝ_eq hre0
      have hhalf : line t / 2 = ((1/4 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I := by
        rw [line_def]; push_cast; ring
      rw [hhalf] at hG
      unfold clockRate
      rw [hG]
      simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re]
      change _ = 2 * (-(Real.log Real.pi) / 2 + (Complex.digamma _).re / 2) + Real.log Real.pi
      ring
    have hcr := clockRate_upper ht
    have hshift := digamma_shift_le ht (x := σ/2) (by linarith) (by linarith)
    have hre_le : (Complex.digamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).re
        ≤ (Complex.digamma (((1/4 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).re + 7 * (σ/2 - 1/4) := by
      have := Complex.re_le_norm (Complex.digamma (((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)
        - Complex.digamma (((1/4 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I))
      rw [Complex.sub_re] at this
      linarith
    have h7 : 7 * (σ/2 - 1/4) ≤ 2.2 := by nlinarith
    rw [hs2]
    change (Complex.digamma _).re ≤ _
    linarith [hre_le, hline, hcr, h7]
  unfold weilArch
  simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
  linarith [h1, h2, hψ]

/-! ## 3. The seat lower bound at the zero's own height -/

/-- At `s₁ = σ + iγ₀` and a zero `ρ₀ = β₀ + iγ₀` with `β₀ < σ`, `σ + β₀ > 1`: the seat term is the positive real
`m₀/((σ−β₀)(σ+β₀−1))`, hence `≥ 1/((σ−β₀)(σ+β₀−1))`. -/
theorem seatTerm_re_ge_at_height {σ : ℝ} (ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hβσ : ρ₀.val.re < σ) (hsum : 1 < σ + ρ₀.val.re) :
    1 / ((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1))
      ≤ (seatTerm ((σ : ℂ) + (ρ₀.val.im : ℂ) * I) ρ₀).re := by
  set s₁ : ℂ := (σ : ℂ) + (ρ₀.val.im : ℂ) * I with hs₁
  unfold seatTerm
  rw [← mul_inv, seat_denominator]
  have hprod : (s₁ - ρ₀.val) * (ρ₀.val + conj s₁ - 1)
      = (((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1) : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [seat_denominator_re]; simp [hs₁]
    · simp [hs₁, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  rw [hprod, ← Complex.ofReal_inv]
  have hm : (1 : ℝ) ≤ (ZD.xiOrderNat ρ₀.val : ℝ) :=
    Nat.one_le_cast.mpr (Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ₀.2))
  have hden : (0 : ℝ) < (σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1) := by
    apply mul_pos <;> linarith
  rw [show ((ZD.xiOrderNat ρ₀.val : ℂ) * (((((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1))⁻¹ : ℝ)) : ℂ))
      = (((ZD.xiOrderNat ρ₀.val : ℝ) * ((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1))⁻¹ : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.ofReal_re, one_div]
  have hinv : (0 : ℝ) < ((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1))⁻¹ := inv_pos.mpr hden
  nlinarith

/-- **The ξ-rung at the zero's height**: for `σ ∈ (1, 9/8]` and a zero `ρ₀ = β₀ + iγ₀` with `β₀ ≠ ½`,
`1/(σ−β₀) ≤ Re ξ′/ξ(σ + iγ₀)`. Keeps the pair `{ρ₀, 1 − ρ̄₀}` of the seat sum and drops the rest. -/
theorem re_logDeriv_xi_ge_at_height {σ : ℝ} (hσ1 : 1 < σ) (ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hβ : ρ₀.val.re ≠ 1/2) :
    1 / (σ - ρ₀.val.re) ≤ (logDeriv ZD.riemannXi ((σ : ℂ) + (ρ₀.val.im : ℂ) * I)).re := by
  set s₁ : ℂ := (σ : ℂ) + (ρ₀.val.im : ℂ) * I with hs₁
  have hs₁re : s₁.re = σ := by simp [hs₁]
  have hs₁z : s₁ ∉ ZD.NontrivialZeros := fun h => by linarith [h.2.1]
  have hs₁z' : 1 - conj s₁ ∉ ZD.NontrivialZeros := fun h => by
    have := h.1
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith
  have hσh : s₁.re ≠ 1/2 := by rw [hs₁re]; intro h; linarith
  rw [logDeriv_apply, re_logDeriv_xi_eq_seat hs₁z hs₁z' hσh, hs₁re,
    Complex.re_tsum (seatTerm_summable hs₁z hs₁z' hσh)]
  -- the mirror zero
  let ρm : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨1 - conj ρ₀.val, mirror_mem ρ₀⟩
  have hβ0 := ρ₀.2.1
  have hβ1 := ρ₀.2.2.1
  have hne : ρ₀ ≠ ρm := by
    intro h
    have := congrArg (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => ρ.val.re) h
    simp only [ρm, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    apply hβ; linarith
  have hnonneg : ∀ ρ, ρ ∉ ({ρ₀, ρm} : Finset _) → 0 ≤ (seatTerm s₁ ρ).re :=
    fun ρ _ => seatTerm_re_nonneg (by rw [hs₁re]; exact hσ1.le) ρ
  have hsummable : Summable (fun ρ => (seatTerm s₁ ρ).re) :=
    Complex.reCLM.summable (seatTerm_summable hs₁z hs₁z' hσh)
  have hpair := hsummable.sum_le_tsum ({ρ₀, ρm} : Finset _) hnonneg
  rw [Finset.sum_pair hne] at hpair
  -- both pair terms are `≥ 1/((σ−β₀)(σ+β₀−1))`
  have hβσ : ρ₀.val.re < σ := by linarith
  have hsum1 : 1 < σ + ρ₀.val.re := by linarith
  have ht1 := seatTerm_re_ge_at_height (σ := σ) ρ₀ hβσ hsum1
  have hmre : ρm.val.re = 1 - ρ₀.val.re := by simp [ρm, Complex.conj_re]
  have hmim : ρm.val.im = ρ₀.val.im := by simp [ρm, Complex.conj_im]
  have ht2 : 1 / ((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1)) ≤ (seatTerm s₁ ρm).re := by
    have h := seatTerm_re_ge_at_height (σ := σ) ρm (by rw [hmre]; linarith) (by rw [hmre]; linarith)
    rw [hmre, hmim] at h
    have e : (σ - (1 - ρ₀.val.re)) * (σ + (1 - ρ₀.val.re) - 1) = (σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1) := by ring
    rw [e] at h
    exact h
  have hden : (0 : ℝ) < (σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1) := by apply mul_pos <;> linarith
  -- `(σ − ½)·2/((σ−β)(σ+β−1)) ≥ 1/(σ−β)` ⟸ `2σ − 1 ≥ σ + β − 1`
  have hσβ : (0 : ℝ) < σ - ρ₀.val.re := by linarith
  have hkey : 1 / (σ - ρ₀.val.re)
      ≤ (σ - 1/2) * (2 * (1 / ((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1)))) := by
    rw [div_le_iff₀ hσβ]
    have : (σ - 1/2) * (2 * (1 / ((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1)))) * (σ - ρ₀.val.re)
        = (2 * σ - 1) / (σ + ρ₀.val.re - 1) := by
      field_simp
    rw [this, le_div_iff₀ (by linarith)]
    linarith
  calc 1 / (σ - ρ₀.val.re)
      ≤ (σ - 1/2) * (2 * (1 / ((σ - ρ₀.val.re) * (σ + ρ₀.val.re - 1)))) := hkey
    _ ≤ (σ - 1/2) * ((seatTerm s₁ ρ₀).re + (seatTerm s₁ ρm).re) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
    _ ≤ (σ - 1/2) * ∑' ρ, (seatTerm s₁ ρ).re := by
        apply mul_le_mul_of_nonneg_left hpair (by linarith)

/-! ## 4. The region -/

set_option maxHeartbeats 3200000 in
/-- The positive-ordinate case: `Re ρ ≤ 1 − (1/45)/log(Im ρ)` for `Im ρ ≥ e³²`. -/
theorem zero_free_region_xi_aux {ρ : ℂ}
    (hζρ : riemannZeta ρ = 0) (hT32 : Real.exp 32 ≤ ρ.im) :
    ρ.re ≤ 1 - (1/45) / Real.log ρ.im := by
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
  -- β < 1
  have hβ1 : β < 1 := by
    by_contra hc
    push_neg at hc
    exact riemannZeta_ne_zero_of_one_le_re (by rw [← hβdef]; exact hc) hζρ
  -- trivial branch
  by_cases hβtriv : β ≤ 1 - 3/32
  · have hc0 : (1/45 : ℝ) / L ≤ 3/32 := by
      have h1 : (1/45 : ℝ) / L ≤ (1/45 : ℝ) / 32 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL32
      calc (1/45 : ℝ) / L ≤ (1/45 : ℝ) / 32 := h1
        _ ≤ 3/32 := by norm_num
    linarith
  push_neg at hβtriv
  have hβ0 : (0 : ℝ) < β := by linarith
  -- the zero as a nontrivial zero
  have hρmem : ρ ∈ ZD.NontrivialZeros := ⟨hβ0, hβ1, hζρ⟩
  let ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρ, hρmem⟩
  have hβhalf : ρ₀.val.re ≠ 1/2 := by show ρ.re ≠ 1/2; intro h; linarith
  -- the anchor
  set σ : ℝ := 1 + 1/(5*L) with hσdef
  have hinv : (0:ℝ) < 1/(5*L) := by positivity
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ98 : σ ≤ 9/8 := by
    rw [hσdef]
    have : (1:ℝ)/(5*L) ≤ 1/8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    linarith
  -- (B) the real-axis rung
  have hΦ0 : (LSeries (fun k =>
      ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re ≤ 5*L + 3 := by
    rw [vonMangoldt_re_eq_neg_logDeriv (by simp; linarith)]
    have h1 := zeta_logDeriv_rung_sharp hσ1 hσ98
    have h2 : -(logDeriv riemannZeta ((σ:ℝ):ℂ)).re ≤ ‖logDeriv riemannZeta ((σ:ℝ):ℂ)‖ := by
      have := Complex.abs_re_le_norm (logDeriv riemannZeta ((σ:ℝ):ℂ))
      have := neg_abs_le (logDeriv riemannZeta ((σ:ℝ):ℂ)).re
      linarith
    have h3 : 1/(σ-1) = 5*L := by
      rw [hσdef, show (1 + 1/(5*L) - 1) = 1/(5*L) by ring, one_div_one_div]
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
  -- (E) the 3-4-1 assembly
  have h341 := three_four_one (σ := σ) (t := T) hσ1
  have hkey : 4/(σ - β) ≤ 18*L := by
    have hσβ : (0:ℝ) < σ - β := by linarith
    have hc1 : 0 ≤ 3 * (5*L + 3) + 4 * (-(1/(σ - β)) + ((1/2) * L + 1.2)) + ((1/2) * L + 1.55) := by
      calc (0:ℝ) ≤ 3 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) ((σ:ℝ):ℂ)).re
          + 4 * (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₁).re
          + (LSeries (fun k =>
            ((ArithmeticFunction.vonMangoldt k : ℝ) : ℂ)) s₂).re := h341
        _ ≤ 3 * (5*L + 3) + 4 * (-(1/(σ - β)) + ((1/2) * L + 1.2)) + ((1/2) * L + 1.55) := by
            linarith [hΦ0, hΦ1, hΦ2]
    have h4d : 4/(σ - β) = 4*(1/(σ - β)) := by ring
    rw [h4d]
    linarith
  -- extract β
  have hσβ : (0:ℝ) < σ - β := by linarith
  have hx : 4/(18*L) ≤ σ - β := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 18*L)]
    rw [div_le_iff₀ hσβ] at hkey
    nlinarith [hkey]
  have hfinal : β ≤ 1 - (1/45)/L := by
    have hnum : (1:ℝ)/5 + 1/45 ≤ 4/18 := by norm_num
    have hkey2 : 1/(5*L) + (1/45)/L ≤ 4/(18*L) := by
      have e1 : (1:ℝ)/(5*L) = (1/5)/L := (div_div 1 5 L).symm
      have e2 : (4:ℝ)/(18*L) = (4/18)/L := (div_div 4 18 L).symm
      rw [e1, e2, ← add_div]
      exact div_le_div_of_nonneg_right hnum hLpos.le
    rw [hσdef] at hx
    linarith
  rw [← hLdef, ← hβdef] at *
  exact hfinal

/-- **The exponent-1 zero-free region with the explicit constant `1/45`.** -/
theorem zero_free_region_xi' :
    ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - (1/45) / Real.log |ρ.im| := by
  intro ρ hζρ him
  rcases abs_cases ρ.im with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at him ⊢
    exact zero_free_region_xi_aux hζρ him
  · have hζρ' : riemannZeta ((starRingEnd ℂ) ρ) = 0 := by
      rw [riemannZeta_conj, hζρ, map_zero]
    have hconj_im : ((starRingEnd ℂ) ρ).im = -ρ.im := Complex.conj_im ρ
    have him' : Real.exp 32 ≤ ((starRingEnd ℂ) ρ).im := by
      rw [hconj_im]
      rw [heq] at him
      linarith
    have haux := zero_free_region_xi_aux hζρ' him'
    rw [Complex.conj_re, hconj_im] at haux
    rw [heq]
    exact haux

/-- **The exponent-1 zero-free region through the Hadamard product, `c₀ = 1/45`.** -/
theorem zero_free_region_xi :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      Real.exp 32 ≤ |ρ.im| → ρ.re ≤ 1 - c₀ / Real.log |ρ.im| :=
  ⟨1/45, by norm_num, zero_free_region_xi'⟩

end CriticalLinePhasor.DVP

end

#print axioms CriticalLinePhasor.DVP.norm_deriv_digamma_le
#print axioms CriticalLinePhasor.DVP.digamma_shift_le
#print axioms CriticalLinePhasor.DVP.re_weilArch_le
#print axioms CriticalLinePhasor.DVP.re_logDeriv_xi_ge_at_height
#print axioms CriticalLinePhasor.DVP.zero_free_region_xi
