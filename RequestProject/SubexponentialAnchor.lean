import RequestProject.BoundedIffRH
import RequestProject.RiemannHypothesisBridge

/-!
# Subexponential and polynomial growth of the explicit anchor coefficients

Unfolded target: for an anchor s off the zeros with Re s < 1/2, the multiplicity-weighted
moments mu_k = sum_rho m_rho / ((s-rho)(rho-(1-conj s))) * transport(s,rho)^k
satisfy the zero-location conclusion whenever mu_k / R^k tends to zero for every R > 1.
In particular, an estimate |mu_k| <= C*(1+k^p), with fixed C and p, suffices.

Expectation-free construction: isolate a maximal transported atom with a Cesaro average;
first line `by_contra hlt`. Independently, convert a polynomial estimate to normalized decay;
first line `refine squeeze_zero_norm ...`. The maximal-atom argument below is adapted from
`BoundedIffRH.re_ge_half_of_bounded`, retaining its summable tail and analytic multiplicities.
Only the invocation of normalized decay changes. No simplicity assumption is used.

Searches before construction:
`rg -n -i 'subexponential|sub_exponential|polynomial.?growth|rh_of_.*growth|coeff.*bound.*pow|root.*coeff|radius.*converg' RequestProject --glob '*.lean'`;
`rg -n 'tendsto.*(pow|rpow).*mul.*(pow|exp)|tendsto.*(pow|rpow).*div.*(pow|exp)' .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean'`.
LeanSearch: n to a fixed natural power divided by r to the n tends to zero, r > 1.
Loogle: `"tendsto", "pow", "mul"`.
-/

open Complex Finset Filter Topology

namespace CriticalLinePhasor.SeatingLedger

theorem re_ge_half_of_subexponential {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2)
    (hdecay : ∀ R : ℝ, 1 < R →
      Tendsto (fun k : ℕ => xiCoeff s k / (R : ℂ) ^ k) atTop (𝓝 0)) (ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    1 / 2 ≤ ρ₀.val.re := by
  by_contra hlt
  push Not at hlt
  have hne0 : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, s - ρ.val ≠ 0 :=
    fun ρ => sub_ne_zero_of_notMem hs ρ.property
  have hw0 : 1 < ‖transport s ρ₀.val‖ := (one_lt_norm_transport_iff hs' (hne0 ρ₀)).mpr hlt
  -- the finite set of large atoms and its maximum
  set η : ℝ := (‖transport s ρ₀.val‖ - 1) / 2 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hAfin := finite_transport_ge hs hηpos
  have hρ₀A : ρ₀ ∈ {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | 1 + η ≤ ‖transport s ρ.val‖} := by
    simp only [Set.mem_ofPred_eq, hη]; linarith
  obtain ⟨ρs, hρsA, hρsmax⟩ := Set.exists_max_image _ (fun ρ => ‖transport s ρ.val‖) hAfin ⟨ρ₀, hρ₀A⟩
  set R : ℝ := ‖transport s ρs.val‖ with hRdef
  have hR1 : 1 < R := by
    have := hρsmax ρ₀ hρ₀A; linarith
  have hRpos : 0 < R := by linarith
  have hRall : ∀ ρ ∈ ZD.NontrivialZeros, ‖transport s ρ‖ ≤ R := by
    intro ρ hρ
    by_cases hmem : (⟨ρ, hρ⟩ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) ∈
        {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | 1 + η ≤ ‖transport s ρ.val‖}
    · exact hρsmax _ hmem
    · simp only [Set.mem_ofPred_eq, not_le] at hmem
      have := hρsmax ρ₀ hρ₀A
      rw [hη] at hmem; linarith
  -- the atoms of maximal modulus
  have hBfin : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | ‖transport s ρ.val‖ = R}.Finite :=
    hAfin.subset (fun ρ hρ => by
      simp only [Set.mem_ofPred_eq] at hρ ⊢
      have := hρsmax ρ₀ hρ₀A; rw [hρ, hη]; linarith)
  set B : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := hBfin.toFinset with hBdef
  have hρsB : ρs ∈ B := by rw [hBdef, Set.Finite.mem_toFinset]; exact hRdef.symm
  have hBout : ∀ ρ, ρ ∉ B → ‖transport s ρ.val‖ < R := by
    intro ρ hρ
    rw [hBdef, Set.Finite.mem_toFinset] at hρ
    simp only [Set.mem_ofPred_eq] at hρ
    exact lt_of_le_of_ne (hRall ρ.val ρ.property) hρ
  -- the finite part tends to zero
  have hsplit : ∀ k : ℕ, ∑ ρ ∈ B, nterm s R ρ k
      = xiCoeff s k / (R : ℂ) ^ k
        - ∑' ρ : ↑((↑B : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})ᶜ), nterm s R ρ.val k := by
    intro k
    rw [xiCoeff_div_pow, ← (summable_nterm hs hRall hRpos k).sum_add_tsum_compl (s := B)]
    ring
  have hF : Tendsto (fun k : ℕ => ∑ ρ ∈ B, nterm s R ρ k) atTop (𝓝 0) := by
    have := (hdecay R hR1).sub (tendsto_tail_zero hs hRpos hRall B hBout)
    rw [sub_zero] at this
    exact this.congr (fun k => (hsplit k).symm)
  -- twist by the conjugate of the maximal atom and take Cesàro means
  set u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun ρ => transport s ρ.val / (R : ℂ) with hu
  have hu1 : ∀ ρ ∈ B, ‖u ρ‖ = 1 := by
    intro ρ hρ
    rw [hBdef, Set.Finite.mem_toFinset] at hρ
    simp only [Set.mem_ofPred_eq] at hρ
    rw [hu]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hρ, div_self hRpos.ne']
  have hus : ‖u ρs‖ = 1 := hu1 ρs hρsB
  set a : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ :=
    fun ρ => (ZD.xiOrderNat ρ.val : ℂ) * atomWeight s ρ.val with ha
  have hG : Tendsto (fun k : ℕ => (starRingEnd ℂ) (u ρs) ^ k * ∑ ρ ∈ B, nterm s R ρ k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_zero_iff_norm_tendsto_zero.mp hF)
    refine this.congr (fun k => ?_)
    rw [norm_mul, norm_pow, Complex.norm_conj, hus, one_pow, one_mul]
  have hces := hG.cesaro_smul
  -- the Cesàro means computed atom by atom
  have hces_eq : ∀ K : ℕ, ((K : ℝ)⁻¹ : ℝ) • ∑ k ∈ range K,
      (starRingEnd ℂ) (u ρs) ^ k * ∑ ρ ∈ B, nterm s R ρ k
      = ∑ ρ ∈ B, a ρ * (((K : ℝ)⁻¹ : ℝ) • ∑ k ∈ range K, (u ρ * (starRingEnd ℂ) (u ρs)) ^ k) := by
    intro K
    simp only [Finset.mul_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Complex.real_smul, Complex.real_smul, ha, hu]
    simp only
    unfold nterm
    rw [mul_pow]
    ring
  have hlim : Tendsto (fun K : ℕ => ∑ ρ ∈ B, a ρ *
      (((K : ℝ)⁻¹ : ℝ) • ∑ k ∈ range K, (u ρ * (starRingEnd ℂ) (u ρs)) ^ k)) atTop (𝓝 (a ρs)) := by
    have hterm : ∀ ρ ∈ B, Tendsto (fun K : ℕ => a ρ *
        (((K : ℝ)⁻¹ : ℝ) • ∑ k ∈ range K, (u ρ * (starRingEnd ℂ) (u ρs)) ^ k)) atTop
        (𝓝 (if ρ = ρs then a ρs else 0)) := by
      intro ρ hρ
      by_cases hρs : ρ = ρs
      · subst hρs
        rw [if_pos rfl]
        have hone : u ρ * (starRingEnd ℂ) (u ρ) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hus]; norm_num
        have hev : ∀ᶠ K : ℕ in atTop, a ρ * (((K : ℝ)⁻¹ : ℝ) • ∑ k ∈ range K,
            (u ρ * (starRingEnd ℂ) (u ρ)) ^ k) = a ρ := by
          filter_upwards [Filter.eventually_ge_atTop 1] with K hK
          rw [hone]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
            Complex.real_smul]
          have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast (by omega : K ≠ 0)
          push_cast
          field_simp
        exact tendsto_const_nhds.congr' (hev.mono (fun K hK => hK.symm))
      · rw [if_neg hρs]
        have hv : ‖u ρ * (starRingEnd ℂ) (u ρs)‖ = 1 := by
          rw [norm_mul, Complex.norm_conj, hu1 ρ hρ, hus, one_mul]
        have hv1 : u ρ * (starRingEnd ℂ) (u ρs) ≠ 1 := by
          intro h
          apply hρs
          have hus0 : u ρs ≠ 0 := by intro h0; rw [h0, norm_zero] at hus; exact zero_ne_one hus
          have hcu : (starRingEnd ℂ) (u ρs) * u ρs = 1 := by
            rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hus]; norm_num
          have huu : u ρ = u ρs := by
            calc u ρ = u ρ * ((starRingEnd ℂ) (u ρs) * u ρs) := by rw [hcu, mul_one]
              _ = (u ρ * (starRingEnd ℂ) (u ρs)) * u ρs := by ring
              _ = u ρs := by rw [h, one_mul]
          rw [hu] at huu
          simp only at huu
          have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
          have hw : transport s ρ.val = transport s ρs.val := by
            have := congrArg (fun z => z * (R : ℂ)) huu
            simpa [div_mul_cancel₀ _ hR0] using this
          exact Subtype.ext (transport_injective (by intro h'; linarith) (hne0 ρ) (hne0 ρs) hw)
        have := (tendsto_cesaro_geom_zero hv hv1).const_mul (a ρ)
        rwa [mul_zero] at this
    have := tendsto_finsetSum B hterm
    rwa [Finset.sum_ite_eq' B ρs, if_pos hρsB] at this
  have hlim0 : Tendsto (fun K : ℕ => ∑ ρ ∈ B, a ρ *
      (((K : ℝ)⁻¹ : ℝ) • ∑ k ∈ range K, (u ρ * (starRingEnd ℂ) (u ρs)) ^ k)) atTop (𝓝 0) :=
    hces.congr hces_eq
  have hzero : a ρs = 0 := tendsto_nhds_unique hlim hlim0
  -- but the maximal atom's weight is nonzero
  have hm : (ZD.xiOrderNat ρs.val : ℂ) ≠ 0 := by
    exact_mod_cast (ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρs.property).ne'
  have hω : atomWeight s ρs.val ≠ 0 := by
    apply atomWeight_ne_zero (hne0 ρs)
    intro h
    have : ρs.val = 1 - (starRingEnd ℂ) s := by linear_combination h
    exact mirror_notMem_nontrivialZeros hs (this ▸ ρs.property)
  rw [ha] at hzero
  simp only at hzero
  exact mul_ne_zero hm hω hzero


/-- Reflection finishes the zero-location conclusion from normalized decay. -/
theorem rh_of_subexponential {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2)
    (hdecay : ∀ R : ℝ, 1 < R →
      Tendsto (fun k : ℕ => xiCoeff s k / (R : ℂ) ^ k) atTop (𝓝 0)) : RH := by
  intro ρ hρ
  have h1 := re_ge_half_of_subexponential hs hs' hdecay ⟨ρ, hρ⟩
  have h2 := re_ge_half_of_subexponential hs hs' hdecay
    ⟨1 - (starRingEnd ℂ) ρ, mirror_mem_nontrivialZeros hρ⟩
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h2
  linarith

/-- Polynomial growth is enough for normalized decay; the sequence here is arbitrary. -/
theorem normalized_decay_of_polynomial_growth {μ : ℕ → ℂ} {C : ℝ} {p : ℕ}
    (hC : ∀ k, ‖μ k‖ ≤ C * (1 + (k : ℝ) ^ p)) {R : ℝ} (hR : 1 < R) :
    Tendsto (fun k : ℕ => μ k / (R : ℂ) ^ k) atTop (𝓝 0) := by
  have hRpos : 0 < R := by linarith
  refine squeeze_zero_norm
    (a := fun k : ℕ => C * (1 / R ^ k + (k : ℝ) ^ p / R ^ k)) (fun k => ?_) ?_
  · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    calc ‖μ k‖ / R ^ k ≤ (C * (1 + (k : ℝ) ^ p)) / R ^ k :=
        div_le_div_of_nonneg_right (hC k) (pow_nonneg hRpos.le k)
      _ = _ := by ring
  · have h := ((tendsto_pow_const_div_const_pow_of_one_lt 0 hR).add
        (tendsto_pow_const_div_const_pow_of_one_lt p hR)).const_mul C
    simpa only [pow_zero, add_zero, mul_zero] using h

/-- A polynomial bound at one channel anchor suffices. -/
theorem rh_of_polynomial_growth {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2)
    {C : ℝ} {p : ℕ} (hC : ∀ k, ‖xiCoeff s k‖ ≤ C * (1 + (k : ℝ) ^ p)) : RH :=
  rh_of_subexponential hs hs' (fun _ hR => normalized_decay_of_polynomial_growth hC hR)

/-- Polynomial growth of the explicit prime-and-Gamma coefficients is a sufficient endpoint. -/
theorem explicit_polynomial_growth_iff_rh {s : ℂ} (hs : s.re < 0) :
    (∃ C : ℝ, ∃ p : ℕ, ∀ k,
      ‖toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets explicitLogDeriv s) k‖ ≤
        C * (1 + (k : ℝ) ^ p)) ↔ RH := by
  have hs0 : s ∉ ZD.NontrivialZeros := notMem_nontrivialZeros_of_re_nonpos hs.le
  have hs' : s.re ≠ 1 / 2 := by linarith
  have hseq : ∀ k, toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
      (jets explicitLogDeriv s) k = xiCoeff s k := by
    intro k
    rw [← jets_xiLogDeriv_eq_explicit hs, toeplitzCoeff_jets_eq_xiCoeff hs0 hs' k]
  simp only [hseq]
  constructor
  · rintro ⟨C, p, hC⟩
    exact rh_of_polynomial_growth hs0 (by linarith) hC
  · intro hRH
    refine ⟨(xiCoeff s 0).re / 2, 0, ?_⟩
    intro k
    convert bounded_of_rh hs0 hRH k using 1
    ring

/-- The one-anchor polynomial estimate reaches Mathlib's literal statement. -/
theorem riemannHypothesis_of_explicit_fixed_anchor_polynomial_growth
    (hbound : ∃ C : ℝ, ∃ p : ℕ, ∀ k,
      ‖toeplitzCoeff (-3) (jets explicitLogDeriv ((-1 : ℂ) + 20 * I)) k‖ ≤
        C * (1 + (k : ℝ) ^ p)) : RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  apply (explicit_polynomial_growth_iff_rh
    (s := (-1 : ℂ) + 20 * I) (by norm_num)).mp
  convert hbound using 1 <;> norm_num

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.re_ge_half_of_subexponential
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_subexponential
#print axioms CriticalLinePhasor.SeatingLedger.normalized_decay_of_polynomial_growth
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_polynomial_growth
#print axioms CriticalLinePhasor.SeatingLedger.explicit_polynomial_growth_iff_rh
#print axioms CriticalLinePhasor.SeatingLedger.riemannHypothesis_of_explicit_fixed_anchor_polynomial_growth
