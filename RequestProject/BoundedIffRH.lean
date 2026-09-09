import RequestProject.JetsAreAtoms

/-!
# RH is the boundedness of the explicit sequence (ledger 632)

The growth argument of 630 used the ladder only through the minor bound `‖μ_k‖ ≤ μ_0`. Hence a mere
bound `‖μ_k‖ ≤ C` already forces every zero to the line (`re_ge_half_of_bounded`), and conversely under
RH `‖μ_k‖ ≤ Σ m_ρ ω_ρ = μ_0` since every atom is unimodular with positive weight. So

  **`rh_iff_bounded`: RH ⟺ the coefficient sequence at one channel anchor is bounded**, and with 628/631
  **`explicit_bounded_iff_rh`: RH ⟺ the explicit prime-and-Γ sequence at one anchor `Re s < 0` is bounded.**

Equivalently the power series `Σ μ_k z^k` has radius of convergence `1`: the Cayley image of the channel
is the disc, and `ξ′/ξ` is holomorphic on the channel iff RH. In the carrier picture (att632): the prime
side is purely oscillatory on the carrier after the uniform cancels the Poisson DC prime by prime, so the
transported measure is `Γ density − (1/π)|s₀−½−iy|^{−2}·Re Σ Λ(n) n^{−½−iy}`, and its positivity is
Weil's criterion in the anchored class. That positivity is not proved here.
-/

open Complex Finset Filter Topology

namespace CriticalLinePhasor.SeatingLedger

/-- A bounded coefficient sequence has `μ_k/R^k → 0` for every `R > 1`. -/
theorem tendsto_normalized_zero_of_bounded {s : ℂ} {C : ℝ} (hC : ∀ k, ‖xiCoeff s k‖ ≤ C) {R : ℝ}
    (hR : 1 < R) :
    Tendsto (fun k : ℕ => xiCoeff s k / (R : ℂ) ^ k) atTop (𝓝 0) := by
  have hRpos : 0 < R := by linarith
  refine squeeze_zero_norm (a := fun k => C * (R⁻¹) ^ k) (fun k => ?_) ?_
  · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, div_eq_mul_inv,
      ← inv_pow]
    gcongr
    exact hC k
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hRpos.le)
      (inv_lt_one_of_one_lt₀ hR)).const_mul C
    rwa [mul_zero] at this

/-- **The growth contradiction, from boundedness alone**: if the coefficient sequence at a channel anchor
is bounded, no zero lies left of the line. -/
theorem re_ge_half_of_bounded {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2)
    {C : ℝ} (hC : ∀ k, ‖xiCoeff s k‖ ≤ C) (ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
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
    simp only [Set.mem_setOf_eq, hη]; linarith
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
    · simp only [Set.mem_setOf_eq, not_le] at hmem
      have := hρsmax ρ₀ hρ₀A
      rw [hη] at hmem; linarith
  -- the atoms of maximal modulus
  have hBfin : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | ‖transport s ρ.val‖ = R}.Finite :=
    hAfin.subset (fun ρ hρ => by
      simp only [Set.mem_setOf_eq] at hρ ⊢
      have := hρsmax ρ₀ hρ₀A; rw [hρ, hη]; linarith)
  set B : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := hBfin.toFinset with hBdef
  have hρsB : ρs ∈ B := by rw [hBdef, Set.Finite.mem_toFinset]; exact hRdef.symm
  have hBout : ∀ ρ, ρ ∉ B → ‖transport s ρ.val‖ < R := by
    intro ρ hρ
    rw [hBdef, Set.Finite.mem_toFinset] at hρ
    simp only [Set.mem_setOf_eq] at hρ
    exact lt_of_le_of_ne (hRall ρ.val ρ.property) hρ
  -- the finite part tends to zero
  have hsplit : ∀ k : ℕ, ∑ ρ ∈ B, nterm s R ρ k
      = xiCoeff s k / (R : ℂ) ^ k
        - ∑' ρ : ↑((↑B : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})ᶜ), nterm s R ρ.val k := by
    intro k
    rw [xiCoeff_div_pow, ← (summable_nterm hs hRall hRpos k).sum_add_tsum_compl (s := B)]
    ring
  have hF : Tendsto (fun k : ℕ => ∑ ρ ∈ B, nterm s R ρ k) atTop (𝓝 0) := by
    have := (tendsto_normalized_zero_of_bounded hC hR1).sub (tendsto_tail_zero hs hRpos hRall B hBout)
    rw [sub_zero] at this
    exact this.congr (fun k => (hsplit k).symm)
  -- twist by the conjugate of the maximal atom and take Cesàro means
  set u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun ρ => transport s ρ.val / (R : ℂ) with hu
  have hu1 : ∀ ρ ∈ B, ‖u ρ‖ = 1 := by
    intro ρ hρ
    rw [hBdef, Set.Finite.mem_toFinset] at hρ
    simp only [Set.mem_setOf_eq] at hρ
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


/-- **Bounded ⟹ RH.** -/
theorem rh_of_bounded {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2) {C : ℝ}
    (hC : ∀ k, ‖xiCoeff s k‖ ≤ C) : RH := by
  intro ρ hρ
  have h1 : 1 / 2 ≤ ρ.re := re_ge_half_of_bounded hs hs' hC ⟨ρ, hρ⟩
  have h2 : 1 / 2 ≤ (1 - (starRingEnd ℂ) ρ).re :=
    re_ge_half_of_bounded hs hs' hC ⟨_, mirror_mem_nontrivialZeros hρ⟩
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h2
  linarith

/-- **RH ⟹ bounded**, by the minor bound of the ladder. -/
theorem bounded_of_rh {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hRH : RH) :
    ∀ k, ‖xiCoeff s k‖ ≤ (xiCoeff s 0).re :=
  ladder_coeff_bound (ladder_of_rh hs hRH)

/-- **RH is the boundedness of the coefficient sequence at one channel anchor.** -/
theorem rh_iff_bounded {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2) :
    RH ↔ ∃ C : ℝ, ∀ k, ‖xiCoeff s k‖ ≤ C :=
  ⟨fun h => ⟨_, bounded_of_rh hs h⟩, fun ⟨_, hC⟩ => rh_of_bounded hs hs' hC⟩

/-- **RH is the boundedness of the explicit prime-and-Γ sequence at one anchor `Re s < 0`.** -/
theorem explicit_bounded_iff_rh {s : ℂ} (hs : s.re < 0) :
    (∃ C : ℝ, ∀ k, ‖toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets explicitLogDeriv s) k‖ ≤ C) ↔ RH := by
  have hs0 : s ∉ ZD.NontrivialZeros := notMem_nontrivialZeros_of_re_nonpos hs.le
  have hs' : s.re ≠ 1 / 2 := by intro h; linarith
  have hseq : ∀ k, toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets explicitLogDeriv s) k = xiCoeff s k := by
    intro k
    rw [← jets_xiLogDeriv_eq_explicit hs, toeplitzCoeff_jets_eq_xiCoeff hs0 hs' k]
  simp only [hseq]
  exact (rh_iff_bounded hs0 (by linarith)).symm

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.re_ge_half_of_bounded
#print axioms CriticalLinePhasor.SeatingLedger.rh_iff_bounded
#print axioms CriticalLinePhasor.SeatingLedger.explicit_bounded_iff_rh
