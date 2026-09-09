import RequestProject.LadderMinor

/-!
# The ladder at one anchor, part 2b: `ladder ⟹ RH`, and the equivalence (ledger 630)

If a zero `ρ₀` lies left of the line, its transported atom has `‖w_{ρ₀}‖ > 1` (`one_lt_norm_transport_iff`).
The moduli `‖w_ρ‖ ≥ 1 + η` occur for finitely many zeros (`finite_transport_ge`), so the largest modulus
`R > 1` is attained by a finite nonempty set `B` of atoms. Normalising, `μ_k/R^k` splits into the finite
sum over `B` and a tail that tends to `0` by dominated convergence. The ladder's minor bound
`‖μ_k‖ ≤ μ_0` forces `μ_k/R^k → 0`, hence the finite almost-periodic sum `Σ_{ρ∈B} m_ρ ω_ρ u_ρ^k` tends
to `0` with `u_ρ` distinct unimodular; its Cesàro means against `conj(u_{ρ*})^k` tend to `m_{ρ*} ω_{ρ*} ≠ 0`,
a contradiction. Hence every zero has `Re ρ ≥ ½`, and by mirror symmetry `Re ρ = ½`.

**`anchor_ladder_iff_rh`: at any anchor `s` in the channel off the zero set, `Ladder s ↔ RH`.**
-/

open Complex Finset Filter Topology

namespace CriticalLinePhasor.SeatingLedger

/-- The normalised atom term `m_ρ ω_ρ (w_ρ/R)^k`. -/
noncomputable def nterm (s : ℂ) (R : ℝ) (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) (k : ℕ) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) * atomWeight s ρ.val * (transport s ρ.val / (R : ℂ)) ^ k

theorem xiCoeff_div_pow (s : ℂ) (R : ℝ) (k : ℕ) :
    xiCoeff s k / (R : ℂ) ^ k = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, nterm s R ρ k := by
  unfold xiCoeff nterm
  rw [← tsum_div_const]
  apply tsum_congr
  intro ρ
  rw [div_pow]
  ring

theorem norm_nterm_le {s : ℂ} {R : ℝ} (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hR : ‖transport s ρ.val‖ ≤ R) (hRpos : 0 < R) (k : ℕ) :
    ‖nterm s R ρ k‖ ≤ (ZD.xiOrderNat ρ.val : ℝ) * ‖atomWeight s ρ.val‖ := by
  unfold nterm
  rw [norm_mul, norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hRpos, Complex.norm_natCast]
  have h1 : ‖transport s ρ.val‖ / R ≤ 1 := by rw [div_le_one hRpos]; exact hR
  have h2 : (‖transport s ρ.val‖ / R) ^ k ≤ 1 :=
    pow_le_one₀ (by positivity) h1
  calc (ZD.xiOrderNat ρ.val : ℝ) * ‖atomWeight s ρ.val‖ * (‖transport s ρ.val‖ / R) ^ k
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * ‖atomWeight s ρ.val‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem summable_nterm {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) {R : ℝ}
    (hR : ∀ ρ ∈ ZD.NontrivialZeros, ‖transport s ρ‖ ≤ R) (hRpos : 0 < R) (k : ℕ) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => nterm s R ρ k) :=
  Summable.of_norm_bounded (summable_absWeight hs)
    (fun ρ => norm_nterm_le ρ (hR ρ.val ρ.property) hRpos k)

/-- Only finitely many transported atoms have modulus `≥ 1 + η`. -/
theorem finite_transport_ge {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) {η : ℝ} (hη : 0 < η) :
    {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | 1 + η ≤ ‖transport s ρ.val‖}.Finite := by
  set M : ℝ := |2 * s.re - 1| / ((1 + η) ^ 2 - 1) with hM
  have hden : 0 < (1 + η) ^ 2 - 1 := by nlinarith
  have hMnn : 0 ≤ M := by positivity
  have hfin := ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (‖s‖ + Real.sqrt M)
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  simp only [Set.mem_setOf_eq] at hρ
  refine ⟨ρ.property, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h : s - ρ.val ≠ 0 := sub_ne_zero_of_notMem hs ρ.property
  have hnpos : 0 < Complex.normSq (s - ρ.val) := by rw [Complex.normSq_pos]; exact h
  have hsq := norm_transport_sq s ρ.val h
  have hnum : (2 * ρ.val.re - 1) * (2 * s.re - 1) ≤ |2 * s.re - 1| := by
    obtain ⟨h1, h2, -⟩ := ρ.property
    calc (2 * ρ.val.re - 1) * (2 * s.re - 1) ≤ |(2 * ρ.val.re - 1) * (2 * s.re - 1)| := le_abs_self _
      _ = |2 * ρ.val.re - 1| * |2 * s.re - 1| := abs_mul _ _
      _ ≤ 1 * |2 * s.re - 1| := by gcongr; rw [abs_le]; constructor <;> linarith
      _ = |2 * s.re - 1| := one_mul _
  have hbig : (1 + η) ^ 2 ≤ ‖transport s ρ.val‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hρ 2
  rw [hsq] at hbig
  have hle : (1 + η) ^ 2 - 1 ≤ |2 * s.re - 1| / Complex.normSq (s - ρ.val) := by
    have := div_le_div_of_nonneg_right hnum hnpos.le
    linarith
  have hnormSq : Complex.normSq (s - ρ.val) ≤ M := by
    rw [hM, le_div_iff₀ hden]
    rw [le_div_iff₀ hnpos] at hle
    linarith
  have hdist : ‖s - ρ.val‖ ≤ Real.sqrt M := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq]
    exact Real.sqrt_le_sqrt hnormSq
  calc ‖ρ.val‖ = ‖s - (s - ρ.val)‖ := by ring_nf
    _ ≤ ‖s‖ + ‖s - ρ.val‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + Real.sqrt M := by linarith

/-- The normalised tail over the atoms strictly inside modulus `R` tends to `0`. -/
theorem tendsto_tail_zero {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) {R : ℝ} (hRpos : 0 < R)
    (hR : ∀ ρ ∈ ZD.NontrivialZeros, ‖transport s ρ‖ ≤ R)
    (B : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hB : ∀ ρ, ρ ∉ B → ‖transport s ρ.val‖ < R) :
    Tendsto (fun k : ℕ => ∑' ρ : ↑((↑B : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})ᶜ), nterm s R ρ.val k)
      atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun (k : ℕ) (ρ : ↑((↑B : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})ᶜ)) => nterm s R ρ.val k)
    (g := fun _ => 0)
    (bound := fun ρ => (ZD.xiOrderNat ρ.val.val : ℝ) * ‖atomWeight s ρ.val.val‖)
    (𝓕 := atTop)
    ((summable_absWeight hs).subtype _)
    (fun ρ => by
      have hlt : ‖transport s ρ.val.val / (R : ℂ)‖ < 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, div_lt_one hRpos]
        exact hB ρ.val ρ.property
      have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt).const_mul
        ((ZD.xiOrderNat ρ.val.val : ℂ) * atomWeight s ρ.val.val)
      rw [mul_zero] at this
      exact this)
    (Eventually.of_forall (fun k ρ => norm_nterm_le ρ.val (hR _ ρ.val.property) hRpos k))
  simpa using h

/-- The ladder forces the normalised sequence `μ_k/R^k` to `0` for any `R > 1`. -/
theorem tendsto_normalized_zero {s : ℂ} (hL : Ladder s) {R : ℝ} (hR : 1 < R) :
    Tendsto (fun k : ℕ => xiCoeff s k / (R : ℂ) ^ k) atTop (𝓝 0) := by
  have hRpos : 0 < R := by linarith
  refine squeeze_zero_norm (a := fun k => (xiCoeff s 0).re * (R⁻¹) ^ k) (fun k => ?_) ?_
  · rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, div_eq_mul_inv,
      ← inv_pow]
    gcongr
    exact ladder_coeff_bound hL k
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hRpos.le)
      (inv_lt_one_of_one_lt₀ hR)).const_mul ((xiCoeff s 0).re)
    rwa [mul_zero] at this

/-- Cesàro means of a unimodular geometric sequence `v ≠ 1` tend to `0`. -/
theorem tendsto_cesaro_geom_zero {v : ℂ} (hv : ‖v‖ = 1) (hv1 : v ≠ 1) :
    Tendsto (fun K : ℕ => ((K : ℝ)⁻¹ : ℝ) • ∑ k ∈ range K, v ^ k) atTop (𝓝 0) := by
  have hne : v - 1 ≠ 0 := sub_ne_zero.mpr hv1
  refine squeeze_zero_norm (a := fun K : ℕ => (K : ℝ)⁻¹ * (2 / ‖v - 1‖)) (fun K => ?_) ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg K)),
      geom_sum_eq hv1, norm_div]
    gcongr
    calc ‖v ^ K - 1‖ ≤ ‖v ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hv, one_pow, norm_one]; norm_num
  · have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (2 / ‖v - 1‖)
    rwa [zero_mul] at this

/-- **The growth contradiction**: at a ladder anchor in the channel no zero lies left of the line. -/
theorem re_ge_half_of_ladder {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2)
    (hL : Ladder s) (ρ₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) : 1 / 2 ≤ ρ₀.val.re := by
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
    have := (tendsto_normalized_zero hL hR1).sub (tendsto_tail_zero hs hRpos hRall B hBout)
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

/-- **`ladder ⟹ RH`** at any anchor in the channel off the zero set. -/
theorem rh_of_ladder {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2) (hL : Ladder s) :
    RH := by
  intro ρ hρ
  have h1 : 1 / 2 ≤ ρ.re := re_ge_half_of_ladder hs hs' hL ⟨ρ, hρ⟩
  have h2 : 1 / 2 ≤ (1 - (starRingEnd ℂ) ρ).re :=
    re_ge_half_of_ladder hs hs' hL ⟨_, mirror_mem_nontrivialZeros hρ⟩
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h2
  linarith

/-- **One anchor's ladder is equivalent to RH.** -/
theorem anchor_ladder_iff_rh {s : ℂ} (hs : s ∉ ZD.NontrivialZeros) (hs' : s.re < 1 / 2) :
    Ladder s ↔ RH :=
  ⟨rh_of_ladder hs hs', ladder_of_rh hs⟩

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.re_ge_half_of_ladder
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_ladder
#print axioms CriticalLinePhasor.SeatingLedger.anchor_ladder_iff_rh
