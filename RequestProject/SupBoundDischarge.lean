import RequestProject.SupBound
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The fundamental-domain bound, discharged: Hecke's pointwise bound is unconditional

Completes `SupBound.lean`.  The invariant readout `P = im^k·|f|²` is bounded on the fundamental
domain — on the compact band `√3/2 ≤ im ≤ A` by continuity (the band is the continuous image of
a compact rectangle, no embedding machinery), above `A` by cusp decay against the polynomial
factor — and therefore, by the compiled transport, Hecke's pointwise bound
`|f(z)|² ≤ M·im(z)^{-k}` holds everywhere, unconditionally, from the base fiber's own
modularity.  This is the analytic input the second-moment (Parseval) layer of the `r = 2`
cancellation chain consumes.  No RH/GRH.
-/

open UpperHalfPlane Complex Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Real

namespace CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The invariant readout is continuous. -/
lemma P_continuous (f : CuspForm 𝒮ℒ k) : Continuous (P k f) := by
  apply Continuous.mul
  · exact UpperHalfPlane.continuous_im.zpow₀ k (fun z => Or.inl z.im_pos.ne')
  · exact Complex.continuous_normSq.comp (CuspFormClass.holo f).continuous

/-- The readout is bounded on the band `|re| ≤ 1/2`, `√3/2 ≤ im ≤ A`. -/
lemma P_band_bound (f : CuspForm 𝒮ℒ k) (A : ℝ) :
    ∃ M : ℝ, ∀ z : ℍ, |z.re| ≤ 1 / 2 →
      z.im ∈ Set.Icc (Real.sqrt 3 / 2) A → P k f z ≤ M := by
  rcases lt_or_ge A (Real.sqrt 3 / 2) with hA | hA
  · exact ⟨0, fun z _ him => absurd (him.1.trans him.2) (not_le.mpr hA)⟩
  set K : Set (ℝ × ℝ) := Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Icc (Real.sqrt 3 / 2) A with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty := by
    refine ⟨(0, Real.sqrt 3 / 2), ?_⟩
    constructor
    · rw [Set.mem_Icc]
      norm_num
    · rw [Set.mem_Icc]
      exact ⟨le_refl _, hA⟩
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKc
  haveI : Nonempty ↥K := hKne.to_subtype
  have him_pos : ∀ p : ↥K, 0 < ((p.1.1 : ℂ) + (p.1.2 : ℂ) * Complex.I).im := by
    intro p
    have h2 : Real.sqrt 3 / 2 ≤ p.1.2 := p.2.2.1
    have h3 : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    linarith
  obtain ⟨R, hRc, hRne, hRmem⟩ : ∃ R : Set ℍ, IsCompact R ∧ R.Nonempty ∧
      ∀ z : ℍ, |z.re| ≤ 1 / 2 → z.im ∈ Set.Icc (Real.sqrt 3 / 2) A → z ∈ R := by
    refine ⟨Set.range (fun p : ↥K =>
      (⟨(p.1.1 : ℂ) + (p.1.2 : ℂ) * Complex.I, him_pos p⟩ : ℍ)),
      isCompact_range ?_, Set.range_nonempty _, ?_⟩
    · apply continuous_induced_rng.mpr
      show Continuous fun p : ↥K => ((p.1.1 : ℂ) + (p.1.2 : ℂ) * Complex.I)
      fun_prop
    · intro z hre him
      have hmem : (z.re, z.im) ∈ K := by
        constructor
        · rw [Set.mem_Icc]
          have := abs_le.mp hre
          exact ⟨by linarith [this.1], this.2⟩
        · exact him
      refine ⟨⟨(z.re, z.im), hmem⟩, ?_⟩
      apply UpperHalfPlane.ext
      show (z.re : ℂ) + (z.im : ℂ) * Complex.I = (z : ℂ)
      apply Complex.ext <;> simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  obtain ⟨z₀, -, hz₀⟩ := hRc.exists_isMaxOn hRne (P_continuous f).continuousOn
  exact ⟨P k f z₀, fun z hre him => hz₀ (hRmem z hre him)⟩

/-- Above a computable height the readout is at most one: cusp decay beats the polynomial. -/
lemma P_tail_bound (f : CuspForm 𝒮ℒ k) :
    ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → P k f z ≤ 1 := by
  have hdecay := CuspFormClass.exp_decay_atImInfty (f := f) (h := 1) one_pos
    one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hdecay
  obtain ⟨C, hC⟩ := hdecay
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem] at hC
  obtain ⟨A₀, hA₀⟩ := hC
  set C₁ : ℝ := max C 1 with hC₁def
  have hC₁pos : (0 : ℝ) < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k.toNat
  have hev : ∀ᶠ x : ℝ in atTop, x ^ k.toNat * Real.exp (-x) < (C₁ ^ 2)⁻¹ :=
    hlim.eventually_lt_const (by positivity)
  rw [eventually_atTop] at hev
  obtain ⟨A₁, hA₁⟩ := hev
  refine ⟨max (max A₀ A₁) 1, fun z hz => ?_⟩
  have hzA₀ : A₀ ≤ z.im := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hz
  have hzA₁ : A₁ ≤ z.im := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hz
  have hz1 : (1 : ℝ) ≤ z.im := le_trans (le_max_right _ _) hz
  have hb := hA₀ z hzA₀
  simp only [Set.mem_setOf_eq] at hb
  have hfb : ‖f z‖ ≤ C₁ * Real.exp (-z.im) := by
    calc ‖f z‖ ≤ C * ‖Real.exp (-2 * π * z.im / 1)‖ := hb
      _ ≤ C₁ * Real.exp (-z.im) := by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]
          apply mul_le_mul (le_max_left C 1) ?_ (Real.exp_pos _).le hC₁pos.le
          apply Real.exp_le_exp.mpr
          have hπ : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
          have hzpos := z.im_pos
          nlinarith
  have hnormSq : Complex.normSq (f z) ≤ C₁ ^ 2 * Real.exp (-z.im) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    calc ‖f z‖ ^ 2 ≤ (C₁ * Real.exp (-z.im)) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _) hfb
      _ = C₁ ^ 2 * Real.exp (-z.im) ^ 2 := by ring
  have hzk : z.im ^ k ≤ z.im ^ (k.toNat : ℤ) :=
    zpow_le_zpow_right₀ hz1 (Int.self_le_toNat k)
  have hexp1 : Real.exp (-z.im) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hkey : z.im ^ k.toNat * Real.exp (-z.im) < (C₁ ^ 2)⁻¹ := hA₁ z.im hzA₁
  unfold P
  have himk_pos : (0 : ℝ) < z.im ^ k := zpow_pos z.im_pos k
  calc z.im ^ k * Complex.normSq (f z)
      ≤ z.im ^ k * (C₁ ^ 2 * Real.exp (-z.im) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hnormSq himk_pos.le
    _ ≤ z.im ^ k.toNat * (C₁ ^ 2 * Real.exp (-z.im) ^ 2) := by
        apply mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [← zpow_natCast]
        exact hzk
    _ = C₁ ^ 2 * (z.im ^ k.toNat * Real.exp (-z.im)) * Real.exp (-z.im) := by
        ring
    _ ≤ C₁ ^ 2 * (C₁ ^ 2)⁻¹ * 1 := by
        apply mul_le_mul ?_ hexp1 (Real.exp_pos _).le (by positivity)
        exact mul_le_mul_of_nonneg_left hkey.le (by positivity)
    _ = 1 := by
        field_simp
  -- done

/-- **The readout is bounded on the fundamental domain.** -/
theorem P_fd_bound (f : CuspForm 𝒮ℒ k) :
    ∃ M : ℝ, ∀ z ∈ ModularGroup.fd, P k f z ≤ M := by
  obtain ⟨A, hA⟩ := P_tail_bound f
  obtain ⟨M, hM⟩ := P_band_bound f A
  refine ⟨max M 1, fun z hz => ?_⟩
  rcases le_or_gt z.im A with h | h
  · exact le_trans (hM z hz.2 ⟨fd_im_ge hz, h⟩) (le_max_left _ _)
  · exact le_trans (hA z h.le) (le_max_right _ _)

/-- **Hecke's pointwise bound, unconditional**: `|f(z)|² ≤ M·im(z)^{-k}` everywhere, from the
base fiber's own modularity — the analytic input of the second-moment layer. -/
theorem hecke_pointwise (f : CuspForm 𝒮ℒ k) :
    ∃ M : ℝ, ∀ z : ℍ, Complex.normSq (f z) ≤ M * z.im ^ (-k) := by
  obtain ⟨M, hM⟩ := P_fd_bound f
  exact ⟨M, fun z => hecke_pointwise_of_fdBound f M hM z⟩

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.P_fd_bound
#print axioms CriticalLinePhasor.HeckeSupBound.hecke_pointwise
