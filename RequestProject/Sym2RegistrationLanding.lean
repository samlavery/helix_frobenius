import RequestProject.RSPairInterface
import RequestProject.ZetaPeelSkeleton
import RequestProject.FunctorialityCancellation
import RequestProject.RSSeriesFactorization
import RequestProject.Sym2CoefficientIdentification

/-!
# The r = 2 registration landing: the peeled Sym² bank in the prescribed Γ-chart

Composition of the compiled r = 2 assets toward the r = 2 standing wave — the functional
equation of the ζ-peeled Rankin–Selberg readout (the Sym² bank) in its prescribed chart.
Everything proven here is unconditional.  The chain:

* `peeledProfile` / `peeledProfile_mellin` — the Möbius-dilated averaged profile
  `θ_μ(θ̄_f − ‖f‖²)` and its Mellin identification `ζ(s)⁻¹ · Λ̄(s)` on `1 < Re s`
  (`ZetaPeel.zetaPeel_mellin` composed with the compiled averaged-pair readout).
* `peeledFE` — **the peeled functional equation, global and division-free**: for every
  `s ∈ ℂ`, `Λζ(s) · Λ̄(1−s) = Λζ(1−s) · Λ̄(s)` — the self-dual reflection of the averaged
  pair welded to the reflection of the completed ζ it peels.  `peeledFE_gammaChart` /
  `peeledFE_gammaChart_strip` put it in the `Γℝ`-chart: the reflection cost of the peeled
  object is exactly the peeled ζ's own chart factor `Γℝ`.
* `rankinSquareNorm_LSeriesSummable` / `rankinNorm_sym2_transfer` — the Deligne-normalized
  Rankin square `b_n = ‖a_n‖²/n^{k−1}` is L-series-summable on `2 < Re s`, where its ζ-factor
  peels: `L(b, s) = ζ(s) · L(μ ⋆ b, s)`.
* `LSeries_rankinSquare_shift` / `rsSeries_eq_LSeriesNorm` — axis bookkeeping: the compiled
  un-normalized readout at `w = s + k − 1` **is** the normalized readout at `s`; the master
  series is `(4π)^{−(s+k−1)} · L(b, s)`-scaled.
* `rsAveraged_lambda_eq_pairing` — **the Fubini bridge**: on `1 < Re s` the completed
  averaged transform is the fundamental-domain pairing of the Petersson density with the
  pointwise Epstein completion, `Λ̄(s) = ∫_𝒟 P(z) · Λ_z(s)` — the Mellin transform exchanged
  with the Petersson average (product integrability from the compiled tail bounds, swap by
  `integral_integral_swap`).
* `peeled_readout_gammaChart` — **the landing**: on `2 < Re s`,

  `mellin (θ_μ(θ̄_f − ‖f‖²)) s
     = 2^{−k} · ζ(2s) · Γℝ(s)·Γℝ(s+1)·Γℝ(s+k−1)·Γℝ(s+k) · L(μ ⋆ b, s)`

  — the ζ-peeled Rankin square readout in the prescribed degree-4 `Γℝ`-chart with shifts
  `[0, 1, k−1, k]`, the `Γℝ(s)` factor being the peeled ζ's own chart factor and `ζ(2s)`
  the Satake-redundancy dressing of `L(μ ⋆ b, s)`.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter ArithmeticFunction
open scoped Real MatrixGroups Topology LSeries.notation ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Sym2Registration

open CriticalLinePhasor.Unfolding CriticalLinePhasor.HeckeSupBound
  CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.CarrierTheta CriticalLinePhasor.ZetaPeel

variable {k : ℤ}

/-! ## The peeled profile and its Mellin identification -/

/-- **The peeled profile**: the Möbius-weighted dilation resummation of the averaged
lattice-bank tail `θ̄_f − ‖f‖²` — the carrier-level object whose Mellin readout is the
averaged completion with one ζ-factor divided out. -/
noncomputable def peeledProfile (k : ℤ) (f : CuspForm 𝒮ℒ k) : ℝ → ℂ :=
  theta moebiusSeq (fun t => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))

/-- The peeled profile's Mellin transform converges and equals `ζ(s)⁻¹ · Λ̄(s)` on
`1 < Re s` — the zeta-peel engine applied to the compiled averaged-pair readout. -/
theorem peeledProfile_hasMellin (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    HasMellin (peeledProfile k f) s
      ((riemannZeta s)⁻¹ * (rsAveragedWeakFEPair f hk).Λ s) := by
  have h := zetaPeel_hasMellin
    (fun t => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))
    (rsAveraged_mellinConvergent f hk hs) hs
  rwa [rsAveraged_mellin_eq f hk hs] at h

/-- **The peeled Mellin identification** on `1 < Re s`:
`mellin (θ_μ(θ̄_f − ‖f‖²)) s = ζ(s)⁻¹ · Λ̄(s)`. -/
theorem peeledProfile_mellin (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    mellin (peeledProfile k f) s =
      (riemannZeta s)⁻¹ * (rsAveragedWeakFEPair f hk).Λ s :=
  (peeledProfile_hasMellin f hk hs).2

/-! ## The peeled functional equation -/

/-- **The peeled functional equation, global and division-free**: for every `s ∈ ℂ`,

  `Λζ(s) · Λ̄(1−s) = Λζ(1−s) · Λ̄(s)`.

The self-dual reflection `Λ̄(1−s) = Λ̄(s)` of the averaged pair (the lattice weld carried
through the Petersson average) welded to the reflection `Λζ(1−s) = Λζ(s)` of the completed
ζ it peels: the cross-multiplied functional equation of the peeled quotient `Λ̄/Λζ`,
stated without division so it holds at every point of the plane. -/
theorem peeledFE (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ) :
    completedRiemannZeta s * (rsAveragedWeakFEPair f hk).Λ (1 - s) =
      completedRiemannZeta (1 - s) * (rsAveragedWeakFEPair f hk).Λ s := by
  rw [rsAveraged_selfdual_FE f hk s, completedRiemannZeta_one_sub]

/-- **The peeled functional equation in the `Γℝ`-chart**: away from `{0, 1}` and the zeros
of the two `Γℝ`-factors,

  `ζ(s)·Γℝ(s) · Λ̄(1−s) = ζ(1−s)·Γℝ(1−s) · Λ̄(s)`

— the reflection cost of the peeled object is exactly the peeled ζ's own chart factor. -/
theorem peeledFE_gammaChart (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) (hΓ' : Gammaℝ (1 - s) ≠ 0) :
    riemannZeta s * Gammaℝ s * (rsAveragedWeakFEPair f hk).Λ (1 - s) =
      riemannZeta (1 - s) * Gammaℝ (1 - s) * (rsAveragedWeakFEPair f hk).Λ s := by
  have h1 : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp
  have h2 : riemannZeta (1 - s) * Gammaℝ (1 - s) = completedRiemannZeta (1 - s) := by
    rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr (Ne.symm hs1))]
    field_simp
  rw [h1, h2]
  exact peeledFE f hk s

/-- The `Γℝ`-chart peeled functional equation on the open critical strip
`0 < Re s < 1`, where all side conditions discharge automatically. -/
theorem peeledFE_gammaChart_strip (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s * Gammaℝ s * (rsAveragedWeakFEPair f hk).Λ (1 - s) =
      riemannZeta (1 - s) * Gammaℝ (1 - s) * (rsAveragedWeakFEPair f hk).Λ s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have h0' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact peeledFE_gammaChart f hk hs0 hs1
    (Gammaℝ_ne_zero_of_re_pos h0) (Gammaℝ_ne_zero_of_re_pos h0')

/-! ## The normalized coefficient side -/

/-- The Deligne-normalized Rankin square `b_n = ‖a_n‖²/n^{k−1}` is L-series-summable on
`2 < Re s` — the compiled Rankin–Dirichlet convergence, with the `(4π)`-scale and the
`n^{k−1}` normalization moved across the comparison. -/
theorem rankinSquareNorm_LSeriesSummable (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    LSeriesSummable (⇑(rankinSquareNorm f)) s := by
  have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  apply Summable.of_norm
  have hdir := (summable_rankin_dirichlet f
    (σ := s.re + (k : ℝ) - 1) (by linarith)).mul_left ((4 * π) ^ (s.re + (k : ℝ) - 1))
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hdir
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [if_pos rfl]
    positivity
  · rw [if_neg hn]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn1
    have hcoe : ‖(⇑(rankinSquareNorm f) : ℕ → ℂ) n‖ =
        ‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) - 1) := by
      rw [rankinSquareNorm, toArithmeticFunction]
      simp only [ArithmeticFunction.coe_mk, if_neg hn]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hcoe]
    have key : ‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) - 1) / (n : ℝ) ^ s.re =
        (4 * π) ^ (s.re + (k : ℝ) - 1) *
          (‖(qExpansion 1 f).coeff n‖ ^ 2 / (4 * π * n) ^ (s.re + (k : ℝ) - 1)) := by
      rw [Real.mul_rpow (by positivity) hnp.le,
        show s.re + (k : ℝ) - 1 = s.re + ((k : ℝ) - 1) from by ring,
        Real.rpow_add hnp]
      have h4π : (0 : ℝ) < (4 * π) ^ (s.re + ((k : ℝ) - 1)) :=
        Real.rpow_pos_of_pos (by positivity) _
      have hns : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hnp _
      have hnk : (0 : ℝ) < (n : ℝ) ^ ((k : ℝ) - 1) := Real.rpow_pos_of_pos hnp _
      field_simp
    exact key.le

/-- **The normalized Sym² transfer** on `2 < Re s`:
`L(b, s) = ζ(s) · L(μ ⋆ b, s)` for the Deligne-normalized Rankin square `b`. -/
theorem rankinNorm_sym2_transfer (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    LSeries (⇑(rankinSquareNorm f)) s =
      riemannZeta s *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s :=
  moebius_zeta_transfer _ (by linarith) (rankinSquareNorm_LSeriesSummable f hk hs)

/-- **Axis bookkeeping**: the un-normalized Rankin square L-series at the shifted argument
`s + k − 1` is term-by-term the normalized one at `s` — the `n^{k−1}` normalization is the
axis shift.  Unconditional (term-wise identity of the defining sums). -/
theorem LSeries_rankinSquare_shift (f : CuspForm 𝒮ℒ k) (s : ℂ) :
    LSeries (⇑(rankinSquare f)) (s + (k : ℂ) - 1) =
      LSeries (⇑(rankinSquareNorm f)) s := by
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hcoeS : (⇑(rankinSquare f) : ℕ → ℂ) n =
        ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) := by
      rw [rankinSquare, toArithmeticFunction]
      simp only [ArithmeticFunction.coe_mk, if_neg hn]
    have hcoeN : (⇑(rankinSquareNorm f) : ℕ → ℂ) n =
        ((‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) - 1) : ℝ) : ℂ) := by
      rw [rankinSquareNorm, toArithmeticFunction]
      simp only [ArithmeticFunction.coe_mk, if_neg hn]
    have hpow : (((n : ℝ) ^ ((k : ℝ) - 1) : ℝ) : ℂ) = (n : ℂ) ^ ((k : ℂ) - 1) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    have hsplit : (n : ℂ) ^ (s + (k : ℂ) - 1) = (n : ℂ) ^ s * (n : ℂ) ^ ((k : ℂ) - 1) := by
      rw [show s + (k : ℂ) - 1 = s + ((k : ℂ) - 1) from by ring, cpow_add _ _ hnc]
    rw [hcoeS, hcoeN, hsplit, Complex.ofReal_div, hpow, div_div, mul_comm ((n : ℂ) ^ ((k : ℂ) - 1))]

/-- **The normalized-series display** on `2 < Re s`: the master-equation series is the
`(4π)^{−(s+k−1)}`-scaled normalized L-series at `s`. -/
theorem rsSeries_eq_LSeriesNorm (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    ∑' n : ℕ, ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
        ((4 * π * n : ℝ) : ℂ) ^ (s + (k : ℂ) - 1) =
      ((4 * π : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) *
        LSeries (⇑(rankinSquareNorm f)) s := by
  have hw : (k : ℝ) + 1 < (s + (k : ℂ) - 1).re := by
    have : (s + (k : ℂ) - 1).re = s.re + (k : ℝ) - 1 := by
      simp [Complex.add_re, Complex.sub_re]
    rw [this]
    linarith
  rw [rsSeries_eq_LSeries f hk hw, LSeries_rankinSquare_shift f s]

/-! ## The Fubini bridge -/

/-- The averaged tail is the fundamental-domain pairing of the Petersson density with the
pointwise bank tail, real form, at every positive carrier height. -/
lemma averagedTheta_sub_mass (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {t : ℝ} (ht : 0 < t) :
    averagedTheta k f t - peterssonMass k f =
      ∫ z in ModularGroup.fd, P k f z * (latticeTheta z t - 1) ∂volume := by
  unfold averagedTheta peterssonMass
  rw [← MeasureTheory.integral_sub (integrableOn_P_mul_theta f hk ht)
    (integrableOn_P_fd f)]
  refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  ring

/-- **The Fubini bridge**: on `1 < Re s` the completed averaged transform is the
fundamental-domain pairing of the Petersson density with the pointwise Epstein completion,

  `Λ̄(s) = ∫_𝒟 P(z) · Λ_z(s)`.

The Mellin transform of the averaged tail is exchanged with the Petersson average: the
product integrand is jointly measurable (compiled bank measurability), its `z`-sections
are integrable at every height (compiled tail integrability), and the outer norm integral
is exactly the convergent Mellin norm integral of the averaged tail — so the swap is
`integral_integral_swap`, and each inner integral is the compiled Epstein readout. -/
theorem rsAveraged_lambda_eq_pairing (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    (rsAveragedWeakFEPair f hk).Λ s =
      ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s ∂volume := by
  haveI hfin : IsFiniteMeasure ((volume : Measure ℍ).restrict ModularGroup.fd) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_fd_lt_top⟩
  set F : ℝ → ℍ → ℂ := fun t z =>
    ((t : ℂ) ^ (s - 1)) • (((P k f z : ℝ) : ℂ) * (latticeThetaC z t - 1)) with hFdef
  -- joint measurability
  have hPmeas : Measurable fun p : ℝ × ℍ =>
      ((P k f p.2 : ℝ) : ℂ) * (latticeThetaC p.2 p.1 - 1) := by
    have hP : Measurable fun p : ℝ × ℍ => ((P k f p.2 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((P_continuous f).measurable.comp measurable_snd)
    have hLT : Measurable fun p : ℝ × ℍ => (latticeThetaC p.2 p.1 : ℂ) :=
      Complex.measurable_ofReal.comp (measurable_latticeTheta.comp
        (measurable_snd.prodMk measurable_fst))
    exact hP.mul (hLT.sub measurable_const)
  have hcp : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi 0)).prod (volume.restrict ModularGroup.fd)) :=
    hcp.comp_fst.smul hPmeas.aestronglyMeasurable
  -- pointwise norm identity on positive heights
  have hptw : ∀ t : ℝ, 0 < t → ∀ z : ℍ,
      ‖F t z‖ = ‖(t : ℂ) ^ (s - 1)‖ * (P k f z * (latticeTheta z t - 1)) := by
    intro t ht z
    have h1 : latticeThetaC z t - 1 = ((latticeTheta z t - 1 : ℝ) : ℂ) := by
      rw [latticeThetaC]
      push_cast
      ring
    rw [hFdef]
    simp only [norm_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (P_nonneg f z), h1]
    rw [Real.norm_of_nonneg (by linarith [one_le_latticeTheta z ht])]
  -- the outer norm integral is the Mellin norm integrand of the averaged tail
  have hnorm_eq : ∀ t : ℝ, 0 < t →
      (∫ z in ModularGroup.fd, ‖F t z‖ ∂volume) =
        ‖(t : ℂ) ^ (s - 1) •
          (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))‖ := by
    intro t ht
    calc ∫ z in ModularGroup.fd, ‖F t z‖ ∂volume
        = ∫ z in ModularGroup.fd,
            ‖(t : ℂ) ^ (s - 1)‖ * (P k f z * (latticeTheta z t - 1)) ∂volume :=
          setIntegral_congr_fun measurableSet_fd fun z _ => hptw t ht z
      _ = ‖(t : ℂ) ^ (s - 1)‖ * (averagedTheta k f t - peterssonMass k f) := by
          rw [MeasureTheory.integral_const_mul, ← averagedTheta_sub_mass f hk ht]
      _ = ‖(t : ℂ) ^ (s - 1) •
            (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))‖ := by
          rw [norm_smul, averagedThetaC, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_of_nonneg
              (by linarith [peterssonMass_le_averagedTheta f hk ht])]
  -- product integrability
  have hMC := rsAveraged_mellinConvergent f hk hs
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi 0)).prod (volume.restrict ModularGroup.fd)) := by
    rw [MeasureTheory.integrable_prod_iff hmeas]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hbase : IntegrableOn (fun z : ℍ => P k f z * (latticeTheta z t - 1))
          ModularGroup.fd volume := integrableOn_P_mul_tail' f hk ht0
      have hbaseC : IntegrableOn
          (fun z : ℍ => ((P k f z : ℝ) : ℂ) * (latticeThetaC z t - 1))
          ModularGroup.fd volume := by
        refine (hbase.ofReal (𝕜 := ℂ)).congr (ae_of_all _ fun z => ?_)
        show ((P k f z * (latticeTheta z t - 1) : ℝ) : ℂ) =
          ((P k f z : ℝ) : ℂ) * (latticeThetaC z t - 1)
        rw [show latticeThetaC z t = ((latticeTheta z t : ℝ) : ℂ) from rfl]
        push_cast
        ring
      exact hbaseC.smul ((t : ℂ) ^ (s - 1))
    · have hnorm : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) •
          (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))‖)
          (volume.restrict (Ioi 0)) := hMC.norm
      refine hnorm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hnorm_eq t ht).symm
  -- the swap and the two readouts
  have hswap := MeasureTheory.integral_integral_swap hint
  calc (rsAveragedWeakFEPair f hk).Λ s
      = mellin (fun t : ℝ =>
          averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)) s :=
        (rsAveraged_mellin_eq f hk hs).symm
    _ = ∫ t in Ioi (0 : ℝ), ∫ z in ModularGroup.fd, F t z ∂volume ∂volume := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        show (t : ℂ) ^ (s - 1) •
            (averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)) =
          ∫ z in ModularGroup.fd, F t z ∂volume
        rw [averagedThetaC_sub_mass f hk ht, ← MeasureTheory.integral_smul]
    _ = ∫ z in ModularGroup.fd, ∫ t in Ioi (0 : ℝ), F t z ∂volume ∂volume := hswap
    _ = ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s ∂volume := by
        refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
        have h1 : ∀ t : ℝ, F t z =
            ((P k f z : ℝ) : ℂ) * ((t : ℂ) ^ (s - 1) • (latticeThetaC z t - 1)) := by
          intro t
          rw [hFdef]
          simp only [smul_eq_mul]
          ring
        calc ∫ t in Ioi (0 : ℝ), F t z ∂volume
            = ∫ t in Ioi (0 : ℝ), ((P k f z : ℝ) : ℂ) *
                ((t : ℂ) ^ (s - 1) • (latticeThetaC z t - 1)) ∂volume :=
              setIntegral_congr_fun measurableSet_Ioi fun t _ => h1 t
          _ = ((P k f z : ℝ) : ℂ) *
                ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • (latticeThetaC z t - 1) ∂volume :=
              MeasureTheory.integral_const_mul _ _
          _ = ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s := by
              rw [show (∫ t in Ioi (0 : ℝ),
                  (t : ℂ) ^ (s - 1) • (latticeThetaC z t - 1) ∂volume) =
                  mellin (fun t : ℝ => latticeThetaC z t - 1) s from rfl,
                epstein_mellin_eq z hs]

/-! ## The Γ-chart registration -/

/-- Legendre duplication in the readout chart: `Γ(s)·π^{−s} = (2^s/2)·Γℝ(s)·Γℝ(s+1)`. -/
lemma Gamma_mul_pi_cpow (s : ℂ) :
    Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) =
      (2 : ℂ) ^ s / 2 * (Gammaℝ s * Gammaℝ (s + 1)) := by
  rw [Gammaℝ_mul_Gammaℝ_add_one s, Gammaℂ_def]
  rw [show ((2 : ℂ) * (π : ℂ)) ^ (-s) = (2 : ℂ) ^ (-s) * ((π : ℝ) : ℂ) ^ (-s) from by
    rw [show ((2 : ℂ) * (π : ℂ)) = (((2 : ℝ)) : ℂ) * ((π : ℝ) : ℂ) from by norm_num,
      mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le,
      show (((2 : ℝ)) : ℂ) = (2 : ℂ) from by norm_num]]
  have h2s : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ two_ne_zero]
    simp
  linear_combination (-(((π : ℝ) : ℂ) ^ (-s) * Complex.Gamma s)) * h2s

/-- Legendre duplication in the `4π` readout chart:
`Γ(w)·(4π)^{−w} = (2^{−w}/2)·Γℝ(w)·Γℝ(w+1)`. -/
lemma Gamma_mul_fourpi_cpow (w : ℂ) :
    Complex.Gamma w * ((4 * π : ℝ) : ℂ) ^ (-w) =
      (2 : ℂ) ^ (-w) / 2 * (Gammaℝ w * Gammaℝ (w + 1)) := by
  rw [Gammaℝ_mul_Gammaℝ_add_one w, Gammaℂ_def]
  rw [show ((4 * π : ℝ) : ℂ) = (((2 : ℝ)) : ℂ) * (((2 : ℝ) * π : ℝ) : ℂ) from by
      push_cast; ring,
    show ((((2 : ℝ)) : ℂ) * (((2 : ℝ) * π : ℝ) : ℂ)) ^ (-w) =
        (((2 : ℝ)) : ℂ) ^ (-w) * (((2 : ℝ) * π : ℝ) : ℂ) ^ (-w) from
      mul_cpow_ofReal_nonneg (by norm_num) (by positivity) (-w),
    show ((2 : ℂ) * (π : ℂ)) = (((2 : ℝ) * π : ℝ) : ℂ) from by push_cast; ring,
    show (((2 : ℝ)) : ℂ) = (2 : ℂ) from by norm_num]
  ring

/-- **The landing: the peeled Sym² readout in the prescribed `Γℝ`-chart.**  On `2 < Re s`,

  `mellin (θ_μ(θ̄_f − ‖f‖²)) s
     = 2^{−k} · ζ(2s) · Γℝ(s)·Γℝ(s+1)·Γℝ(s+k−1)·Γℝ(s+k) · L(μ ⋆ b, s)`

with `b_n = ‖a_n‖²/n^{k−1}` the Deligne-normalized Rankin square: the ζ-peeled readout of
the averaged lattice bank is the normalized Möbius-peeled L-series dressed by the
Satake-redundancy factor `ζ(2s)`, in the degree-4 `Γℝ`-chart with shifts `[0, 1, k−1, k]`
(`Γℝ(s)` being the peeled ζ's own chart factor).  Identifying `ζ(2s)·L(μ ⋆ b, s)` with the
Sym²-Satake Euler product is Hecke multiplicativity. -/
theorem peeled_readout_gammaChart (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    mellin (peeledProfile k f) s =
      (2 : ℂ) ^ (-(k : ℂ)) * riemannZeta (2 * s) *
        (Gammaℝ s * Gammaℝ (s + 1) * Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))) *
        LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s := by
  have hs1 : 1 < s.re := by linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hB : (rsAveragedWeakFEPair f hk).Λ s =
      Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) * (2 * riemannZeta (2 * s)) *
        (Complex.Gamma (s + (k : ℂ) - 1) * ∑' n : ℕ,
          ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
            ((4 * π * n : ℝ) : ℂ) ^ (s + (k : ℂ) - 1)) := by
    rw [rsAveraged_lambda_eq_pairing f hk hs1, rs_master f hk hs]
  rw [peeledProfile_mellin f hk hs1, hB, rsSeries_eq_LSeriesNorm f hk hs,
    rankinNorm_sym2_transfer f hk hs]
  have h1 := Gamma_mul_pi_cpow s
  have h2 := Gamma_mul_fourpi_cpow (s + (k : ℂ) - 1)
  rw [show s + (k : ℂ) - 1 + 1 = s + (k : ℂ) from by ring] at h2
  have h4 : (2 : ℂ) ^ s * (2 : ℂ) ^ (-(s + (k : ℂ) - 1)) = 2 * (2 : ℂ) ^ (-(k : ℂ)) := by
    rw [← cpow_add _ _ two_ne_zero,
      show s + -(s + (k : ℂ) - 1) = 1 + -(k : ℂ) from by ring,
      cpow_add _ _ two_ne_zero, cpow_one]
  have hzz : (riemannZeta s)⁻¹ * riemannZeta s = 1 := inv_mul_cancel₀ hζ
  set Lval : ℂ := LSeries (⇑((μ : ArithmeticFunction ℂ) * rankinSquareNorm f)) s with hLval
  set yζ : ℂ := riemannZeta (2 * s) with hyζ
  calc (riemannZeta s)⁻¹ *
        (Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) * (2 * yζ) *
          (Complex.Gamma (s + (k : ℂ) - 1) *
            (((4 * π : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * (riemannZeta s * Lval))))
      = ((riemannZeta s)⁻¹ * riemannZeta s) *
          (Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) * (2 * yζ) *
            (Complex.Gamma (s + (k : ℂ) - 1) *
              ((4 * π : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * Lval)) := by ring
    _ = Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) * (2 * yζ) *
          (Complex.Gamma (s + (k : ℂ) - 1) *
            ((4 * π : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)) * Lval) := by rw [hzz, one_mul]
    _ = (2 : ℂ) ^ (-(k : ℂ)) * yζ *
          (Gammaℝ s * Gammaℝ (s + 1) * Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))) *
          Lval := by
        linear_combination
          (2 * yζ * Lval * (Complex.Gamma (s + (k : ℂ) - 1) *
            ((4 * π : ℝ) : ℂ) ^ (-(s + (k : ℂ) - 1)))) * h1 +
          (yζ * Lval * (2 : ℂ) ^ s * (Gammaℝ s * Gammaℝ (s + 1))) * h2 +
          (yζ * Lval * (Gammaℝ s * Gammaℝ (s + 1)) *
            (Gammaℝ (s + (k : ℂ) - 1) * Gammaℝ (s + (k : ℂ))) / 2) * h4

end CriticalLinePhasor.Sym2Registration

#print axioms CriticalLinePhasor.Sym2Registration.peeledProfile
#print axioms CriticalLinePhasor.Sym2Registration.peeledProfile_hasMellin
#print axioms CriticalLinePhasor.Sym2Registration.peeledProfile_mellin
#print axioms CriticalLinePhasor.Sym2Registration.peeledFE
#print axioms CriticalLinePhasor.Sym2Registration.peeledFE_gammaChart
#print axioms CriticalLinePhasor.Sym2Registration.peeledFE_gammaChart_strip
#print axioms CriticalLinePhasor.Sym2Registration.rankinSquareNorm_LSeriesSummable
#print axioms CriticalLinePhasor.Sym2Registration.rankinNorm_sym2_transfer
#print axioms CriticalLinePhasor.Sym2Registration.LSeries_rankinSquare_shift
#print axioms CriticalLinePhasor.Sym2Registration.rsSeries_eq_LSeriesNorm
#print axioms CriticalLinePhasor.Sym2Registration.averagedTheta_sub_mass
#print axioms CriticalLinePhasor.Sym2Registration.rsAveraged_lambda_eq_pairing
#print axioms CriticalLinePhasor.Sym2Registration.Gamma_mul_pi_cpow
#print axioms CriticalLinePhasor.Sym2Registration.Gamma_mul_fourpi_cpow
#print axioms CriticalLinePhasor.Sym2Registration.peeled_readout_gammaChart
