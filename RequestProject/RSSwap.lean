import RequestProject.LambdaIdentification

/-!
# The sum–integral swap: the Rankin–Selberg pairing absorbs the coset sum

The last bookkeeping gate before the continuation.  The coset sum passes through the
Petersson integral (`rs_swap`): the summand is *exactly* the RS integrand at the coset
translate (`rsIntegrand_smul` + `im_smul_cpow`), so the domination required by
`integral_tsum` is the hypothesis-free lintegral unfolding (`lintegral_unfolding` — the
compiled two-domain transfer replayed for `ℝ≥0∞`, where no integrability is needed) evaluated
against the compiled strip integrability.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise ENNReal

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound CriticalLinePhasor.EpsteinTheta

variable {k : ℤ}

/-- **The lintegral unfolding** — hypothesis-free: for any measurable translation-periodic
`ℝ≥0∞`-valued function, the strip lintegral is the coset sum of domain lintegrals. -/
lemma lintegral_unfolding (F : ℍ → ℝ≥0∞) (hF : ∀ (n : ℤ) (z : ℍ),
    F (ModularGroup.T ^ n • z) = F z) :
    ∫⁻ z in strip, F z ∂(volume : Measure ℍ) =
      ∑' q : CosetQ, ∫⁻ z in ModularGroup.fd, F (rep q • z)
        ∂(volume : Measure ℍ) := by
  have hinv : ∀ (g : gammaInfty) (z : ℍ), F (g • z) = F z := by
    rintro ⟨δ, hδ⟩ z
    obtain ⟨n, rfl⟩ := hδ
    exact hF n z
  calc ∫⁻ z in strip, F z ∂volume
      = ∫⁻ z in fdUnion, F z ∂volume :=
        isFundamentalDomain_strip.setLIntegral_eq isFundamentalDomain_fdUnion F hinv
    _ = ∑' q : CosetQ, ∫⁻ z in rep q • ModularGroup.fd, F z ∂volume := by
        rw [fdUnion, lintegral_iUnion₀
          (fun q => (measurableSet_smul_fd (rep q)).nullMeasurableSet) tiles_aedisjoint]
    _ = ∑' q : CosetQ, ∫⁻ z in ModularGroup.fd, F (rep q • z) ∂volume := by
        refine tsum_congr fun q => ?_
        have hmp : MeasurePreserving (fun z : ℍ => rep q • z) volume volume := by
          show MeasurePreserving (fun z : ℍ =>
            (Matrix.SpecialLinearGroup.mapGL ℝ (rep q)) • z) volume volume
          exact measurePreserving_smul _ _
        have hme : MeasurableEmbedding (fun z : ℍ => rep q • z) := by
          show MeasurableEmbedding (fun z : ℍ =>
            (Matrix.SpecialLinearGroup.mapGL ℝ (rep q)) • z)
          exact measurableEmbedding_const_smul _
        have himg : rep q • ModularGroup.fd =
            (fun z : ℍ => rep q • z) '' ModularGroup.fd := rfl
        rw [himg, ← hmp.setLIntegral_comp_emb hme]

/-- The gram-power kernel is continuous in the point. -/
lemma continuous_gram_cpow {p : ℤ × ℤ} (hp : p ≠ 0) (s : ℂ) :
    Continuous fun z : ℍ => ((gram z p : ℝ) : ℂ) ^ (-s) := by
  have hgc : Continuous fun z : ℍ => gram z p := by
    rw [show (fun z : ℍ => gram z p) = fun z : ℍ =>
      (((p.1 : ℝ) * z.re + (p.2 : ℝ)) ^ 2 + (p.1 : ℝ) ^ 2 * z.im ^ 2) / z.im from rfl]
    apply Continuous.div
    · fun_prop
    · exact UpperHalfPlane.continuous_im
    · exact fun z => z.im_ne_zero
  apply Continuous.cpow
  · exact Complex.continuous_ofReal.comp hgc
  · exact continuous_const
  · exact fun z => Complex.ofReal_mem_slitPlane.mpr (gram_pos z hp)

/-- Rows of representatives are nonzero as pairs. -/
lemma rep_row_ne_zero' (q : CosetQ) :
    (((rep q).1 1 0, (rep q).1 1 1) : ℤ × ℤ) ≠ 0 := by
  intro h
  apply rep_row_ne_zero q
  rw [Prod.ext_iff] at h
  exact ⟨h.1, h.2⟩

/-- **The sum–integral swap** for the Rankin–Selberg pairing, dominated by the compiled
strip integrability through the lintegral unfolding. -/
theorem rs_swap (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) *
        (∑' q : CosetQ,
          ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)) ∂volume =
      ∑' q : CosetQ, ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) *
        ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) ∂volume := by
  have hkey : ∀ (q : CosetQ) (z : ℍ), ((P k f z : ℝ) : ℂ) *
      ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) =
      rsIntegrand f s (rep q • z) := by
    intro q z
    rw [rsIntegrand_smul, im_smul_cpow]
  have hmeas : ∀ q : CosetQ, AEStronglyMeasurable (fun z : ℍ => ((P k f z : ℝ) : ℂ) *
      ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s))
      (volume.restrict ModularGroup.fd) := fun q =>
    ((Complex.continuous_ofReal.comp (continuous_P f)).mul
      (continuous_gram_cpow (rep_row_ne_zero' q) s)).aestronglyMeasurable.restrict
  have hdom : ∑' q : CosetQ, ∫⁻ z in ModularGroup.fd,
      ‖((P k f z : ℝ) : ℂ) *
        ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)‖ₑ ∂volume ≠ ⊤ := by
    have hcongr : ∀ q : CosetQ, (∫⁻ z in ModularGroup.fd,
        ‖((P k f z : ℝ) : ℂ) *
          ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)‖ₑ ∂volume) =
        ∫⁻ z in ModularGroup.fd, ‖rsIntegrand f s (rep q • z)‖ₑ ∂volume := by
      intro q
      exact lintegral_congr fun z => by rw [hkey]
    have hper : ∀ (n : ℤ) (z : ℍ),
        ‖rsIntegrand f s (ModularGroup.T ^ n • z)‖ₑ = ‖rsIntegrand f s z‖ₑ := by
      intro n z
      rw [rsIntegrand_periodic]
    have hunfold := lintegral_unfolding (fun z => ‖rsIntegrand f s z‖ₑ) hper
    have hfin := (rsIntegrand_integrableOn_strip f hk hs).2
    rw [tsum_congr hcongr, ← hunfold]
    exact hfin.ne
  have hpull : ∀ z : ℍ, ((P k f z : ℝ) : ℂ) *
      (∑' q : CosetQ, ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s)) =
      ∑' q : CosetQ, ((P k f z : ℝ) : ℂ) *
        ((gram z ((rep q).1 1 0, (rep q).1 1 1) : ℝ) : ℂ) ^ (-s) := fun z =>
    (tsum_mul_left).symm
  rw [setIntegral_congr_fun measurableSet_fd fun z _ => hpull z,
    integral_tsum hmeas hdom]

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.lintegral_unfolding
#print axioms CriticalLinePhasor.Unfolding.rs_swap
