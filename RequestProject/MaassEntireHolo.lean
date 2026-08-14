import RequestProject.MaassGGlobalBound
import RequestProject.RSEntireHolo

/-!
# Holomorphy of the Maass entire-part Petersson integral

Item (3) of the Eisenstein continuation, for a Maass form.

`RSEntireHolo.rs_entirePart_differentiable` discharges, unconditionally, the holomorphy of
`s ↦ ∫_𝒟 P·Λ₀_z(s) dμ` — the input `RSPoleStructure` named as "not in Mathlib".  Its proof touches
the cusp form in exactly four places, all of them the same two facts: the density's exponential
decay on `𝒟` and its nonnegativity.  Both hold for a Maass form
(`maassP_exp_decay_on_fd`, `maassP_nonneg`), so the argument transfers verbatim.

Everything analytic in it — the `Λ₀` bound from `TruncatedMellin`, `cz_ge_on_fd`, the
locally-uniform dominated-holomorphy engine — never mentions the form.  This is the eighth
form-independent transfer in this campaign.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.

**Provenance.**  This proof is `rs_entirePart_differentiable` with `P k f` replaced by `maassP M`
and its two inputs replaced by the Maass ones; nothing else is changed.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter Asymptotics
open scoped Real Topology MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.HeckeSupBound
open CriticalLinePhasor.ThreeDConverse

/-- The Maass Petersson density is continuous. -/
lemma continuous_maassP (M : GenuineMaassCuspForm3D) : Continuous (maassP M) :=
  (continuous_maassWave M).norm.pow 2

theorem maass_entirePart_differentiable (M : GenuineMaassCuspForm3D) :
    Differentiable ℂ (fun s => ∫ z in ModularGroup.fd,
      ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s ∂volume) := by
  obtain ⟨C, hC0, hC⟩ := maassP_exp_decay_on_fd M
  intro s₀
  obtain ⟨Nnat, hN1, hNa, hNb⟩ :
      ∃ n : ℕ, 1 ≤ n ∧ s₀.re + 1 ≤ (n : ℝ) ∧ 2 - s₀.re ≤ (n : ℝ) := by
    refine ⟨⌈s₀.re + 1⌉₊ + ⌈2 - s₀.re⌉₊ + 1, by omega, ?_, ?_⟩
    · push_cast
      linarith [Nat.le_ceil (s₀.re + 1), Nat.cast_nonneg (α := ℝ) ⌈2 - s₀.re⌉₊]
    · push_cast
      linarith [Nat.le_ceil (2 - s₀.re), Nat.cast_nonneg (α := ℝ) ⌈s₀.re + 1⌉₊]
  set N : ℝ := (Nnat : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hN1
  -- the dominating bound
  set bound : ℍ → ℝ := fun z =>
    (C * Real.exp (-(2 * π) * z.im)) * (lambdaC N * ((1 + z.im ^ 2) * z.im ^ N)) with hbound
  set F : ℂ → ℍ → ℂ := fun s z => ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s with hF
  -- (a) measurability of the integrand
  have hFmeas : ∀ s ∈ Metric.ball s₀ 1,
      AEStronglyMeasurable (F s) (volume.restrict ModularGroup.fd) := by
    intro s _
    refine AEStronglyMeasurable.mul ?_ ((aestronglyMeasurable_Lambda0 s).restrict)
    exact (Complex.continuous_ofReal.comp (continuous_maassP M)).aestronglyMeasurable
  -- (b) pointwise holomorphy (the completion is entire)
  have hFholo : ∀ᵐ z ∂(volume.restrict ModularGroup.fd),
      DifferentiableOn ℂ (fun s => F s z) (Metric.ball s₀ 1) := by
    refine ae_of_all _ (fun z => ?_)
    exact (((generalFEPair z).differentiable_Λ₀).const_mul ((maassP M z : ℝ) : ℂ)).differentiableOn
  -- (c) the uniform domination
  have hFbound : ∀ᵐ z ∂(volume.restrict ModularGroup.fd),
      ∀ s ∈ Metric.ball s₀ 1, ‖F s z‖ ≤ bound z := by
    refine (ae_restrict_mem measurableSet_fd).mono (fun z hz => ?_)
    intro s hs
    have hdist : |s.re - s₀.re| < 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h1
      have h2 : ‖s - s₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hs
      linarith
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hdist
    have hs1 : s.re ≤ N := by linarith
    have hs2 : (1 - s).re ≤ N := by rw [Complex.sub_re, Complex.one_re]; linarith
    rw [hF]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (maassP_nonneg M z)]
    exact mul_le_mul (hC z hz) (lambda0_bound_on_fd hz hNpos hs1 hs2) (norm_nonneg _)
      (mul_nonneg hC0 (Real.exp_pos _).le)
  -- (d) integrability of the dominant (constant on 𝒟)
  have hbound_int : Integrable bound (volume.restrict ModularGroup.fd) := by
    have him : Continuous (fun z : ℍ => z.im) := UpperHalfPlane.continuous_im
    have hcont : Continuous bound := by
      rw [hbound]
      have hrpow : Continuous (fun z : ℍ => z.im ^ N) :=
        him.rpow_const (fun z => Or.inl z.im_ne_zero)
      have hexp : Continuous (fun z : ℍ => Real.exp (-(2 * π) * z.im)) :=
        Real.continuous_exp.comp (continuous_const.mul him)
      exact (continuous_const.mul hexp).mul
        (continuous_const.mul ((continuous_const.add (him.pow 2)).mul hrpow))
    refine integrableOn_fd_of_bounded hcont
      (C := C * lambdaC N * (3 * (Nnat.factorial : ℝ))) (fun z _ => ?_)
    have hy : 0 < z.im := z.im_pos
    have hy0 : 0 ≤ z.im := hy.le
    have hbnn : 0 ≤ bound z :=
      mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le)
        (mul_nonneg (lambdaC_nonneg hNpos)
          (mul_nonneg (by positivity) (Real.rpow_nonneg hy0 N)))
    rw [Real.norm_of_nonneg hbnn]
    show (C * Real.exp (-(2 * π) * z.im)) * (lambdaC N * ((1 + z.im ^ 2) * z.im ^ N))
        ≤ C * lambdaC N * (3 * (Nnat.factorial : ℝ))
    have hyN : z.im ^ N = z.im ^ Nnat := by rw [hN, Real.rpow_natCast]
    rw [hyN]
    set y := z.im with hy_def
    have e1 : (1 + y ^ 2) ≤ 3 * Real.exp y := by
      have h2 := pow_le_factorial_mul_exp hy0 2
      have h1 : (1 : ℝ) ≤ Real.exp y := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hy0
      have hfac2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [hfac2] at h2
      nlinarith [Real.exp_pos y]
    have e2 : y ^ Nnat ≤ (Nnat.factorial : ℝ) * Real.exp y := pow_le_factorial_mul_exp hy0 Nnat
    have hexp1 : Real.exp y * Real.exp y * Real.exp (-(2 * π) * y) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, hy])
    have step : (1 + y ^ 2) * y ^ Nnat ≤ (3 * Real.exp y) * ((Nnat.factorial : ℝ) * Real.exp y) :=
      mul_le_mul e1 e2 (by positivity) (by positivity)
    calc (C * Real.exp (-(2 * π) * y)) * (lambdaC N * ((1 + y ^ 2) * y ^ Nnat))
        = C * lambdaC N * ((1 + y ^ 2) * y ^ Nnat * Real.exp (-(2 * π) * y)) := by ring
      _ ≤ C * lambdaC N *
            ((3 * Real.exp y) * ((Nnat.factorial : ℝ) * Real.exp y) * Real.exp (-(2 * π) * y)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (lambdaC_nonneg hNpos))
          exact mul_le_mul_of_nonneg_right step (Real.exp_pos _).le
      _ = C * lambdaC N *
            (3 * (Nnat.factorial : ℝ) * (Real.exp y * Real.exp y * Real.exp (-(2 * π) * y))) := by
          ring
      _ ≤ C * lambdaC N * (3 * (Nnat.factorial : ℝ) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (lambdaC_nonneg hNpos))
          exact mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = C * lambdaC N * (3 * (Nnat.factorial : ℝ)) := by ring
  -- assemble the general holomorphy-under-integral lemma
  exact differentiableAt_integral_of_dominated_holo F bound one_pos hFmeas hFholo hFbound hbound_int

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maass_entirePart_differentiable
