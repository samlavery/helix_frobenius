import RequestProject.PhragmenBV

/-!
# The identification: from the theta reflection to the modular transformation laws

The converse chain now reads: package + one boundedness constant ⟹ theta reflection
(`weil_converse_of_BV_gammaC_reflection`).  This file carries the reflection from the
positive imaginary axis to the upper half-plane — the classical *identification* step
of the Hecke converse theorem:

* `qSeries` — the q-expansion `Σ a(n)·e^{2πi(n+1)τ}` of a coefficient surface;
* `qSeries_analyticOnNhd` — holomorphy on the upper half-plane (Weierstrass M-test
  on every horocycle strip, `differentiableOn_tsum_of_summable_norm`);
* `qSeries_T` — **the T-law**: exact 1-periodicity, from the q-expansion alone;
* `theta_eq_qSeries_axis` — the bridge: the compiled `Γℂ`-clock theta readout at
  height `y` is `2·qSeries` at `τ = iy`;
* `qSeries_S_of_reflection` — **the S-law**: the axis reflection extends to
  `qSeries a τ = ε·(-(I·τ))⁻¹·qSeries a (-1/τ)` on all of `ℍ`, by the identity
  theorem (both sides analytic, equal on the axis, `ℍ` connected);
* `hecke_identification` — **the Hecke converse, carrier register**: an entire
  package with the functional equation and one boundedness constant yields both
  generator transformation laws of its q-expansion.

Register.  `S` and `T` generate `SL(2,ℤ)` — compiled in Mathlib
(`SpecialLinearGroup.SL2Z_generators`), so the two laws proven here are the full
generator set of level-one modularity; packaging the resulting multiplier system as
a typed `SlashInvariantForm` (the weight/multiplier bookkeeping along
`closure_induction`) is the named extension.  Level `N` (Weil proper: finitely many
twisted functional equations ⟹ `Γ₀(N)`-automorphy via Weil's lemma) remains the
cited classical layer, consumed at the identification interface.  No `axiom`, no
`sorry`.
-/

open Real Complex Set Filter Topology MeasureTheory Asymptotics

namespace CriticalLinePhasor.WeilIdentification

open CriticalLinePhasor.CarrierTheta CriticalLinePhasor.RamifiedMechanism
open CriticalLinePhasor.WeilConverse CriticalLinePhasor.PhragmenBV
open CriticalLinePhasor.GlobalHelix

/-! ## The q-expansion and its holomorphy -/

/-- The q-expansion of a coefficient sequence: amplitude at index `n` sits at
frequency `n+1` (the house indexing law). -/
noncomputable def qSeries (a : ℕ → ℂ) (τ : ℂ) : ℂ :=
  ∑' n : ℕ, a n * Complex.exp (2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) * τ)

/-- The upper half-plane as a subset of `ℂ`. -/
def upperHalf : Set ℂ := {τ : ℂ | 0 < τ.im}

theorem isOpen_upperHalf : IsOpen upperHalf :=
  isOpen_lt continuous_const Complex.continuous_im

theorem I_mem_upperHalf : I ∈ upperHalf := by
  simp [upperHalf]

/-- Norm of a q-term: pure exponential decay in the height. -/
theorem qSeries_term_norm (a : ℕ → ℂ) (n : ℕ) (τ : ℂ) :
    ‖a n * Complex.exp (2 * Real.pi * I * ((n + 1 : ℕ) : ℂ) * τ)‖
      = ‖a n‖ * Real.exp (-(2 * Real.pi * (n + 1)) * τ.im) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  have : (2 * (Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * τ).re
      = -(2 * Real.pi * (n + 1)) * τ.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]

/-- The M-test majorant on a horocycle strip is summable. -/
theorem qSeries_majorant_summable (A : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ (A : ℕ) * Real.exp (-(2 * Real.pi * (n + 1)) * δ)) := by
  have hr : |Real.exp (-(2 * Real.pi * δ))| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    have := Real.pi_pos
    nlinarith
  have hbase := summable_pow_mul_geometric_of_norm_lt_one (k := A)
    (r := Real.exp (-(2 * Real.pi * δ))) (by simpa using hr)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  refine hshift.congr fun n => ?_
  have hexp : Real.exp (-(2 * Real.pi * δ)) ^ (n + 1)
      = Real.exp (-(2 * Real.pi * (n + 1)) * δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  push_cast
  rw [hexp]

/-- Holomorphy of the q-expansion on every horocycle strip. -/
theorem qSeries_differentiableOn (P : CoefficientSurface) (δ : ℝ) (hδ : 0 < δ) :
    DifferentiableOn ℂ (qSeries P.a) {τ : ℂ | δ < τ.im} := by
  refine differentiableOn_tsum_of_summable_norm
    (qSeries_majorant_summable P.A δ hδ) (fun n => ?_) ?_ (fun n τ hτ => ?_)
  · exact ((differentiable_const _).mul
      (((differentiable_const _).mul differentiable_id).cexp)).differentiableOn
  · exact isOpen_lt continuous_const Complex.continuous_im
  · rw [qSeries_term_norm]
    simp only [Set.mem_setOf_eq] at hτ
    have h1 : ‖P.a n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (P.A : ℕ) := P.a_bound n
    have h2 : Real.exp (-(2 * Real.pi * (n + 1)) * τ.im)
        ≤ Real.exp (-(2 * Real.pi * (n + 1)) * δ) := by
      apply Real.exp_le_exp.mpr
      have hc : (0 : ℝ) ≤ 2 * Real.pi * (n + 1) := by positivity
      have h3 : 0 ≤ (2 * Real.pi * (n + 1)) * (τ.im - δ) :=
        mul_nonneg hc (by linarith)
      nlinarith [h3]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

theorem qSeries_analyticOnNhd (P : CoefficientSurface) :
    AnalyticOnNhd ℂ (qSeries P.a) upperHalf := by
  have hdiff : DifferentiableOn ℂ (qSeries P.a) upperHalf := by
    intro τ hτ
    have hτ' : (0 : ℝ) < τ.im := hτ
    have h := qSeries_differentiableOn P (τ.im / 2) (by linarith)
    exact (h.differentiableAt ((isOpen_lt continuous_const
      Complex.continuous_im).mem_nhds (by simp; linarith))).differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_upperHalf

/-! ## The T-law -/

/-- **The T-law**: exact 1-periodicity of the q-expansion. -/
theorem qSeries_T (a : ℕ → ℂ) (τ : ℂ) : qSeries a (τ + 1) = qSeries a τ := by
  unfold qSeries
  apply tsum_congr
  intro n
  congr 1
  rw [mul_add, Complex.exp_add, mul_one]
  have h1 : 2 * (Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ)
      = ((n + 1 : ℕ) : ℂ) * (2 * Real.pi * I) := by ring
  rw [h1, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-! ## The axis bridge -/

/-- The compiled `Γℂ`-clock theta readout at height `y` is `2·qSeries` at `τ = iy`. -/
theorem theta_eq_qSeries_axis (a : ℕ → ℂ) (y : ℝ) :
    CriticalLinePhasor.CarrierTheta.theta a (gammaClock 0) y
      = 2 * qSeries a (I * (y : ℂ)) := by
  unfold CriticalLinePhasor.CarrierTheta.theta qSeries gammaClock
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hpow : (((((n + 1 : ℕ) : ℝ) * y : ℝ)) : ℂ) ^ (0 : ℂ) = 1 := Complex.cpow_zero _
  have harg : -(2 * (Real.pi : ℂ)) * (((((n + 1 : ℕ) : ℝ) * y : ℝ)) : ℂ)
      = 2 * (Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * (I * (y : ℂ)) := by
    have hI := Complex.I_mul_I
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (y : ℂ))) * hI
  rw [hpow, harg]
  ring

/-! ## The S-law by the identity theorem -/

/-- `τ ↦ -1/τ` preserves the upper half-plane. -/
theorem neg_inv_mem_upperHalf {τ : ℂ} (hτ : τ ∈ upperHalf) :
    -1 / τ ∈ upperHalf := by
  have hτ' : (0 : ℝ) < τ.im := hτ
  have hne : τ ≠ 0 := by
    intro h
    rw [h] at hτ'
    simp at hτ'
  show (0 : ℝ) < (-1 / τ).im
  rw [div_eq_mul_inv, neg_one_mul, Complex.neg_im, Complex.inv_im]
  have hnormSq : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hne
  rw [neg_div, neg_neg]
  exact div_pos hτ' hnormSq

/-- **The S-law**: the axis reflection extends to the upper half-plane. -/
theorem qSeries_S_of_reflection (P : CoefficientSurface) (ε : ℂ)
    (hrefl : ∀ y : ℝ, 0 < y →
      qSeries P.a (I * (y : ℂ)) = ε * (((y : ℝ) : ℂ)⁻¹ * qSeries P.a (I * ((1 / y : ℝ) : ℂ)))) :
    ∀ τ ∈ upperHalf,
      qSeries P.a τ = ε * ((-(I * τ))⁻¹ * qSeries P.a (-1 / τ)) := by
  set L : ℂ → ℂ := fun τ => qSeries P.a τ with hLdef
  set R : ℂ → ℂ := fun τ => ε * ((-(I * τ))⁻¹ * qSeries P.a (-1 / τ)) with hRdef
  have hL : AnalyticOnNhd ℂ L upperHalf := qSeries_analyticOnNhd P
  have hR : AnalyticOnNhd ℂ R upperHalf := by
    have hcomp : AnalyticOnNhd ℂ (fun τ : ℂ => qSeries P.a (-1 / τ)) upperHalf := by
      have hmap : Set.MapsTo (fun τ : ℂ => -1 / τ) upperHalf upperHalf :=
        fun τ hτ => neg_inv_mem_upperHalf hτ
      have hinv : AnalyticOnNhd ℂ (fun τ : ℂ => -1 / τ) upperHalf := by
        have hdiff : DifferentiableOn ℂ (fun τ : ℂ => -1 / τ) upperHalf := by
          intro τ hτ
          have hne : τ ≠ 0 := by
            intro h
            have : (0 : ℝ) < τ.im := hτ
            rw [h] at this
            simp at this
          exact ((differentiable_const (-1 : ℂ)).differentiableAt.div
            differentiableAt_id hne).differentiableWithinAt
        exact hdiff.analyticOnNhd isOpen_upperHalf
      exact (qSeries_analyticOnNhd P).comp hinv hmap
    have hfactor : AnalyticOnNhd ℂ (fun τ : ℂ => (-(I * τ))⁻¹) upperHalf := by
      have hdiff : DifferentiableOn ℂ (fun τ : ℂ => (-(I * τ))⁻¹) upperHalf := by
        intro τ hτ
        have hne : -(I * τ) ≠ 0 := by
          intro h
          have h2 : I * τ = 0 := by
            have := neg_eq_zero.mp h
            exact this
          rcases mul_eq_zero.mp h2 with h3 | h3
          · exact I_ne_zero h3
          · have : (0 : ℝ) < τ.im := hτ
            rw [h3] at this
            simp at this
        exact (((differentiable_const I).differentiableAt.mul
          differentiableAt_id).neg.inv hne).differentiableWithinAt
      exact hdiff.analyticOnNhd isOpen_upperHalf
    have : AnalyticOnNhd ℂ
        (fun τ : ℂ => ε * ((-(I * τ))⁻¹ * qSeries P.a (-1 / τ))) upperHalf :=
      analyticOnNhd_const.mul (hfactor.mul hcomp)
    exact this
  have haxis : ∀ y : ℝ, 0 < y → L (I * (y : ℂ)) = R (I * (y : ℂ)) := by
    intro y hy
    rw [hLdef, hRdef]
    dsimp only
    have h1 : -(I * (I * (y : ℂ))) = (y : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]
      ring
    have h2 : -1 / (I * (y : ℂ)) = I * ((1 / y : ℝ) : ℂ) := by
      have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      rw [show ((1 / y : ℝ) : ℂ) = ((y : ℝ) : ℂ)⁻¹ by push_cast; rw [one_div]]
      rw [div_eq_mul_inv, mul_inv, Complex.inv_I]
      ring
    rw [h1, h2]
    exact hrefl y hy
  -- the sequence approaching I within the axis
  have hseq : Tendsto (fun n : ℕ => I * (((1 + (n + 1 : ℝ)⁻¹ : ℝ)) : ℂ)) atTop
      (𝓝[≠] I) := by
    have h1 : Tendsto (fun n : ℕ => (1 + (n + 1 : ℝ)⁻¹ : ℝ)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => 1 + (1 / (n + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add h0
      simpa [one_div] using h2
    have h2 : Tendsto (fun n : ℕ => I * (((1 + (n + 1 : ℝ)⁻¹ : ℝ)) : ℂ)) atTop
        (𝓝 (I * ((1 : ℝ) : ℂ))) :=
      Tendsto.const_mul I ((Complex.continuous_ofReal.tendsto _).comp h1)
    rw [show (I * ((1 : ℝ) : ℂ)) = I by simp] at h2
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h2 ?_
    refine Eventually.of_forall fun n => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have h3 : (((1 + (n + 1 : ℝ)⁻¹ : ℝ)) : ℂ) = 1 :=
      mul_left_cancel₀ I_ne_zero (h.trans (mul_one I).symm)
    have h4 : (1 + (n + 1 : ℝ)⁻¹ : ℝ) = 1 := by exact_mod_cast h3
    have h5 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] I, L z = R z := by
    refine hseq.frequently (Frequently.of_forall fun n => ?_)
    exact haxis _ (by positivity)
  have heq := hL.eqOn_of_preconnected_of_frequently_eq hR
    ((convex_halfSpace_im_gt 0).isPreconnected) I_mem_upperHalf hfreq
  intro τ hτ
  exact heq hτ

/-! ## The Hecke converse, carrier register -/

/-- **THE HECKE IDENTIFICATION** — an entire package at the `Γℂ` chart with the
functional equation and one boundedness constant yields both generator
transformation laws of its q-expansion: exact 1-periodicity, and the S-law on the
full upper half-plane.  With `SpecialLinearGroup.SL2Z_generators` (compiled in
Mathlib), these are the complete generator set of level-one modularity. -/
theorem hecke_identification (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (ε : ℂ)
    (pkg : KNicePackage (coefficientArithmetic P.a)
      (gammaCKernel 0 (by simp)).G
      (max (gammaCKernel 0 (by simp)).B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max (gammaCKernel 0 (by simp)).B0 ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    (∀ τ : ℂ, qSeries P.a (τ + 1) = qSeries P.a τ) ∧
    (∀ τ ∈ upperHalf,
      qSeries P.a τ = ε * ((-(I * τ))⁻¹ * qSeries P.a (-1 / τ))) := by
  refine ⟨fun τ => qSeries_T P.a τ, ?_⟩
  have hrefl := weil_converse_of_BV_gammaC_reflection P hdual 0 (by simp) ε pkg σ hσ
    C hBV
  refine qSeries_S_of_reflection P ε fun y hy => ?_
  have h := hrefl y hy
  have hK : (gammaCKernel 0 (by simp : (0:ℝ) ≤ (0:ℂ).re)).K = gammaClock 0 := rfl
  rw [hK] at h
  have hthA := theta_eq_qSeries_axis P.a y
  have hthD := theta_eq_qSeries_axis P.adual (1 / y)
  have hdualq : qSeries P.adual (I * ((1 / y : ℝ) : ℂ)) = qSeries P.a (I * ((1 / y : ℝ) : ℂ)) := by
    unfold qSeries
    exact tsum_congr fun n => by rw [hdual n]
  rw [hthA, hthD, hdualq] at h
  have h3 : (2 : ℂ) * qSeries P.a (I * (y : ℂ))
      = 2 * (ε * ((((y : ℝ)) : ℂ)⁻¹ * qSeries P.a (I * ((1 / y : ℝ) : ℂ)))) := by
    rw [h]
    ring
  exact mul_left_cancel₀ two_ne_zero h3

end CriticalLinePhasor.WeilIdentification

#print axioms CriticalLinePhasor.WeilIdentification.qSeries_analyticOnNhd
#print axioms CriticalLinePhasor.WeilIdentification.qSeries_T
#print axioms CriticalLinePhasor.WeilIdentification.theta_eq_qSeries_axis
#print axioms CriticalLinePhasor.WeilIdentification.qSeries_S_of_reflection
#print axioms CriticalLinePhasor.WeilIdentification.hecke_identification
