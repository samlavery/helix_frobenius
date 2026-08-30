import RequestProject.SeatingFloor
import RequestProject.DVPWeightedCount

/-!
# Transversality: a simple on-line zero is a flip

* `xi_deriv_line_re` — the readout's derivative is purely imaginary on the
  line (differentiating the compiled reality `Xi_line_im`);
* `deriv_xi_ne_zero_of_simple` — multiplicity one forces `deriv ξ ≠ 0` there
  (the compiled ξ/ζ order bridge `DVP.xi_order_eq_zeta_order` + Mathlib's
  order-derivative kit);
* `simple_zero_flips` — hence **every simple on-line zero produces a genuine
  sign flip of `XiLine` in every sufficiently small window**.

With `seating_simple_floor`, half the census is flip-visible: the first
compiled quantitative instance of the flip-visibility hypothesis.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The line path has derivative `I`. -/
theorem linePt_hasDerivAt (γ : ℝ) :
    HasDerivAt (fun t : ℝ => linePt t) I γ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 γ :=
    Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) γ := h1.mul_const I
  have h3 := h2.const_add (1/2 : ℂ)
  simpa [linePt] using h3

/-- The readout along the line, with its chain-rule slope. -/
theorem XiF_hasDerivAt (γ : ℝ) :
    HasDerivAt (fun t : ℝ => ZD.riemannXi (linePt t))
      (I * deriv ZD.riemannXi (linePt γ)) γ := by
  have hin : HasDerivAt (fun w : ℂ => 1/2 + w * I) I (γ:ℂ) := by
    simpa using ((hasDerivAt_id (γ:ℂ)).mul_const I).const_add (1/2:ℂ)
  have hξ : HasDerivAt ZD.riemannXi (deriv ZD.riemannXi (linePt γ))
      ((1/2:ℂ) + (γ:ℂ) * I) :=
    (ZD.riemannXi_differentiable _).hasDerivAt
  have hG := HasDerivAt.comp (γ:ℂ) hξ hin
  have := hG.comp_ofReal
  simpa [linePt, Function.comp, mul_comm] using this

/-- **The line derivative is purely imaginary**: `Re ξ′(½+iγ) = 0`. -/
theorem xi_deriv_line_re (γ : ℝ) :
    (deriv ZD.riemannXi (linePt γ)).re = 0 := by
  have hXiF := XiF_hasDerivAt γ
  have him : HasDerivAt (fun t : ℝ => (ZD.riemannXi (linePt t)).im)
      ((I * deriv ZD.riemannXi (linePt γ)).im) γ :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt γ hXiF
  have hconst : (fun t : ℝ => (ZD.riemannXi (linePt t)).im) = fun _ => (0:ℝ) :=
    funext Xi_line_im
  rw [hconst] at him
  have hz := him.unique (hasDerivAt_const γ 0)
  simpa [Complex.mul_im] using hz

/-- The real readout's slope. -/
theorem XiLine_hasDerivAt (γ : ℝ) :
    HasDerivAt XiLine ((I * deriv ZD.riemannXi (linePt γ)).re) γ :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt γ (XiF_hasDerivAt γ)

/-- **Multiplicity one forces a nonzero derivative** of the completed readout. -/
theorem deriv_xi_ne_zero_of_simple {γ : ℝ} (hγ : γ ≠ 0)
    (hm : Zeta23.zeroMult (linePt γ) = 1) :
    deriv ZD.riemannXi (linePt γ) ≠ 0 := by
  have him : (linePt γ).im ≠ 0 := by
    rw [linePt_im]
    exact hγ
  -- ζ-order = 1 from toNat = 1
  have hζ : analyticOrderAt riemannZeta (linePt γ) = 1 := by
    unfold Zeta23.zeroMult at hm
    have hne : analyticOrderAt riemannZeta (linePt γ) ≠ ⊤ := by
      intro htop
      rw [htop] at hm
      simp [ENat.toNat_top] at hm
    have hcoe := ENat.coe_toNat hne
    rw [hm] at hcoe
    simpa using hcoe.symm
  -- transfer to ξ
  have hξord : analyticOrderAt ZD.riemannXi (linePt γ) = 1 := by
    rw [CriticalLinePhasor.DVP.xi_order_eq_zeta_order him, hζ]
  have hDiff : Differentiable ℂ ZD.riemannXi := fun z => ZD.riemannXi_differentiable z
  have hA : AnalyticAt ℂ ZD.riemannXi (linePt γ) :=
    hDiff.differentiableOn.analyticAt
      (IsOpen.mem_nhds isOpen_univ (Set.mem_univ _))
  have hd0 : analyticOrderAt (deriv ZD.riemannXi) (linePt γ) = 0 := by
    have := analyticOrderAt_deriv_of_pos hA (n := 0)
      (by rw [hξord]; simp)
    simpa using this
  have hAd : AnalyticAt ℂ (deriv ZD.riemannXi) (linePt γ) := hA.deriv
  intro hzero
  rw [hAd.analyticOrderAt_eq_zero] at hd0
  exact hd0 hzero

/-- **The transversal flip**: a simple on-line zero flips the real readout in
every sufficiently small symmetric window. -/
theorem simple_zero_flips {γ : ℝ} (hγ : γ ≠ 0)
    (hmem : linePt γ ∈ ZD.NontrivialZeros)
    (hm : Zeta23.zeroMult (linePt γ) = 1) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      XiLine (γ - δ) * XiLine (γ + δ) < 0 := by
  set c := (I * deriv ZD.riemannXi (linePt γ)).re with hcdef
  have hc0 : c ≠ 0 := by
    have hne := deriv_xi_ne_zero_of_simple hγ hm
    have hre := xi_deriv_line_re γ
    rw [hcdef]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im]
    intro h
    apply hne
    have him0 : (deriv ZD.riemannXi (linePt γ)).im = 0 := by linarith
    apply Complex.ext
    · simpa using hre
    · simpa using him0
  have hzero : XiLine γ = 0 := XiLine_zero_iff.mpr hmem
  have htend := hasDerivAt_iff_tendsto_slope.mp (XiLine_hasDerivAt γ)
  rw [← hcdef] at htend
  have hball : Metric.ball c (|c|/2) ∈ nhds c :=
    Metric.ball_mem_nhds _ (by positivity)
  have hev : ∀ᶠ t in nhdsWithin γ {γ}ᶜ,
      slope XiLine γ t ∈ Metric.ball c (|c|/2) := htend.eventually_mem hball
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεs⟩ := hev
  refine ⟨ε, hε, fun δ hδ0 hδε => ?_⟩
  have hdp : dist (γ + δ) γ < ε := by
    rw [Real.dist_eq, show γ + δ - γ = δ by ring, abs_of_pos hδ0]
    exact hδε
  have hdm : dist (γ - δ) γ < ε := by
    rw [Real.dist_eq, show γ - δ - γ = -δ by ring, abs_neg, abs_of_pos hδ0]
    exact hδε
  have hnp : (γ + δ) ∈ ({γ}ᶜ : Set ℝ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    linarith
  have hnm : (γ - δ) ∈ ({γ}ᶜ : Set ℝ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    linarith
  have hplus := hεs hdp hnp
  have hminus := hεs hdm hnm
  -- the slopes have the sign of c, and XiLine(γ±δ) = slope·(±δ)
  rw [Metric.mem_ball, Real.dist_eq] at hplus hminus
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hsp : XiLine (γ + δ) = slope XiLine γ (γ + δ) * δ := by
    rw [slope_def_field, hzero, show γ + δ - γ = δ by ring]
    field_simp [hδne]
    ring
  have hsm : XiLine (γ - δ) = slope XiLine γ (γ - δ) * (-δ) := by
    rw [slope_def_field, hzero, show γ - δ - γ = -δ by ring]
    field_simp [hδne]
    ring
  rw [hsp, hsm]
  rcases abs_cases c with ⟨hac, hc⟩ | ⟨hac, hc⟩
  · -- c ≥ 0 (hence > 0): both slopes > c/2 > 0
    have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    rw [hac] at hplus hminus
    have h1 : c/2 < slope XiLine γ (γ + δ) := by
      have := abs_lt.mp hplus
      linarith [this.1]
    have h2 : c/2 < slope XiLine γ (γ - δ) := by
      have := abs_lt.mp hminus
      linarith [this.1]
    have hp1 : (0:ℝ) < slope XiLine γ (γ + δ) := by linarith
    have hp2 : (0:ℝ) < slope XiLine γ (γ - δ) := by linarith
    nlinarith [mul_pos hp1 hp2, mul_pos hδ0 hδ0]
  · -- c < 0: both slopes < c/2 < 0
    have hcneg : c < 0 := hc
    rw [hac] at hplus hminus
    have h1 : slope XiLine γ (γ + δ) < c/2 := by
      have := abs_lt.mp hplus
      linarith [this.2]
    have h2 : slope XiLine γ (γ - δ) < c/2 := by
      have := abs_lt.mp hminus
      linarith [this.2]
    have hp1 : slope XiLine γ (γ + δ) < 0 := by linarith
    have hp2 : slope XiLine γ (γ - δ) < 0 := by linarith
    nlinarith [mul_pos_of_neg_of_neg hp1 hp2, mul_pos hδ0 hδ0]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.xi_deriv_line_re
#print axioms CriticalLinePhasor.SeatingLedger.deriv_xi_ne_zero_of_simple
#print axioms CriticalLinePhasor.SeatingLedger.simple_zero_flips
