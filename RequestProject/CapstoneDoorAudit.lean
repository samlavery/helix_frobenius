import RequestProject.HelixResolventCapture

/-!
# Capstone door audit: the rule-14 inhabitant check, run on `HelixResolventCapture`

This file runs the inhabitant check (`node / inhabitant / input / verdict`, field 1 of the
response envelope) on the two named readings of `HelixResolventCapture.lean`, and records the
outcome as compiled theorems rather than prose.

## 1D-correlation reading

`OneDCorrelationEvidence χ` asks that every `ρ` with `LFunction χ ρ = 0` carry a nonzero kernel
vector of `specOp (vonNeumannOp γ) ρ` at `γ = ρ.im`.  Unfolding the three definitions involved
(`vonNeumannOp γ = γ • id` on `ℂ`, `specHeight s = -i(s - 1/2)`, `specBchan γ s = γ - specHeight s`)
the kernel condition is *definitionally* the pair of real equations `Re ρ = 1/2` and `γ = Im ρ`
(`specOp_kernel_iff_line_and_height`).  Two consequences, both compiled below.

* The quantifier is over **all** zeros of `LFunction χ`, not the strip zeros.  At modulus one
  `LFunction χ₁ = riemannZeta`, whose trivial zero at `-2` has real part `-2 ≠ 1/2`.  So
  `OneDCorrelationEvidence χ₁` is **false** (`not_oneDCorrelationEvidence_modOne`), the hypothesis
  of `HelixLimit.RH_of_resolvant_trace_1D_correlation` is uninhabited, and that implication is
  vacuously true (`rh_1D_reading_hypothesis_uninhabited`).  The same instantiation at `M = 1`
  empties `HelixLimit.grhComplete_of_resolvant_trace_1D_correlation`
  (`grhComplete_1D_reading_hypothesis_uninhabited`).
* Restricting the quantifier to `GRHSpectral.NontrivialZeros χ` — the repair — produces a premise
  that gives `GRHSpectral.GRH χ` unconditionally (`grh_of_oneDCorrelationEvidenceStrip`).  The fibre
  operator contributes no arithmetic input: the implication is `Im (γ - specHeight ρ) = Re ρ - 1/2`.

## 3D-real reading

Already settled inside `HelixResolventCapture.lean` itself by
`grh_and_nativeCarrierCoverage_of_threeDCrossings`: the premise `ThreeD_crossings_are_real_zeros χ`
gives `GRH χ ∧ NativeCarrierCoverage χ`, so the conclusion is one of its own consequences
(`threeD_premise_contains_conclusion`).

No `axiom`, no `sorry`; footprint audited by the `#print axioms` block at the bottom.
-/

namespace CapstoneDoorAudit

open Complex CriticalLinePhasor CriticalLinePhasor.RiemannEvidence
open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.UnconditionalFrobenius

/-! ## 1. What a fibre kernel event says -/

/-- **The fibre kernel event carries no information beyond the critical line.**
A nonzero kernel vector of `specOp (vonNeumannOp γ) s` exists iff `Re s = 1/2` and `γ = Im s`.
Both directions are elementary algebra on `specBchan γ s = γ + i(1/2 - s)`; nothing about
`L`-functions, primes, or the Euler product enters. -/
theorem specOp_kernel_iff_line_and_height (γ : ℝ) (s : ℂ) :
    (∃ ψ : ℂ, ψ ≠ 0 ∧ specOp (vonNeumannOp γ) s ψ = 0) ↔ (s.re = 1 / 2 ∧ γ = s.im) := by
  rw [specOp_kernel_iff_specBchan_zero]
  constructor
  · intro h
    have hre : (specBchan γ s).re = 0 := by rw [h]; simp
    have him : (specBchan γ s).im = 0 := by rw [h]; simp
    rw [specBchan_re] at hre
    rw [specBchan_im] at him
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hline, hgam⟩
    apply Complex.ext
    · rw [specBchan_re, hgam]; simp
    · rw [specBchan_im, hline]; simp

/-! ## 2. The 1D-correlation door is uninhabited -/

/-- **The 1D-correlation premise is false at modulus one.**
`OneDCorrelationEvidence` quantifies over every zero of `LFunction χ`, including the trivial
zeros.  At modulus one `LFunction χ₁ = riemannZeta`, and `riemannZeta (-2) = 0` with
`Re (-2) = -2 ≠ 1/2`. -/
theorem not_oneDCorrelationEvidence_modOne (χ₁ : DirichletCharacter ℂ 1) :
    ¬ OneDCorrelationEvidence χ₁ := by
  intro h
  have hz : DirichletCharacter.LFunction χ₁ (-2 : ℂ) = 0 := by
    rw [DirichletCharacter.LFunction_modOne_eq]
    have h0 := riemannZeta_neg_two_mul_nat_add_one 0
    norm_num at h0
    exact h0
  have hchart : OneDChartZero χ₁ (-2 : ℂ) := ⟨hz, (-2 : ℂ).im, rfl⟩
  obtain ⟨γ, ψ, hψ, hker, _⟩ := h hchart
  have hre := ((specOp_kernel_iff_line_and_height γ (-2 : ℂ)).mp ⟨ψ, hψ, hker⟩).1
  norm_num at hre

/-- **`RH_of_resolvant_trace_1D_correlation` is vacuous**: its hypothesis has no inhabitant. -/
theorem rh_1D_reading_hypothesis_uninhabited (χ₁ : DirichletCharacter ℂ 1) :
    ¬ (OneDCorrelationEvidence χ₁ ∧ HelixLimit.OneD_zeta_zero_correlated χ₁) :=
  fun h => not_oneDCorrelationEvidence_modOne χ₁ h.1

/-- **`grhComplete_of_resolvant_trace_1D_correlation` is vacuous**: instantiating its
all-moduli hypothesis at `M = 1` reproduces the refuted premise. -/
theorem grhComplete_1D_reading_hypothesis_uninhabited :
    ¬ (∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
        OneDCorrelationEvidence χ ∧ HelixLimit.OneD_zeta_zero_correlated χ) := by
  intro h
  exact not_oneDCorrelationEvidence_modOne 1 (h 1 1).1

/-! ## 3. The repaired 1D premise gives GRH -/

/-- The 1D-correlation premise with its quantifier corrected to range over the strip zeros. -/
def OneDCorrelationEvidenceStrip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ ∈ GRHSpectral.NontrivialZeros χ, ∃ γ : ℝ, ∃ ψ : ℂ, ψ ≠ 0 ∧
    specOp (vonNeumannOp γ) ρ ψ = 0 ∧ γ = ρ.im

/-- **The repaired premise gives the conclusion**, unconditionally; no arithmetic input is
consumed. -/
theorem grh_of_oneDCorrelationEvidenceStrip {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : OneDCorrelationEvidenceStrip χ) : GRHSpectral.GRH χ := by
  intro ρ hρ
  obtain ⟨γ, ψ, hψ, hker, _⟩ := h ρ hρ
  exact ((specOp_kernel_iff_line_and_height γ ρ).mp ⟨ψ, hψ, hker⟩).1

/-! ## 4. The 3D-real door contains its own conclusion -/

/-- The 3D premise gives GRH as one of its own consequences. -/
theorem threeD_premise_contains_conclusion {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : HelixLimit.ThreeD_crossings_are_real_zeros χ) : GRHSpectral.GRH χ :=
  (HelixLimit.grh_and_nativeCarrierCoverage_of_threeDCrossings χ h).1

/-- **Unfolding the coverage conjunct.**  `CompletedThreeDZeroAtHeight χ Z` is
`0 < Z ∧ Dcell χ Z = 0`; the cell residual vanishes iff the `L`-value at the represented point
vanishes (`HarmonicCell.focal_residual_zero_iff_L_zero`), and at `Z = exp y` the represented point
is `carrierAbscissa + i y = 1/2 + i y`.  So coverage says: every strip zero's ordinate also
carries an on-line zero. -/
theorem nativeCarrierCoverage_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    HelixLimit.NativeCarrierCoverage χ ↔
      ∀ ρ ∈ GRHSpectral.NontrivialZeros χ,
        DirichletCharacter.LFunction χ (1 / 2 + Complex.I * (ρ.im : ℂ)) = 0 := by
  constructor
  · intro h ρ hρ
    have hcell := (h ρ hρ).2
    have hL := (HarmonicCell.focal_residual_zero_iff_L_zero χ (Real.exp ρ.im)).mp hcell
    rwa [ThreeDFocal.reprPoint_eq_carrierPointAtHeight χ _ (Real.exp_pos _),
      ThreeDFocal.carrierPointAtHeight_exp, ThreeDFocal.carrierPoint_eq_half_add_I] at hL
  · intro h ρ hρ
    refine ⟨Real.exp_pos _, ?_⟩
    refine (HarmonicCell.focal_residual_zero_iff_L_zero χ (Real.exp ρ.im)).mpr ?_
    rw [ThreeDFocal.reprPoint_eq_carrierPointAtHeight χ _ (Real.exp_pos _),
      ThreeDFocal.carrierPointAtHeight_exp, ThreeDFocal.carrierPoint_eq_half_add_I]
    exact h ρ hρ

end CapstoneDoorAudit

#print axioms CapstoneDoorAudit.specOp_kernel_iff_line_and_height
#print axioms CapstoneDoorAudit.not_oneDCorrelationEvidence_modOne
#print axioms CapstoneDoorAudit.rh_1D_reading_hypothesis_uninhabited
#print axioms CapstoneDoorAudit.grhComplete_1D_reading_hypothesis_uninhabited
#print axioms CapstoneDoorAudit.grh_of_oneDCorrelationEvidenceStrip
#print axioms CapstoneDoorAudit.threeD_premise_contains_conclusion
#print axioms CapstoneDoorAudit.nativeCarrierCoverage_iff
