import RequestProject.HelixResolventCapture

/-!
# The capture route, audited: the uncompleted interface is unsatisfiable

Closing the analytic-coverage route means instantiating
`grh_of_selfAdjoint_resolvent_capture`: a self-adjoint `a` whose regularized resolvent trace
`T z = -L'/L(1/2 + iz)` is regular off `spectrum ℂ a`.  **This file proves that no such
instantiation exists** — for the pinned *uncompleted* `DirichletCharacter.LFunction`, the
route is closed negatively, by the trivial zeros:

`ζ(-2) = 0` (Mathlib), so `T` has a genuine pole at `z₀ = (5/2)·I` (the affine image of
`s = -2`).  A self-adjoint element has real spectrum, so `z₀` is *always* off-spectrum, and
`hReg` demands a finite limit exactly where the trivial zero forbids one
(`no_selfAdjoint_uncompleted_capture`, from the same `logDeriv_not_tendsto` machinery that
powers the resonance lemma at nontrivial zeros).

Consequences, exact: the completion route as previously typed can never be closed by any
operator; it must be **re-typed on the completed L-function** (entire for nontrivial primitive
`χ`, so the only singularities of the completed trace are the nontrivial-zero images), with the
principal character routed through the pole-stripped completed zeta.  The re-typed capstone is
the corrected target; its resonance lemma (completed `-Λ'/Λ` poles exactly at the zero images)
is the named next construction.  This audit is the falsification machinery running on the
house's own interface: the named route was tested and it broke, one theorem names where.
No `sorry`, no `axiom`.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CaptureInterfaceAudit

/-- The mod-one (principal) character: its `LFunction` is `riemannZeta`. -/
local notation "χ₁" => (1 : DirichletCharacter ℂ 1)

/-- `-ζ'/ζ` has no finite limit at the first trivial zero `s = -2`: the same
analytic/zero/not-locally-zero machinery as the nontrivial-zero resonance lemma, applied at
the trivial zero Mathlib supplies. -/
theorem logDeriv_not_tendsto_neg_two :
    ¬ ∃ L, Tendsto (fun s => -logDeriv (DirichletCharacter.LFunction χ₁) s)
      (𝓝[≠] (-2 : ℂ)) (𝓝 L) := by
  have hne1 : (-2 : ℂ) ≠ 1 := by norm_num
  refine HelixSource.logDeriv_not_tendsto
    (HelixSource.LFunction_analyticOnNhd χ₁ (-2) (Set.mem_compl_singleton_iff.mpr hne1))
    ?_ (HelixSource.LFunction_not_eventuallyEq_zero χ₁ hne1)
  rw [DirichletCharacter.LFunction_modOne_eq]
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

/-- **The uncompleted capture interface is unsatisfiable.**  No self-adjoint element of any
C*-algebra admits the regularity hypothesis of `grh_of_selfAdjoint_resolvent_capture` for the
pinned uncompleted trace: the trivial zero `s = -2` puts a genuine pole of `T` at the non-real
point `z₀ = (5/2)·I`, which is off every real (self-adjoint) spectrum, exactly where `hReg`
demands a finite limit. -/
theorem no_selfAdjoint_uncompleted_capture
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (DirichletCharacter.LFunction χ₁)
      (1 / 2 + Complex.I * z)) :
    ¬ ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L) := by
  intro hReg
  -- the trivial-zero image is off every self-adjoint spectrum
  have hz₀ : ((5 / 2 : ℂ) * Complex.I) ∉ spectrum ℂ a := by
    intro hmem
    have him := ha.im_eq_zero_of_mem_spectrum hmem
    simp [Complex.mul_im] at him
  obtain ⟨L, hL⟩ := hReg _ hz₀
  -- transport the finite limit through the affine chart to `s = -2`
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have himg : -Complex.I * ((-2 : ℂ) - 1 / 2) = (5 / 2 : ℂ) * Complex.I := by ring
  refine logDeriv_not_tendsto_neg_two ⟨L, ?_⟩
  have hcont : Tendsto (fun s : ℂ => -Complex.I * (s - 1 / 2)) (𝓝[≠] (-2 : ℂ))
      (𝓝[≠] ((5 / 2 : ℂ) * Complex.I)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hc : Continuous (fun s : ℂ => -Complex.I * (s - 1 / 2)) := by fun_prop
      have hct := hc.tendsto (-2 : ℂ)
      rwa [himg] at hct
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro hc
      rw [← himg] at hc
      have h3 : -Complex.I * ((s - 1 / 2) - ((-2 : ℂ) - 1 / 2)) = 0 := by linear_combination hc
      have h4 : (s - 1 / 2) - ((-2 : ℂ) - 1 / 2) = 0 :=
        (mul_eq_zero.mp h3).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
      exact hs (by linear_combination h4)
  have hcomp := hL.comp hcont
  have heqfun : (fun s : ℂ => -logDeriv (DirichletCharacter.LFunction χ₁) s)
      = (T ∘ fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    funext s
    simp only [Function.comp_apply, hid, key]
  rw [heqfun]
  exact hcomp

/-! ## The corrected capstone: capture typed on the completed function

The carrier-native object is the completed `L`-function; its trace is singular exactly at the
zero images.  The three lemmas below supply the completed resonance, and the capstone re-types
`grh_of_selfAdjoint_resolvent_capture` on the completed object — satisfiable in principle, so
the remaining closure step is the operator itself. -/

section Completed

open DirichletCharacter

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The completed `L`-function vanishes at every nontrivial zero: the gamma factor is
nonvanishing in the strip, so the chart zero is a completed zero. -/
theorem completedLFunction_zero_of_mem_nontrivialZeros
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    completedLFunction χ ρ = 0 := by
  obtain ⟨hre0, hre1, hzero⟩ := hρ
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hre0; simp at hre0
  have hγ : χ.gammaFactor ρ ≠ 0 := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos hre0
    · rw [ho.gammaFactor_def]
      refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
      rw [Complex.add_re, Complex.one_re]
      linarith
  have hdiv := (LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hρ0)).symm
  rw [hzero] at hdiv
  rcases div_eq_zero_iff.mp hdiv with h | h
  · exact h
  · exact absurd h hγ

/-- The completed `L`-function is not locally zero near a strip point. -/
theorem completedLFunction_not_eventuallyEq_zero
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) :
    ¬ (completedLFunction χ) =ᶠ[nhds ρ] 0 := by
  intro hev
  refine HelixSource.LFunction_not_eventuallyEq_zero χ hρ1 ?_
  filter_upwards [hev, eventually_ne_nhds hρ0] with s hs hs0
  simp only [Pi.zero_apply] at hs ⊢
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0), hs, zero_div]

/-- **Completed resonance**: `-Λ'/Λ` has no finite limit at any nontrivial zero. -/
theorem completed_logDeriv_not_tendsto (hχ : χ ≠ 1)
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv (completedLFunction χ) s) (𝓝[≠] ρ) (𝓝 L) := by
  have hzero := completedLFunction_zero_of_mem_nontrivialZeros hρ
  obtain ⟨hre0, hre1, -⟩ := hρ
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at hre1; simp at hre1
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hre0; simp at hre0
  exact HelixSource.logDeriv_not_tendsto
    ((differentiable_completedLFunction hχ).analyticAt ρ)
    hzero (completedLFunction_not_eventuallyEq_zero hρ1 hρ0)

/-- Completed resonance in the chart coordinate: the completed trace has no finite limit at
any zero image. -/
theorem completed_resonates_of_traceIdentity (hχ : χ ≠ 1) {T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv (completedLFunction χ) (1 / 2 + Complex.I * z))
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ) :
    ¬ ∃ L, Tendsto T (𝓝[≠] (HelixLimit.poleParam ρ)) (𝓝 L) := by
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = HelixLimit.poleParam ρ := by
    rw [HelixLimit.poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  rintro ⟨L, hL⟩
  refine completed_logDeriv_not_tendsto hχ hρ ⟨L, ?_⟩
  have hcont : Tendsto (fun s : ℂ => -Complex.I * (s - 1 / 2)) (𝓝[≠] ρ)
      (𝓝[≠] (HelixLimit.poleParam ρ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hc : Continuous (fun s : ℂ => -Complex.I * (s - 1 / 2)) := by fun_prop
      have hct := hc.tendsto ρ
      rwa [hhρ] at hct
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro hc
      rw [← hhρ] at hc
      have h3 : -Complex.I * ((s - 1 / 2) - (ρ - 1 / 2)) = 0 := by linear_combination hc
      have h4 : (s - 1 / 2) - (ρ - 1 / 2) = 0 :=
        (mul_eq_zero.mp h3).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
      exact hs (by linear_combination h4)
  have hcomp := hL.comp hcont
  have heqfun : (fun s : ℂ => -logDeriv (completedLFunction χ) s)
      = (T ∘ fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    funext s
    simp only [Function.comp_apply, hid, key]
  rw [heqfun]
  exact hcomp

/-- **The corrected capture capstone, typed on the completed function.**  A self-adjoint
channel whose regularized resolvent trace is the completed `-Λ'/Λ(1/2 + i·)` and is regular
off its spectrum forces GRH — and unlike the uncompleted typing, this interface is
satisfiable in principle: the completed trace is singular exactly at the zero images.  The
remaining closure step is the operator. -/
theorem grh_of_selfAdjoint_completed_resolvent_capture
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (T : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (completedLFunction χ) (1 / 2 + Complex.I * z))
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto T (𝓝[≠] z) (𝓝 L)) :
    GRHSpectral.GRH χ :=
  HelixLimit.grh_of_selfAdjoint_spectral_capture ha χ (fun ρ hρ => by
    by_contra hns
    exact completed_resonates_of_traceIdentity hχ hid hρ (hReg _ hns))

end Completed

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.completed_logDeriv_not_tendsto
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.grh_of_selfAdjoint_completed_resolvent_capture
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.logDeriv_not_tendsto_neg_two
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.no_selfAdjoint_uncompleted_capture
