import RequestProject.HelixHermitianTraceLimit
import RequestProject.HilbertPolya
import RequestProject.HelixResolventCapture

/-!
# The line tower: the canonical candidate for the trace-limit box

`HelixHermitianTraceLimit` reduces GRH to one locally-uniform limit (`hlim`) over an arbitrary
Hermitian tower.  This file names the canonical candidate and aims the reduction at Mathlib's
`RiemannHypothesis`.

* The **normalized spectrum trace** generalizes the canonical trace by per-term constant
  offsets — the Hadamard normalization the divergent raw sum requires (the audited frontier's
  differencing), with off-real holomorphy still a per-stage theorem.
* The reduction tolerates an **entire correction** `E`: the compiled Hadamard bridge writes the
  completed channel as an entire part plus the normalized pole sum, so the target of the limit
  is `T - E`, not `T` itself.
* The **mod-one resonance** (`completed_logDeriv_not_tendsto_modOne`) extends the compiled
  completed resonance to the trivial character via `completedLFunction_modOne_eq` and the
  analyticity of `completedRiemannZeta` off `{0, 1}` — so the reduction reaches ζ itself.
* The **line tower** (`lineTowerSpectrum`) is the compiled window ledger: its stage spectra are
  the zero ordinates of the window, every spectral value marks an exact vanishing
  (`eigenheight_is_exact_vanishing`), and the compiled Hermitian realization is the ledger
  diagonal `hpOperator` (`hpOperator_isHermitian`), whose diagonal is literally this spectrum.

The capstone `rh_of_lineTower_traceLimit`: if the line tower's normalized traces converge
locally uniformly off the real axis to the completed ζ-channel minus an entire part, then
Mathlib's `RiemannHypothesis` holds.  Register, priced exactly: `hlim` for the line tower is
the wall itself — the tower indexes the *on-line* census, so its trace limit reaching the full
channel is precisely the statement that the off-line defect is empty.  Nothing here proves
`hlim`; what is proven is that the entire remaining distance to RH is that single limit, with
self-adjointness (real stage spectra ⟹ off-real stage holomorphy) doing the mechanism's work.
No RH/GRH is assumed anywhere in this file.
-/

open Filter Topology Complex DirichletCharacter

namespace CriticalLinePhasor.CaptureInterfaceAudit

open CriticalLinePhasor.ResidueJump CriticalLinePhasor.HilbertPolya
open CriticalLinePhasor.CarrierScale

/-! ## The normalized spectrum trace -/

/-- The normalized resolvent trace of a real spectrum: the canonical trace with a per-term
constant offset — the Hadamard/differencing normalization. -/
noncomputable def normalizedSpectrumTrace {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ j, ((z - ((d j : ℝ) : ℂ))⁻¹ + c j)

/-- Every normalized stage is holomorphic off the real axis: the spectrum is real and the
offsets are constant in `z` — spectral reality is the whole mechanism. -/
lemma normalizedSpectrumTrace_differentiableOn {ι : Type*} [Fintype ι]
    (d : ι → ℝ) (c : ι → ℂ) :
    DifferentiableOn ℂ (normalizedSpectrumTrace d c) offReal := by
  unfold normalizedSpectrumTrace
  refine DifferentiableOn.fun_sum fun j _ => DifferentiableOn.add ?_
    (differentiableOn_const _)
  refine DifferentiableOn.inv ((differentiable_id.sub_const _).differentiableOn) ?_
  intro z hz h0
  have him : (z - ((d j : ℝ) : ℂ)).im = z.im := by simp
  rw [h0] at him
  exact hz (by simpa using him.symm)

/-! ## The analytic core of the reduction -/

/-- **The trace-limit core.**  If the normalized traces of a real-spectrum tower converge
locally uniformly off the real axis to `T - E` with `E` entire, and `T` resonates at the pole
parameter of `ρ`, then `ρ` lies on the critical line. -/
theorem re_half_of_traceLimit
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (d : ∀ n, ι n → ℝ) (c : ∀ n, ι n → ℂ) (T E : ℂ → ℂ)
    (hE : Differentiable ℂ E)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (d n) (c n)) (fun z => T z - E z) atTop offReal)
    {ρ : ℂ}
    (hres : ¬ ∃ L, Tendsto T (𝓝[≠] (HelixLimit.poleParam ρ)) (𝓝 L)) :
    ρ.re = 1 / 2 := by
  by_contra hre
  have hz : HelixLimit.poleParam ρ ∈ offReal := by
    simp only [offReal, Set.mem_setOf_eq, HelixLimit.poleParam_im]
    intro h
    exact hre (by linarith)
  have hsub : DifferentiableOn ℂ (fun z => T z - E z) offReal :=
    hlim.differentiableOn
      (Eventually.of_forall fun n => normalizedSpectrumTrace_differentiableOn (d n) (c n))
      isOpen_offReal
  have hT : DifferentiableAt ℂ T (HelixLimit.poleParam ρ) := by
    have h1 : DifferentiableAt ℂ (fun z => T z - E z) (HelixLimit.poleParam ρ) :=
      hsub.differentiableAt (isOpen_offReal.mem_nhds hz)
    have h2 : DifferentiableAt ℂ (fun z => (T z - E z) + E z) (HelixLimit.poleParam ρ) :=
      h1.add (hE.differentiableAt)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards with z
    ring
  exact hres ⟨T (HelixLimit.poleParam ρ),
    (hT.continuousAt.tendsto).mono_left nhdsWithin_le_nhds⟩

/-! ## The mod-one (ζ) resonance -/

variable {N : ℕ} [NeZero N]

/-- **Completed resonance at the trivial character**: `-Λ'/Λ` for the mod-one L-function — the
completed ζ — has no finite limit at any nontrivial zero.  Extends the compiled resonance past
the `χ ≠ 1` hypothesis via `completedLFunction_modOne_eq` and the analyticity of
`completedRiemannZeta` away from `{0, 1}`. -/
theorem completed_logDeriv_not_tendsto_modOne (χ₁ : DirichletCharacter ℂ 1)
    {ρ : ℂ} (hρ : ρ ∈ GRHSpectral.NontrivialZeros χ₁) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv (completedLFunction χ₁) s) (𝓝[≠] ρ) (𝓝 L) := by
  have hzero := completedLFunction_zero_of_mem_nontrivialZeros hρ
  obtain ⟨hre0, hre1, -⟩ := hρ
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at hre1; simp at hre1
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hre0; simp at hre0
  have hana : AnalyticAt ℂ (completedLFunction χ₁) ρ := by
    rw [completedLFunction_modOne_eq]
    have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) := by
      rw [show ({0, 1}ᶜ : Set ℂ) = {0}ᶜ ∩ {1}ᶜ by ext s; simp [not_or]]
      exact isOpen_compl_singleton.inter isOpen_compl_singleton
    have hdiffOn : DifferentiableOn ℂ completedRiemannZeta ({0, 1}ᶜ : Set ℂ) := by
      intro s hs
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
      exact (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt
    exact hdiffOn.analyticAt (hopen.mem_nhds (by simp [hρ0, hρ1]))
  exact HelixSource.logDeriv_not_tendsto hana hzero
    (completedLFunction_not_eventuallyEq_zero hρ1 hρ0)

/-- The chart transport of a log-derivative resonance: generic in the underlying completed
function, factored from the compiled `completed_resonates_of_traceIdentity`. -/
theorem chart_resonates_of_logDeriv_resonance {F T : ℂ → ℂ}
    (hid : ∀ z, T z = -logDeriv F (1 / 2 + Complex.I * z)) {ρ : ℂ}
    (hres : ¬ ∃ L, Tendsto (fun s => -logDeriv F s) (𝓝[≠] ρ) (𝓝 L)) :
    ¬ ∃ L, Tendsto T (𝓝[≠] (HelixLimit.poleParam ρ)) (𝓝 L) := by
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = HelixLimit.poleParam ρ := by
    rw [HelixLimit.poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  rintro ⟨L, hL⟩
  refine hres ⟨L, ?_⟩
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
  have heqfun : (fun s : ℂ => -logDeriv F s)
      = (T ∘ fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    funext s
    simp only [Function.comp_apply, hid, key]
  rw [heqfun]
  exact hcomp

/-! ## The line tower -/

/-- **The canonical line tower**: the spectrum of the compiled window ledger at height `n` —
one real spectral value per unit of multiplicity, the zero ordinates of the window. -/
noncomputable def lineTowerSpectrum (n : ℕ) : WindowIndex (n : ℝ) → ℝ :=
  fun p => p.1.1

/-- Every spectral value of the line tower marks an exact vanishing: `ζ(½ + iγ) = 0` on the
nose. -/
theorem lineTowerSpectrum_isZeroOrdinate (n : ℕ) (p : WindowIndex (n : ℝ)) :
    riemannZeta (line (lineTowerSpectrum n p)) = 0 :=
  eigenheight_is_exact_vanishing p

/-- The line tower is realized by the compiled Hermitian ledger diagonal: the diagonal of
`hpOperator` is literally this spectrum (and `hpOperator_isHermitian` supplies the
self-adjointness). -/
theorem hpOperator_diagonal_eq_lineTowerSpectrum (n : ℕ) (p : WindowIndex (n : ℝ)) :
    hpOperator (n : ℝ) p p = ((lineTowerSpectrum n p : ℝ) : ℂ) := by
  simp [hpOperator, lineTowerSpectrum, Matrix.diagonal_apply_eq]

/-! ## The capstones -/

/-- **GRH at the trivial character from the line-tower trace limit.**  If the line tower's
normalized traces converge locally uniformly off the real axis to the completed mod-one
channel minus an entire part, then every nontrivial zero is on the line. -/
theorem grh_modOne_of_lineTower_traceLimit (χ₁ : DirichletCharacter ℂ 1)
    (c : ∀ n : ℕ, WindowIndex (n : ℝ) → ℂ) (T E : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (completedLFunction χ₁) (1 / 2 + Complex.I * z))
    (hE : Differentiable ℂ E)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (lineTowerSpectrum n) (c n))
      (fun z => T z - E z) atTop offReal) :
    GRHSpectral.GRH χ₁ := fun _ hρ =>
  re_half_of_traceLimit lineTowerSpectrum c T E hE hlim
    (chart_resonates_of_logDeriv_resonance hid
      (completed_logDeriv_not_tendsto_modOne χ₁ hρ))

/-- **RH from the line-tower trace limit — the wall in one statement.**  If the canonical line
tower's normalized traces converge locally uniformly off the real axis to the completed
ζ-channel minus an entire part, Mathlib's `RiemannHypothesis` follows.  The tower indexes the
on-line census, so this `hlim` is the coverage wall itself, stated as a single analytic limit;
everything downstream — per-stage off-real holomorphy from spectral reality, Weierstrass,
the completed resonance, and the mod-one hinge — is compiled. -/
theorem rh_of_lineTower_traceLimit (χ₁ : DirichletCharacter ℂ 1)
    (c : ∀ n : ℕ, WindowIndex (n : ℝ) → ℂ) (T E : ℂ → ℂ)
    (hid : ∀ z, T z = -logDeriv (completedLFunction χ₁) (1 / 2 + Complex.I * z))
    (hE : Differentiable ℂ E)
    (hlim : TendstoLocallyUniformlyOn
      (fun n => normalizedSpectrumTrace (lineTowerSpectrum n) (c n))
      (fun z => T z - E z) atTop offReal) :
    RiemannHypothesis :=
  HelixLimit.RH_of_GRH_Trivial_Char χ₁
    (grh_modOne_of_lineTower_traceLimit χ₁ c T E hid hE hlim)

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.normalizedSpectrumTrace_differentiableOn
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.re_half_of_traceLimit
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.completed_logDeriv_not_tendsto_modOne
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.chart_resonates_of_logDeriv_resonance
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.lineTowerSpectrum_isZeroOrdinate
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.grh_modOne_of_lineTower_traceLimit
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.rh_of_lineTower_traceLimit
