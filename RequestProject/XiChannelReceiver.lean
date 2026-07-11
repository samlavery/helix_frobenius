import RequestProject.HelixSpectralLimit
import RequestProject.HelixSource
import RequestProject.XiHadamardQuotient
import RequestProject.RiemannHypothesisBridge
import RequestProject.HelixCollapseReality

/-!
# The ξ-channel receiver: exact singular set, and RH as regularity off the reals

Stage 2, deliverables D1 + D3.  The capture capstone (`HelixResolventCapture`) consumes a
trace channel whose singularities mark the zeros.  The **clean channel is ξ**: the finite
`L`'s log-derivative also has poles at the trivial zeros (at non-real spectral parameters,
which no self-adjoint spectrum can absorb), while ξ is entire with zero set *exactly* the
nontrivial zeros (`riemannXi_eq_zero_iff`).  This file proves, unconditionally:

* **Resonance** (`xiChannel_resonates`): the ξ-channel `T(z) = −ξ′/ξ(½ + iz)` has no
  finite limit at `poleParam ρ` for every nontrivial zero `ρ` — inherited, with
  multiplicity, from the log-derivative pole (`HelixSource.logDeriv_not_tendsto`).
* **Regularity** (`xiChannel_regular`): at every `z₀` whose line point is *not* a zero,
  the channel has a finite limit.  Together: **the singular set of the ξ-channel is
  exactly `poleParam '' NontrivialZeros`** — no archimedean noise, no pole at `s = 0, 1`.
* **The equivalence** (`xiChannel_offReal_regular_iff_RH`): Mathlib's literal
  `RiemannHypothesis` is *equivalent* to "the ξ-channel is regular off the real axis".
  A sourceless zero **is** a resonance of the channel at a non-real parameter.
* **The capstone corollary** (`RiemannHypothesis_of_selfAdjoint_xiChannel_receiver`):
  any self-adjoint receiver of the ξ-channel — regular off its (automatically real)
  spectrum — forces `RiemannHypothesis`, by spectral reality alone.

Everything here is unconditional: no RH is assumed, and the equivalence isolates the
dangerous hypothesis `hReg` in its exact operator form.  The remaining Stage-2 work
(D2) is the ledger operator whose spectrum is the closed ±event set.  No `sorry`, no
`axiom` beyond the standard three.
-/

open Complex Filter Topology HelixLimit

namespace CriticalLinePhasor.XiChannel

/-- **The ξ-channel**: the regularized trace `T(z) = −ξ′/ξ(½ + iz)` — the completed,
archimedean-clean readout of the zero ledger in the spectral chart `s = ½ + iz`. -/
noncomputable def xiChannel (z : ℂ) : ℂ :=
  -logDeriv ZD.riemannXi (1 / 2 + Complex.I * z)

/-! ## §1 Resonance at every nontrivial zero -/

/-- The s-plane resonance: `−ξ′/ξ` has no finite limit at any nontrivial zero. -/
theorem xi_neg_logDeriv_not_tendsto {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ¬ ∃ L, Tendsto (fun s => -logDeriv ZD.riemannXi s) (𝓝[≠] ρ) (𝓝 L) := by
  refine HelixSource.logDeriv_not_tendsto (ZD.riemannXi_differentiable.analyticAt ρ)
    ((ZD.riemannXi_eq_zero_iff ρ).mpr hρ) ?_
  intro hev
  exact ZD.riemannXi_analyticOrderAt_ne_top_everywhere ρ (analyticOrderAt_eq_top.mpr hev)

/-- **Resonance in the spectral chart**: the ξ-channel has no finite limit at the
spectral parameter of any nontrivial zero. -/
theorem xiChannel_resonates {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ¬ ∃ L, Tendsto xiChannel (𝓝[≠] (poleParam ρ)) (𝓝 L) := by
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hhρ : -Complex.I * (ρ - 1 / 2) = poleParam ρ := by
    rw [poleParam]
    linear_combination Complex.I * Complex.re_add_im ρ - (ρ.im : ℂ) * Complex.I_sq
  rintro ⟨L, hL⟩
  refine xi_neg_logDeriv_not_tendsto hρ ⟨L, ?_⟩
  have hcont : Tendsto (fun s : ℂ => -Complex.I * (s - 1 / 2)) (𝓝[≠] ρ)
      (𝓝[≠] (poleParam ρ)) := by
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
  have heqfun : (fun s : ℂ => -logDeriv ZD.riemannXi s)
      = (xiChannel ∘ fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    funext s
    simp only [Function.comp_apply, xiChannel, key]
  rw [heqfun]
  exact hcomp

/-! ## §2 Regularity everywhere else -/

/-- **Regularity off the zeros**: at any spectral parameter whose line point is not a
nontrivial zero, the ξ-channel has a finite limit (its value; the channel is continuous
there).  ξ is entire and — unlike the finite `L` or `Λ` — has no other singularity to
contribute: no trivial zeros, no pole at `s = 0, 1`. -/
theorem xiChannel_regular {z₀ : ℂ} (hz : (1 / 2 + Complex.I * z₀) ∉ ZD.NontrivialZeros) :
    ∃ L, Tendsto xiChannel (𝓝[≠] z₀) (𝓝 L) := by
  set s₀ : ℂ := 1 / 2 + Complex.I * z₀ with hs₀
  have hξ : ZD.riemannXi s₀ ≠ 0 := fun h => hz ((ZD.riemannXi_eq_zero_iff s₀).mp h)
  have hlog : ContinuousAt (fun s => -logDeriv ZD.riemannXi s) s₀ := by
    have hder : ContinuousAt (deriv ZD.riemannXi) s₀ :=
      ((ZD.riemannXi_differentiable.analyticAt s₀).deriv).continuousAt
    have hcont : ContinuousAt ZD.riemannXi s₀ :=
      ZD.riemannXi_differentiable.continuous.continuousAt
    have hdiv : ContinuousAt (fun s => deriv ZD.riemannXi s / ZD.riemannXi s) s₀ :=
      hder.div hcont hξ
    have heq : (fun s => -logDeriv ZD.riemannXi s)
        = fun s => -(deriv ZD.riemannXi s / ZD.riemannXi s) := by
      funext s
      rw [logDeriv_apply]
    rw [heq]
    exact hdiv.neg
  have haff : Tendsto (fun z : ℂ => 1 / 2 + Complex.I * z) (𝓝[≠] z₀) (𝓝 s₀) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have hc : Continuous (fun z : ℂ => 1 / 2 + Complex.I * z) := by fun_prop
    exact hc.tendsto z₀
  exact ⟨-logDeriv ZD.riemannXi s₀, hlog.tendsto.comp haff⟩

/-! ## §3 The equivalence: RH = regularity off the reals -/

/-- Mathlib's `RiemannHypothesis` places every member of `NontrivialZeros` on the line. -/
theorem rh_implies_line (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) : ρ.re = 1 / 2 := by
  refine hRH ρ hρ.2.2 ?_ ?_
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    have hcalc : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      simp [Complex.mul_re]
    rw [hcalc] at hre
    have h0 := hρ.1
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  · intro h1
    have := hρ.2.1
    rw [h1, Complex.one_re] at this
    exact lt_irrefl _ this

/-- The spectral parameter of a zero is off the reals exactly when the zero is off the
line: `(poleParam ρ).im = ½ − ρ.re`. -/
theorem poleParam_im (ρ : ℂ) : (poleParam ρ).im = 1 / 2 - ρ.re := by
  simp [poleParam]

/-- **The equivalence (D3)**: Mathlib's `RiemannHypothesis` holds **iff** the ξ-channel is
regular off the real axis.  A sourceless zero *is* a non-real resonance of the channel;
`hReg` — the dangerous hypothesis — is precisely the right-hand side. -/
theorem xiChannel_offReal_regular_iff_RH :
    (∀ z : ℂ, z.im ≠ 0 → ∃ L, Tendsto xiChannel (𝓝[≠] z) (𝓝 L)) ↔ RiemannHypothesis := by
  constructor
  · intro hreg
    refine RHBridge.no_offline_zeros_implies_rh ?_
    intro ρ hρ
    by_contra hne
    refine xiChannel_resonates hρ (hreg (poleParam ρ) ?_)
    rw [poleParam_im]
    intro h
    exact hne (by linarith)
  · intro hRH z hz
    refine xiChannel_regular ?_
    intro hmem
    have hre := rh_implies_line hRH hmem
    have him : (1 / 2 + Complex.I * z).re = 1 / 2 - z.im := by
      simp [Complex.add_re, Complex.mul_re]
      ring
    rw [him] at hre
    exact hz (by linarith)

/-! ## §4 The self-adjoint capstone for ζ -/

/-- **RH from a self-adjoint ξ-channel receiver.**  If any self-adjoint element of any
C*-algebra receives the ξ-channel — the channel is regular off its spectrum — then
`RiemannHypothesis` holds: self-adjoint spectra are real (von Neumann reality), so
regularity off the spectrum gives regularity off the reals, and the equivalence closes.
Unconditional; the single remaining input is the receiver hypothesis `hReg` — the
operator form of *every zero has a source*. -/
theorem RiemannHypothesis_of_selfAdjoint_xiChannel_receiver
    {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a)
    (hReg : ∀ z, z ∉ spectrum ℂ a → ∃ L, Tendsto xiChannel (𝓝[≠] z) (𝓝 L)) :
    RiemannHypothesis := by
  refine xiChannel_offReal_regular_iff_RH.mp (fun z hz => hReg z fun hmem => hz ?_)
  exact ha.im_eq_zero_of_mem_spectrum hmem

/-! ## §5 The real section: the wave at the perpendicular

The crossing formulation's type-theoretic half: restricted to real spectral parameters, the
ξ-section is **real-valued** — the 3-D helix seen down the collapse axis reads as a real 1-D
wave, so "the fiber experiences a sign change" is well-typed exactly on the axis.  From
`HelixCollapse.completedRiemannZeta_critical_line_real` (Schwarz reflection + FE) plus the
reality of the polynomial dressing on the line. -/

/-- The ξ-section in the spectral chart: `Ξ(z) = ξ(½ + iz)`. -/
noncomputable def xiSection (z : ℂ) : ℂ := ZD.riemannXi (1 / 2 + Complex.I * z)

/-- **The section is real on the axis**: for real `t`, `Ξ(t) ∈ ℝ`.  The polynomial factor
`s(s−1)/2` equals `−(¼+t²)/2` on the line (real), and `Λ` is real there by Schwarz + FE. -/
theorem xiSection_real (t : ℝ) : (xiSection t).im = 0 := by
  have hs0 : (1 / 2 + Complex.I * (t : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hs1 : (1 / 2 + Complex.I * (t : ℂ)) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hxi := ZD.riemannXi_eq_classical_of_ne_zero_of_ne_one _ hs0 hs1
  rw [xiSection, hxi]
  have hpoly : ((1 / 2 + Complex.I * (t : ℂ)) * ((1 / 2 + Complex.I * (t : ℂ)) - 1) / 2)
      = Complex.ofReal (-(1 / 4 + t ^ 2) / 2) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hΛ : (completedRiemannZeta (1 / 2 + Complex.I * (t : ℂ))).im = 0 := by
    have h := HelixCollapse.completedRiemannZeta_critical_line_im_zero t
    have harg : (1 / 2 + Complex.I * (t : ℂ)) = 1 / 2 + (t : ℂ) * Complex.I := by ring
    rwa [harg]
  rw [hpoly, Complex.mul_im, Complex.ofReal_im, hΛ]
  ring

/-- **Crossings are axis-bound by type**: the section is real exactly where a "sign change"
is a well-typed notion, and its vanishing at a real parameter is an event of the ledger
(`riemannXi_eq_zero_iff` + the line chart).  Off the axis the section is irreducibly
complex-valued — a null there would be a crossingless winding, the configuration the
carrier does not support. -/
theorem xiSection_zero_iff_event (t : ℝ) :
    xiSection t = 0 ↔ (1 / 2 + Complex.I * (t : ℂ)) ∈ ZD.NontrivialZeros := by
  rw [xiSection]
  exact ZD.riemannXi_eq_zero_iff _

end CriticalLinePhasor.XiChannel
