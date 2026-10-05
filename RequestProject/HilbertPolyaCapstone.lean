import RequestProject.HilbertPolyaResolventTrace
import RequestProject.HelixResolventCapture
import RequestProject.XiHadamardQuotient

/-!
# The Hilbert–Pólya capstone: the real spectral operator forces the line

The correspondence the corpus deliberately left unasserted, now asserted as a door.
The ξ spectral trace
`T(z) = −(ξ'/ξ)(½ + iz)` is the boundary readout of the spectral chart; by
the compiled resolvent trace identity (`hilbertPolya_resolvent_trace`) it is
the two-point resolvent sum of the multiplicity ledger.  This file compiles:

* `xi_spectralCoord_mem_singularSupport` — every nontrivial zero's spectral
  coordinate is an absorption resonance of the trace (multiplicity ≥ 1
  forces the pole; no finite limit exists there);
* `rh_of_selfAdjointReceiver_xi` — **the capstone**: if the trace is the
  readout of the real spectral channel (`IsSelfAdjointReceiver`: regular
  off `ℝ`, the earned reality of a self-adjoint operator — supplied
  unconditionally by any bounded self-adjoint realization via
  `isSelfAdjointReceiver_resolventReadout`), every nontrivial zero has
  `Re ρ = ½`;
* `rh_of_selfAdjoint_resolventReadout_xi` — the operator form: a bounded
  self-adjoint element with continuous readout equal to the ξ spectral
  trace forces the Riemann Hypothesis outright.

No `axiom`, no `sorry`.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.HilbertPolya

open HelixLimit

/-- The ξ spectral trace: the completed logarithmic derivative read on the
spectral chart `s = ½ + iz`. -/
noncomputable def xiSpectralTrace (z : ℂ) : ℂ :=
  -logDeriv ZD.riemannXi (1 / 2 + Complex.I * z)

/-- At a nontrivial zero, the completed logarithmic derivative has no finite
limit: the pole carries the multiplicity. -/
theorem xi_logDeriv_not_tendsto {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ¬ ∃ L, Tendsto (logDeriv ZD.riemannXi) (𝓝[≠] ρ) (𝓝 L) := by
  rintro ⟨L, hL⟩
  have han : AnalyticAt ℂ ZD.riemannXi ρ :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ ρ (Set.mem_univ _)
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere ρ
  have hm : analyticOrderAt ZD.riemannXi ρ = (ZD.xiOrderNat ρ : ℕ∞) := by
    rw [ZD.xiOrderNat, analyticOrderNatAt]
    exact (ENat.coe_toNat hne).symm
  have hres := CriticalLinePhasor.ResidueJump.logDeriv_residue_eq_order han hm
  have hzero : Tendsto (fun s => (s - ρ) * logDeriv ZD.riemannXi s)
      (𝓝[≠] ρ) (𝓝 (0 * L)) := by
    apply Tendsto.mul _ hL
    have hc : Continuous fun s : ℂ => s - ρ := by continuity
    have := hc.tendsto ρ
    simp only [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [zero_mul] at hzero
  have huniq := tendsto_nhds_unique hres hzero
  have hpos := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ
  have hne0 : (ZD.xiOrderNat ρ : ℂ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  exact hne0 huniq

/-- **Resonance**: every nontrivial zero's spectral coordinate lies in the
singular support of the ξ spectral trace. -/
theorem xi_spectralCoord_mem_singularSupport {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) :
    spectralCoord ρ ∈ SingularSupport xiSpectralTrace := by
  intro hEx
  obtain ⟨L, hL⟩ := hEx
  apply xi_logDeriv_not_tendsto hρ
  refine ⟨-L, ?_⟩
  have key : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s :=
    fun s => by linear_combination (-(s - 1 / 2)) * Complex.I_mul_I
  have hcont : Tendsto (fun s : ℂ => -Complex.I * (s - 1 / 2)) (𝓝[≠] ρ)
      (𝓝[≠] (spectralCoord ρ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have hc : Continuous fun s : ℂ => -Complex.I * (s - 1 / 2) := by continuity
      exact hc.tendsto ρ
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro hc
      have h3 : -Complex.I * ((s - 1 / 2) - (ρ - 1 / 2)) = 0 := by
        rw [spectralCoord] at hc
        linear_combination hc
      have h4 : (s - 1 / 2) - (ρ - 1 / 2) = 0 :=
        (mul_eq_zero.mp h3).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
      exact hs (by linear_combination h4)
  have hcomp := hL.comp hcont
  have heqfun : logDeriv ZD.riemannXi
      = fun s => -(xiSpectralTrace (-Complex.I * (s - 1 / 2))) := by
    funext s
    simp only [xiSpectralTrace, key s, neg_neg]
  rw [heqfun]
  simpa [Function.comp] using hcomp.neg

/-- **What `IsSelfAdjointReceiver` actually says, under a name that cannot mislead.**
`ResonatesOnlyOnRealAxis T` is a property of a READOUT FUNCTION `T : ℂ → ℂ`: it has a finite
limit at every non-real point, so its resonances (poles) lie on `ℝ`.  It is not a statement
about an operator.  Every self-adjoint operator's resolvent readout has this property
unconditionally (`isSelfAdjointReceiver_resolventReadout`); whether a GIVEN readout, such as
the ξ spectral trace, has it is a question about that readout's poles. -/
abbrev ResonatesOnlyOnRealAxis (T : ℂ → ℂ) : Prop := IsSelfAdjointReceiver T

/-- The operator side, restated: self-adjointness is unconditional and so is the regularity
of the readout off `ℝ`.  Nothing here depends on the location of any zero. -/
theorem selfAdjoint_readout_resonatesOnlyOnRealAxis
    {A : Type*} [CStarAlgebra A] [StarModule ℂ A] {a : A} (ha : IsSelfAdjoint a)
    {φ : A → ℂ} (hφ : Continuous φ) :
    ResonatesOnlyOnRealAxis (fun z => φ (resolvent a z)) :=
  isSelfAdjointReceiver_resolventReadout ha hφ

/-- **The Hilbert–Pólya capstone.**  If the ξ spectral trace resonates only on the real axis
(`IsSelfAdjointReceiver` = `ResonatesOnlyOnRealAxis`, a property of the trace, never an
assumption about an operator), then every nontrivial zero lies on the critical line. -/
theorem rh_of_selfAdjointReceiver_xi
    (hsa : IsSelfAdjointReceiver xiSpectralTrace) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  have hmem := xi_spectralCoord_mem_singularSupport hρ
  have him := real_absorption_of_selfAdjoint hsa _ hmem
  have hcalc : (spectralCoord ρ).im = -(ρ.re - 1 / 2) := by
    simp [spectralCoord, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  rw [hcalc] at him
  linarith

/-- **The operator form.**  A bounded self-adjoint element of any
C⋆-algebra, with any continuous readout whose resolvent trace equals the ξ
spectral trace, forces the Riemann Hypothesis: reality is earned from
self-adjointness (`spectrum ⊆ ℝ` + resolvent regularity are theorems), and
the resonances carry the zeros into that real spectrum. -/
theorem rh_of_selfAdjoint_resolventReadout_xi
    {A : Type*} [CStarAlgebra A] {a : A}
    (ha : IsSelfAdjoint a) {φ : A → ℂ} (hφ : Continuous φ)
    (hid : ∀ z, φ (resolvent a z) = xiSpectralTrace z) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  apply rh_of_selfAdjointReceiver_xi
  have h := isSelfAdjointReceiver_resolventReadout ha hφ
  intro z hz
  obtain ⟨L, hL⟩ := h z hz
  exact ⟨L, hL.congr' (by filter_upwards with w using hid w)⟩

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.xi_spectralCoord_mem_singularSupport
#print axioms CriticalLinePhasor.HilbertPolya.rh_of_selfAdjointReceiver_xi
#print axioms CriticalLinePhasor.HilbertPolya.rh_of_selfAdjoint_resolventReadout_xi
#print axioms CriticalLinePhasor.HilbertPolya.selfAdjoint_readout_resonatesOnlyOnRealAxis
