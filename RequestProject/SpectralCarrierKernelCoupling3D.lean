import RequestProject.SpectralZeroKernel
import RequestProject.ThreeDFocalEvent

/-!
# Parameter-preserving coupling of the analytic zero kernel to the ambient 3D carrier

The scalar configured operator `SpectralFiber.specOp χ s` detects vanishing of the full analytic
`L`-function at `s`.  The independently defined `ThreeDFocal.carrierThreeDOperator` records the
real logarithmic ordinate of every geometric carrier state.  This file couples the two operators
only when they refer to the same analytic point.

The coupling retains, in one object:

* the completed focal event at a positive physical height;
* the equality of its carrier readout with the original analytic parameter;
* the canonical nonzero kernel vector of the configured analytic operator;
* the canonical nonzero eigenvector of the event-independent ambient 3D operator; and
* the kernel vector of the self-adjoint one-mode resolvent at the same parameter.

No operator is defined from an event certificate: the certificate only selects basis states in
operators that were already defined on their ambient spaces.
-/

open Complex

namespace CriticalLinePhasor.SpectralCarrierCoupling

open CriticalLinePhasor
open CriticalLinePhasor.SpectralFiber
open CriticalLinePhasor.SelfAdjointGenerator
open CriticalLinePhasor.ThreeDFocal
open CriticalLinePhasor.UnconditionalFrobenius

variable {q : ℕ} [NeZero q]

/-- A single analytic zero kernel and its parameter-preserving realization on the ambient 3D
carrier.  The pitch and radius parameters belong only to the independently defined geometric
carrier; the completed event itself is character-indexed. -/
structure SpectralCarrierKernelCoupling3D
    (χ : DirichletCharacter ℂ q) (p r : ℝ) (s : ℂ) where
  event : CompletedThreeDEigenEvent χ
  analyticPoint : carrierPointAtHeight event.1 = s
  readout_kernel : SpectralFiber.specOp χ s (1 : ℂ) = 0
  ambient_nonzero : Finsupp.single (event.toCarrierState p r) (1 : ℂ) ≠ 0
  ambient_eigenvector :
    carrierThreeDOperator p r (Finsupp.single (event.toCarrierState p r) (1 : ℂ)) =
      (Real.log event.1 : ℂ) • Finsupp.single (event.toCarrierState p r) (1 : ℂ)
  selfAdjoint_resolvent_kernel :
    ∃ ψ : ℂ, ψ ≠ 0 ∧
      SelfAdjointGenerator.specOp (vonNeumannOp (Real.log event.1)) s ψ = 0

/-- A completed focal event canonically couples its analytic `L`-kernel, ambient 3D eigenvector,
and self-adjoint one-mode resolvent kernel at the same represented point. -/
noncomputable def ofCompletedEvent
    (χ : DirichletCharacter ℂ q) (p r : ℝ) (e : CompletedThreeDEigenEvent χ) :
    SpectralCarrierKernelCoupling3D χ p r (carrierPointAtHeight e.1) := by
  have hL : Lspec χ (carrierPointAtHeight e.1) = 0 :=
    completedThreeDEigenEvent_L_zero χ e
  have hambient := carrierThreeDOperator_completedEvent_eigenvector p r e
  refine ⟨e, rfl, ?_, hambient.1, hambient.2, ?_⟩
  · rw [SpectralFiber.specOp_apply, hL, zero_mul]
  · change ∃ ψ : ℂ, ψ ≠ 0 ∧
      SelfAdjointGenerator.specOp (vonNeumannOp (Real.log e.1))
        (carrierPoint (Real.log e.1)) ψ = 0
    exact carrier_kernel_realized (Real.log e.1)

/-- Height form of the construction: a zero of the full analytic spectral function at the
carrier readout produces the completed focal event and both operator realizations. -/
noncomputable def ofLspecZeroAtHeight
    (χ : DirichletCharacter ℂ q) (p r Z : ℝ) (hZ : 0 < Z)
    (hzero : Lspec χ (carrierPointAtHeight Z) = 0) :
    SpectralCarrierKernelCoupling3D χ p r (carrierPointAtHeight Z) := by
  let e : CompletedThreeDEigenEvent χ :=
    ⟨Z, (completedThreeDZeroAtHeight_iff_L_zero χ Z hZ).2 hzero⟩
  simpa [e] using ofCompletedEvent χ p r e

/-- Any coupled object returns the original full analytic zero; the 3D realization therefore
cannot manufacture a cancellation absent from the configured analytic operator. -/
theorem lspec_zero_of_coupling
    {χ : DirichletCharacter ℂ q} {p r : ℝ} {s : ℂ}
    (C : SpectralCarrierKernelCoupling3D χ p r s) :
    Lspec χ s = 0 :=
  (spectral_kernel_iff_zero χ s).1 ⟨1, one_ne_zero, C.readout_kernel⟩

/-- Any coupled parameter is the readout of a real carrier height, hence its real coordinate is
the area-law carrier abscissa. -/
theorem re_eq_carrierAbscissa_of_coupling
    {χ : DirichletCharacter ℂ q} {p r : ℝ} {s : ℂ}
    (C : SpectralCarrierKernelCoupling3D χ p r s) :
    s.re = carrierAbscissa := by
  rw [← C.analyticPoint, carrierPointAtHeight_re]

/-- Canonical parameter-preserving construction from an analytic zero already represented by the
carrier coordinate.  The witness height is derived as `exp (Im s)`. -/
noncomputable def ofLspecZeroOfReEqCarrierAbscissa
    (χ : DirichletCharacter ℂ q) (p r : ℝ) (s : ℂ)
    (hzero : Lspec χ s = 0) (hre : s.re = carrierAbscissa) :
    SpectralCarrierKernelCoupling3D χ p r s := by
  have hpoint : carrierPointAtHeight (Real.exp s.im) = s := by
    rw [carrierPointAtHeight_exp]
    apply Complex.ext
    · simpa [carrierPoint, carrierAbscissa] using hre.symm
    · simp [carrierPoint]
  have hzero' : Lspec χ (carrierPointAtHeight (Real.exp s.im)) = 0 := by
    rw [hpoint]
    exact hzero
  simpa [hpoint] using
    ofLspecZeroAtHeight χ p r (Real.exp s.im) (Real.exp_pos s.im) hzero'

/-- Geometric construction from analytic vanishing and zero radial drift.  The carrier abscissa
is not supplied to this constructor: it is derived from the area-law/no-drift theorem. -/
noncomputable def ofLspecZeroOfNoRadialDrift
    (χ : DirichletCharacter ℂ q) (p r n : ℝ) (s : ℂ) (hn : 1 < n)
    (hzero : Lspec χ s = 0)
    (hnoDrift : n ^ (s.re - carrierAbscissa) = 1) :
    SpectralCarrierKernelCoupling3D χ p r s :=
  ofLspecZeroOfReEqCarrierAbscissa χ p r s hzero
    ((noRadialDrift_iff_carrierAbscissa n s.re hn).1 hnoDrift)

/-- Independent binary-base reconstruction of the preceding constructor.  It first derives the
area-law coordinate from no drift, then constructs the positive physical height
`Z = exp (Im s)` and invokes the height-form coupling. -/
noncomputable def ofLspecZeroOfBinaryNoRadialDrift
    (χ : DirichletCharacter ℂ q) (p r : ℝ) (s : ℂ)
    (hzero : Lspec χ s = 0)
    (hnoDrift : (2 : ℝ) ^ (s.re - carrierAbscissa) = 1) :
    SpectralCarrierKernelCoupling3D χ p r s := by
  have hre : s.re = carrierAbscissa :=
    (noRadialDrift_iff_carrierAbscissa 2 s.re (by norm_num)).1 hnoDrift
  have hpoint : carrierPointAtHeight (Real.exp s.im) = s := by
    rw [carrierPointAtHeight_exp]
    apply Complex.ext
    · simpa [carrierPoint, carrierAbscissa] using hre.symm
    · simp [carrierPoint]
  have hzero' : Lspec χ (carrierPointAtHeight (Real.exp s.im)) = 0 := by
    simpa [hpoint] using hzero
  simpa [hpoint] using
    ofLspecZeroAtHeight χ p r (Real.exp s.im) (Real.exp_pos s.im) hzero'

/-- Exact kernel-to-carrier identification.  Existence of the parameter-preserving 3D coupling is
equivalent to analytic vanishing together with membership in the derived carrier coordinate. -/
theorem nonempty_coupling_iff
    (χ : DirichletCharacter ℂ q) (p r : ℝ) (s : ℂ) :
    Nonempty (SpectralCarrierKernelCoupling3D χ p r s) ↔
      Lspec χ s = 0 ∧ s.re = carrierAbscissa := by
  constructor
  · rintro ⟨C⟩
    exact ⟨lspec_zero_of_coupling C, re_eq_carrierAbscissa_of_coupling C⟩
  · rintro ⟨hzero, hre⟩
    exact ⟨ofLspecZeroOfReEqCarrierAbscissa χ p r s hzero hre⟩

/-- The same identification stated using the configured analytic operator's nonzero-kernel
predicate rather than its determinant value. -/
theorem nonempty_coupling_iff_readoutKernel
    (χ : DirichletCharacter ℂ q) (p r : ℝ) (s : ℂ) :
    Nonempty (SpectralCarrierKernelCoupling3D χ p r s) ↔
      (∃ ψ : ℂ, ψ ≠ 0 ∧ SpectralFiber.specOp χ s ψ = 0) ∧
        s.re = carrierAbscissa := by
  rw [nonempty_coupling_iff, spectral_kernel_iff_zero]

/-- Operator identification with no midpoint in the input: a coupling exists exactly when the
analytic operator vanishes and its radial projection has zero drift.  The displayed carrier
coordinate is generated internally by the area-law theorem. -/
theorem nonempty_coupling_iff_zero_and_noRadialDrift
    (χ : DirichletCharacter ℂ q) (p r n : ℝ) (s : ℂ) (hn : 1 < n) :
    Nonempty (SpectralCarrierKernelCoupling3D χ p r s) ↔
      Lspec χ s = 0 ∧ n ^ (s.re - carrierAbscissa) = 1 := by
  rw [nonempty_coupling_iff, noRadialDrift_iff_carrierAbscissa n s.re hn]

/-- For an actual analytic zero, failure of the parameter-preserving 3D coupling forces
nontrivial radial drift at every base greater than one. -/
theorem radialDrift_of_lspecZero_of_noCoupling
    (χ : DirichletCharacter ℂ q) (p r n : ℝ) (s : ℂ) (hn : 1 < n)
    (hzero : Lspec χ s = 0)
    (hnoCoupling : ¬ Nonempty (SpectralCarrierKernelCoupling3D χ p r s)) :
    n ^ (s.re - carrierAbscissa) ≠ 1 := by
  intro hnoDrift
  exact hnoCoupling
    ((nonempty_coupling_iff_zero_and_noRadialDrift χ p r n s hn).2
      ⟨hzero, hnoDrift⟩)

end CriticalLinePhasor.SpectralCarrierCoupling

#print axioms CriticalLinePhasor.SpectralCarrierCoupling.ofCompletedEvent
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.ofLspecZeroAtHeight
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.ofLspecZeroOfNoRadialDrift
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.ofLspecZeroOfBinaryNoRadialDrift
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.lspec_zero_of_coupling
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.nonempty_coupling_iff
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.nonempty_coupling_iff_readoutKernel
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.nonempty_coupling_iff_zero_and_noRadialDrift
#print axioms CriticalLinePhasor.SpectralCarrierCoupling.radialDrift_of_lspecZero_of_noCoupling
