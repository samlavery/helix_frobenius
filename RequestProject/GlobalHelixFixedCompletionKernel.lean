import RequestProject.GlobalHelixCoefficientFiber

/-!
# Fixed archimedean completion clocks on the global 3D carrier

The completion kernel is specified only by its archimedean parameters.  It is independent of the
coefficient bank.  Each single clock is `2 x^μ exp (-2πx)` and multiple clocks are assembled by
multiplicative Mellin convolution.  The resulting fixed kernel is then read at the signed-log height
of the global 3D carrier.
-/

open Complex Set MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection CriticalLinePhasor.CarrierTheta

/-- One fixed archimedean Gamma clock. -/
noncomputable def gammaClock (μ : ℂ) (x : ℝ) : ℂ :=
  2 * (x : ℂ) ^ μ * Complex.exp (-(2 * Real.pi : ℂ) * x)

/-- Multiplicative convolution, with Haar measure `dy / y` on the positive real axis. -/
noncomputable def mellinConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Ioi 0, f y * g (x / y) / (y : ℂ)

/-- The closed two-clock kernel before rewriting it as a Bessel function. -/
noncomputable def twoClockKernel (μa μb : ℂ) : ℝ → ℂ :=
  mellinConvolution (gammaClock μa) (gammaClock μb)

/-- A nonempty list of archimedean parameters assembles a fixed completion kernel by iterated
multiplicative convolution.  The empty list carries no completion clock and is represented by zero;
all applications below use a nonempty parameter list. -/
noncomputable def completionKernel : List ℂ → ℝ → ℂ
  | [] => fun _ => 0
  | [μ] => gammaClock μ
  | μ :: ν :: rest => mellinConvolution (gammaClock μ) (completionKernel (ν :: rest))

theorem completionKernel_singleton (μ : ℂ) :
    completionKernel [μ] = gammaClock μ := by
  rfl

theorem completionKernel_pair (μa μb : ℂ) :
    completionKernel [μa, μb] = twoClockKernel μa μb := by
  rfl

/-- Read a fixed completion kernel from the multiplicative height of a 3D carrier point. -/
noncomputable def fixedKernelReadout (μ : List ℂ) (f : Fiber) : ℂ :=
  completionKernel μ (multiplicativeHeight f)

/-- The fixed kernel readout ignores the radial and phase coordinates; those coordinates retain the
coefficient phasor without changing the completion clock. -/
theorem fixedKernelReadout_eq (μ : List ℂ) (f : Fiber) :
    fixedKernelReadout μ f = completionKernel μ (multiplicativeHeight f) := by
  rfl

/-- Exact source attribution for one reciprocal-height term using the prescribed, coefficient-
independent completion kernel. -/
theorem fixedCompletionTerm_as_transformedDualFiber
    (μ : List ℂ) (a : ℕ → ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    a n * completionKernel μ (((n + 1 : ℕ) : ℝ) / x) =
      fiberPhasor
          (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x) *
        fixedKernelReadout μ
          (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x) := by
  rw [fiberPhasor_reciprocalCoefficientFiber_conj, fixedKernelReadout,
    multiplicativeHeight_reciprocalCoefficientFiber _ n hx]

/-- The full reciprocal theta for the fixed completion kernel is the 1D readout of the transformed
dual coefficient bank on the global 3D carrier. -/
theorem fixedCompletionTheta_one_div_as_globalHelix
    (μ : List ℂ) (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) :
    theta a (completionKernel μ) (1 / x) =
      ∑' n : ℕ,
        fiberPhasor
            (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x) *
          fixedKernelReadout μ
            (reciprocalCoefficientFiber (fun m => (starRingEnd ℂ) (a m)) n x) := by
  simpa [fixedKernelReadout] using
    theta_one_div_as_transformedDualFibers a (completionKernel μ) hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.completionKernel_singleton
#print axioms CriticalLinePhasor.GlobalHelix.completionKernel_pair
#print axioms CriticalLinePhasor.GlobalHelix.fixedKernelReadout_eq
#print axioms CriticalLinePhasor.GlobalHelix.fixedCompletionTerm_as_transformedDualFiber
#print axioms CriticalLinePhasor.GlobalHelix.fixedCompletionTheta_one_div_as_globalHelix
