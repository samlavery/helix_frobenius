import RequestProject.GlobalHelixFiniteEulerBank
import RequestProject.GlobalHelixFixedCompletionKernel

/-!
# Arbitrary-height fixed-kernel banks on the global 3D helix

The natural-number ledger is replaced by a native index type `I` and a positive multiplicative
height map `h : I → ℝ`.  A coefficient is first stored as the 3D point
`(‖aᵢ‖, arg aᵢ, log (hᵢx))`.  The global helix involution followed by the exact shear `hᵢ²` sends
its height to `hᵢ/x`.  Only after this 3D transport is the coefficient-independent completion
kernel read out.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- A coefficient at an arbitrary positive multiplicative height, stored on the 3D carrier. -/
noncomputable def indexedCoefficientFiber
    {I : Type*} (a : I → ℂ) (h : I → ℝ) (i : I) (x : ℝ) : Fiber :=
  (‖a i‖, Complex.arg (a i), Real.log (h i * x))

/-- The radial/phase coordinates reconstruct the indexed coefficient. -/
theorem fiberPhasor_indexedCoefficientFiber
    {I : Type*} (a : I → ℂ) (h : I → ℝ) (i : I) (x : ℝ) :
    fiberPhasor (indexedCoefficientFiber a h i x) = a i := by
  simpa [fiberPhasor, indexedCoefficientFiber, radial, phase, mul_comm] using
    Complex.norm_mul_exp_arg_mul_I (a i)

/-- The third coordinate reconstructs the indexed multiplicative height. -/
theorem multiplicativeHeight_indexedCoefficientFiber
    {I : Type*} (a : I → ℂ) (h : I → ℝ) (hh : ∀ i, 0 < h i)
    (i : I) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (indexedCoefficientFiber a h i x) = h i * x := by
  unfold multiplicativeHeight heightEncode indexedCoefficientFiber height
  rw [Real.exp_log]
  exact mul_pos (hh i) hx

/-- Apply the global helix involution and then the exact index-height shear `hᵢ²`. -/
noncomputable def indexedReciprocalCoefficientFiber
    {I : Type*} (aDual : I → ℂ) (h : I → ℝ) (i : I) (x : ℝ) : Fiber :=
  heightShear ((h i) ^ 2)
    (globalHelixInvolution (indexedCoefficientFiber aDual h i x))

/-- Conjugate dual data becomes the primal coefficient after the global involution. -/
theorem fiberPhasor_indexedReciprocalCoefficientFiber_conj
    {I : Type*} (a : I → ℂ) (h : I → ℝ) (i : I) (x : ℝ) :
    fiberPhasor
      (indexedReciprocalCoefficientFiber (fun j => (starRingEnd ℂ) (a j)) h i x) =
        a i := by
  rw [indexedReciprocalCoefficientFiber, fiberPhasor_heightShear,
    fiberPhasor_globalHelixInvolution, fiberPhasor_indexedCoefficientFiber]
  simp

/-- The sheared anti-helix point has reciprocal external height `hᵢ/x`. -/
theorem multiplicativeHeight_indexedReciprocalCoefficientFiber
    {I : Type*} (aDual : I → ℂ) (h : I → ℝ) (hh : ∀ i, 0 < h i)
    (i : I) {x : ℝ} (hx : 0 < x) :
    multiplicativeHeight (indexedReciprocalCoefficientFiber aDual h i x) =
      h i / x := by
  rw [indexedReciprocalCoefficientFiber,
    multiplicativeHeight_heightShear (sq_pos_of_pos (hh i)),
    multiplicativeHeight_globalHelixInvolution,
    multiplicativeHeight_indexedCoefficientFiber aDual h hh i hx]
  have hi0 : h i ≠ 0 := ne_of_gt (hh i)
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp

/-- The scalar theta readout attached to arbitrary indexed heights. -/
noncomputable def indexedTheta
    {I : Type*} (a : I → ℂ) (h : I → ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' i : I, a i * g (h i * x)

/-- The primal fixed-completion bank, defined directly from its 3D source points. -/
noncomputable def indexedFixedPrimalBankReadout
    {I : Type*} (μ : List ℂ) (a : I → ℂ) (h : I → ℝ) (x : ℝ) : ℂ :=
  ∑' i : I,
    fiberPhasor (indexedCoefficientFiber a h i x) *
      fixedKernelReadout μ (indexedCoefficientFiber a h i x)

/-- The transformed dual fixed-completion bank on the sheared anti-helix. -/
noncomputable def indexedFixedTransformedDualBankReadout
    {I : Type*} (μ : List ℂ) (aDual : I → ℂ) (h : I → ℝ) (x : ℝ) : ℂ :=
  ∑' i : I,
    fiberPhasor (indexedReciprocalCoefficientFiber aDual h i x) *
      fixedKernelReadout μ (indexedReciprocalCoefficientFiber aDual h i x)

/-- Projection of the primal 3D bank is the arbitrary-height coefficient theta. -/
theorem indexedFixedPrimalBankReadout_eq_theta
    {I : Type*} (μ : List ℂ) (a : I → ℂ) (h : I → ℝ)
    (hh : ∀ i, 0 < h i) {x : ℝ} (hx : 0 < x) :
    indexedFixedPrimalBankReadout μ a h x =
      indexedTheta a h (completionKernel μ) x := by
  unfold indexedFixedPrimalBankReadout indexedTheta fixedKernelReadout
  apply tsum_congr
  intro i
  rw [fiberPhasor_indexedCoefficientFiber,
    multiplicativeHeight_indexedCoefficientFiber a h hh i hx]

/-- Projection of the transformed conjugate-dual bank is theta at reciprocal external height. -/
theorem indexedFixedTransformedConjugateDualBankReadout_eq_theta_one_div
    {I : Type*} (μ : List ℂ) (a : I → ℂ) (h : I → ℝ)
    (hh : ∀ i, 0 < h i) {x : ℝ} (hx : 0 < x) :
    indexedFixedTransformedDualBankReadout μ
        (fun i => (starRingEnd ℂ) (a i)) h x =
      indexedTheta a h (completionKernel μ) (1 / x) := by
  unfold indexedFixedTransformedDualBankReadout indexedTheta fixedKernelReadout
  apply tsum_congr
  intro i
  rw [fiberPhasor_indexedReciprocalCoefficientFiber_conj,
    multiplicativeHeight_indexedReciprocalCoefficientFiber _ h hh i hx]
  congr 2
  ring

/-- The arbitrary-height 3D odd reflection channel. -/
noncomputable def indexedFixedBankOddChannel
    {I : Type*} (μ : List ℂ) (a : I → ℂ) (h : I → ℝ)
    (η : ℂ) (κ : ℝ) (x : ℝ) : ℂ :=
  indexedFixedPrimalBankReadout μ a h x -
    (η * (x ^ κ : ℝ)) •
      indexedFixedTransformedDualBankReadout μ
        (fun i => (starRingEnd ℂ) (a i)) h x

/-- Vanishing of the 3D odd channel is exactly reflection of the fixed-kernel scalar projection. -/
theorem indexedFixedBankOddChannel_eq_zero_iff_theta_reflection
    {I : Type*} (μ : List ℂ) (a : I → ℂ) (h : I → ℝ)
    (hh : ∀ i, 0 < h i) (η : ℂ) (κ : ℝ) {x : ℝ} (hx : 0 < x) :
    indexedFixedBankOddChannel μ a h η κ x = 0 ↔
      indexedTheta a h (completionKernel μ) x =
        (η * (x ^ κ : ℝ)) •
          indexedTheta a h (completionKernel μ) (1 / x) := by
  rw [indexedFixedBankOddChannel,
    indexedFixedPrimalBankReadout_eq_theta μ a h hh hx,
    indexedFixedTransformedConjugateDualBankReadout_eq_theta_one_div μ a h hh hx]
  exact sub_eq_zero

/-- The finite tensor-Euler bank with the fixed completion kernel is definitionally the indexed
3D primal bank with exponent-vector coefficient and height. -/
theorem finiteTensorEulerBankReadout_completionKernel_eq_indexedFixedPrimal
    {V ι : Type*} [Fintype V] [Fintype ι]
    (μ : List ℂ) (S : Finset V) (W : V → FiniteWeightFiber ι)
    (q : V → ℝ) (x : ℝ) :
    finiteTensorEulerBankReadout S W q (completionKernel μ) x =
      indexedFixedPrimalBankReadout μ
        (finiteEulerCoeff S W) (finiteEulerHeight S q) x := by
  unfold finiteTensorEulerBankReadout indexedFixedPrimalBankReadout
  apply tsum_congr
  intro k
  rfl

/-- The fixed-kernel odd channel of the finite global tensor-Euler source. -/
noncomputable def finiteEulerFixedBankOddChannel
    {V ι : Type*} [Fintype V] [Fintype ι]
    (μ : List ℂ) (S : Finset V) (W : V → FiniteWeightFiber ι)
    (q : V → ℝ) (η : ℂ) (κ : ℝ) (x : ℝ) : ℂ :=
  indexedFixedBankOddChannel μ
    (finiteEulerCoeff S W) (finiteEulerHeight S q) η κ x

/-- Exact 3D-to-1D reflection specification for every finite tensor-Euler bank. -/
theorem finiteEulerFixedBankOddChannel_eq_zero_iff_theta_reflection
    {V ι : Type*} [Fintype V] [Fintype ι]
    (μ : List ℂ) (S : Finset V) (W : V → FiniteWeightFiber ι)
    (q : V → ℝ) (hq : ∀ v ∈ S, 0 < q v)
    (η : ℂ) (κ : ℝ) {x : ℝ} (hx : 0 < x) :
    finiteEulerFixedBankOddChannel μ S W q η κ x = 0 ↔
      indexedTheta (finiteEulerCoeff S W) (finiteEulerHeight S q)
          (completionKernel μ) x =
        (η * (x ^ κ : ℝ)) •
          indexedTheta (finiteEulerCoeff S W) (finiteEulerHeight S q)
            (completionKernel μ) (1 / x) := by
  exact indexedFixedBankOddChannel_eq_zero_iff_theta_reflection
    μ (finiteEulerCoeff S W) (finiteEulerHeight S q)
      (finiteEulerHeight_pos S q hq) η κ hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_indexedCoefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_indexedCoefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.fiberPhasor_indexedReciprocalCoefficientFiber_conj
#print axioms CriticalLinePhasor.GlobalHelix.multiplicativeHeight_indexedReciprocalCoefficientFiber
#print axioms CriticalLinePhasor.GlobalHelix.indexedFixedPrimalBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.indexedFixedTransformedConjugateDualBankReadout_eq_theta_one_div
#print axioms CriticalLinePhasor.GlobalHelix.indexedFixedBankOddChannel_eq_zero_iff_theta_reflection
#print axioms CriticalLinePhasor.GlobalHelix.finiteTensorEulerBankReadout_completionKernel_eq_indexedFixedPrimal
#print axioms CriticalLinePhasor.GlobalHelix.finiteEulerFixedBankOddChannel_eq_zero_iff_theta_reflection
