import RequestProject.NativePencilLimitTrace

/-!
# Where `s` sits in the native self-adjoint pencil (ledger 1201)

The stage-`N` native two-lane pencil `A_N(s) − z·B_N(s)` (`NativePencilLimitTrace`) is
Hermitian-definite: `A_N(s)` is Hermitian for every complex `s` (`stageA_isHermitian`; the coupling
enters as `C` and `Cᴴ`), `B_N > 0` on independent lanes (`twoLaneB_posDef`), and every generalized
eigenvalue `z` is real (`twoLane_eigenheight_real`).

* `stage_det_at_reference`: at the real spectral value `z = (N+1)/2`, the reference lane's mean height,
  `det(A_N(s) − z·B_N(s)) = −|S_N(s)|²`, with `S_N(s)` the native coupling (the signed channel's
  partial sum, `nativeCoupling_tendsto_LFunction`).
* `stage_kernel_at_reference_iff`: **the focal cancellation is a kernel event of the native
  self-adjoint pencil**: `ker(A_N(s) − ((N+1)/2)·B_N(s)) ≠ 0 ⟺ S_N(s) = 0`.

The kernel appears at the fixed real value `(N+1)/2`, with `s` inside the operator. Self-adjointness
makes the spectral value real, and `(N+1)/2` is real for every `s`; it places no condition on `s`.
-/

open Matrix Complex

noncomputable section

namespace CriticalLinePhasor.NativeSpectralSlot

open CriticalLinePhasor CriticalLinePhasor.NativeSquare CriticalLinePhasor.Geometric
open CriticalLinePhasor.Pencil3D

/-- **The native two-lane operator is Hermitian at every complex `s`.** -/
theorem stageA_isHermitian (w : ℕ → ℂ) (s : ℂ) (N : ℕ) : (stageA w s N).IsHermitian :=
  twoLaneHelixA_isHermitian _ _ fun i => by positivity

/-- **At the reference lane's mean height the pencil determinant is `−|S_N(s)|²`.** -/
theorem stage_det_at_reference (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (stageA w s N - (((N : ℂ) + 1) / 2) • stageB w s N).det =
      -((‖nativeCoupling w s N‖ ^ 2 : ℝ) : ℂ) := by
  rw [stage_charpoly, stageA_reference]
  ring

/-- **The focal cancellation is a kernel event of the native self-adjoint pencil**, at the real
spectral value `(N+1)/2`. -/
theorem stage_kernel_at_reference_iff (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (∃ v ≠ 0, (stageA w s N - (((N : ℂ) + 1) / 2) • stageB w s N) *ᵥ v = 0) ↔
      nativeCoupling w s N = 0 := by
  rw [Matrix.exists_mulVec_eq_zero_iff, stage_det_at_reference, neg_eq_zero, Complex.ofReal_eq_zero]
  constructor
  · intro h
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  · intro h
    rw [h, norm_zero]
    ring

end CriticalLinePhasor.NativeSpectralSlot

end

#print axioms CriticalLinePhasor.NativeSpectralSlot.stageA_isHermitian
#print axioms CriticalLinePhasor.NativeSpectralSlot.stage_det_at_reference
#print axioms CriticalLinePhasor.NativeSpectralSlot.stage_kernel_at_reference_iff
