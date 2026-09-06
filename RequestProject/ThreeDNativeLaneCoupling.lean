import RequestProject.ThreeDPencilOperator
import RequestProject.SpectralFiberIsLFunction
import RequestProject.ZetaZeroDefs

/-!
# The native phasor fiber in the off-diagonal 3D pencil coupling

At physical sites n = 1,...,N use the reference feature Q₊(n)=1 and the
despun fiber feature Q₋(n)=cell(n)⁻¹ plane(phasor3D(w,Re s,Im s,n)).
The repository's coupling Q₊* diag(cell) Q₋ is then exactly the native finite
phasor sum.  Its adjoint supplies the conjugate return lane.  The two spatial
operator coefficients retain the positive Gram metric and signed real heights.

These statements use the entire input s, including its radial amplitude coordinate.
For a nonprincipal character the coupling converges to Lχ(s) on Re s>0.
For the principal channel the eta configuration converges to (1-2^(1-s))ζ(s).

Unfolded target: C_N(0,0)=Σ(n=1..N) w(n)n^(-s), with the phase and amplitude
coming from the existing 3D phasor readout.  No eigenparameter is identified by
this sum identity alone; the full pencil equation remains separately visible.

Two decompositions: expand `laneCouplingC` and cancel each unit cell, or pass
the already proved 3D readout convergence through the finite-sum equality.
First Lean lines: `simp only [laneCouplingC, Matrix.mul_apply]` and
`have h := SpectralFiber.spectralFiber_readout_tendsto_LFunction χ hχ hs`.

Searches:
`rg -n 'cell.*(conj|norm|abs|unit)|conj.*cell|mellinSpin.*(norm|conj)'
RequestProject/GeometricPhasorClosure.lean RequestProject/LFunctionPhasor.lean`
`rg -n 'mulVec_single|continuous.*kronecker|Continuous.*matrix_(det|mulVec|mul)'
.lake/packages/mathlib/Mathlib --glob '*.lean'`
LeanSearch: continuity of matrix multiplication by a fixed vector.
Loogle: `Filter.Tendsto, Matrix.mulVec`.
-/

open Matrix Complex Filter Topology
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.Pencil3D

open Geometric SpectralFiber

noncomputable def referenceLane (N : ℕ) : Matrix (Fin N) (Fin 1) ℂ := fun _ _ => 1

noncomputable def nativeFiberLane (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    Matrix (Fin N) (Fin 1) ℂ :=
  fun i _ => (cell (i.val + 1))⁻¹ * readout w s (i.val + 1)

/-- The actual off-diagonal coupling in the geometric pencil. -/
noncomputable def nativeCoupling (w : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  laneCouplingC (referenceLane N) (nativeFiberLane w s N) 0 0

theorem cell_ne_zero (n : ℕ) : cell n ≠ 0 := by
  have h := cell_norm n
  intro hz
  simp [hz] at h

/-- The despin is precisely the conjugate carrier phase. -/
theorem cell_inverse_eq_conjugate (n : ℕ) : (cell n)⁻¹ = star (cell n) := by
  apply inv_eq_of_mul_eq_one_right
  simp [Complex.mul_conj', cell_norm]

/-- Each finite off-diagonal entry is the complete native 3D phasor readout sum. -/
theorem nativeCoupling_eq_sum (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    nativeCoupling w s N = ∑ i : Fin N, readout w s (i.val + 1) := by
  simp only [nativeCoupling, laneCouplingC, Matrix.mul_apply, Matrix.conjTranspose_apply,
    referenceLane, star_one, one_mul, nativeFiberLane]
  simp only [Matrix.diagonal, Matrix.of_apply]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, mul_inv_cancel₀ (cell_ne_zero _), one_mul]

theorem nativeCoupling_eq_partialSum (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    nativeCoupling w s N = ∑ n ∈ Finset.range (N + 1), readout w s n := by
  rw [nativeCoupling_eq_sum,
    Fin.sum_univ_eq_sum_range (fun n => readout w s (n + 1)) N, Finset.sum_range_succ']
  simp [readout_eq_phasorTerm, LFunctionPhasor.phasorTerm]

/-- The native geometric coupling converges to the nonprincipal L-function for every Re s>0. -/
theorem nativeCoupling_tendsto_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (nativeCoupling (fun n => χ (n : ZMod q)) s) atTop
      (nhds (DirichletCharacter.LFunction χ s)) := by
  have h := spectralFiber_readout_tendsto_LFunction χ hχ hs
  have hn : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
  change Tendsto (fun N => nativeCoupling (fun n => χ (n : ZMod q)) s N) _ _
  simp only [nativeCoupling_eq_partialSum]
  exact h.comp hn

/-- Principal-channel coupling, retaining the eta factor exactly. -/
theorem nativeCoupling_tendsto_eta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (nativeCoupling etaW s) atTop
      (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s)) := by
  have h := etaSpectralFiber_readout_tendsto_zeta hs hs1
  have hn : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
  change Tendsto (fun N => nativeCoupling etaW s N) _ _
  simp only [nativeCoupling_eq_partialSum]
  exact h.comp hn

/-- At any nontrivial zeta zero the actual native coupling tends to zero. -/
theorem zeta_zero_nativeCoupling_tendsto_zero {s : ℂ} (hs : s ∈ ZD.NontrivialZeros) :
    Tendsto (nativeCoupling etaW s) atTop (nhds 0) := by
  have hs1 : s ≠ 1 := by
    intro h
    have hh := hs.2.1
    simp [h] at hh
  simpa only [hs.2.2, mul_zero] using nativeCoupling_tendsto_eta hs.1 hs1

/-- The spatial two-ended pencil is Hermitian with the native fiber in its coupling block. -/
theorem native_spatial_isHermitian (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (spatial (twoLaneHelixA (referenceLane N) (nativeFiberLane w s N)
      (fun i => (i.val + 1 : ℝ)))).IsHermitian :=
  spatial_isHermitian _ (twoLaneHelixA_isHermitian_signed _ _ _)

/-- Its metric is positive semidefinite before any cancellation is imposed. -/
theorem native_spatial_metric_posSemidef (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (spatial (twoLaneB (referenceLane N) (nativeFiberLane w s N))).PosSemidef :=
  spatial_posSemidef _ (twoLaneB_posSemidef _ _)

theorem native_readout_one (w : ℕ → ℂ) (s : ℂ) : readout w s 1 = w 1 := by
  simp [readout_eq_phasorTerm, LFunctionPhasor.phasorTerm, LFunctionPhasor.mellinSpin]

/-- The site n=1 gives a nonzero feature in both lanes, hence a strictly positive metric. -/
theorem native_metric_posDef (w : ℕ → ℂ) (hw : w 1 ≠ 0) (s : ℂ)
    (N : ℕ) (hN : 0 < N) :
    (twoLaneB (referenceLane N) (nativeFiberLane w s N)).PosDef := by
  apply twoLaneB_posDef
  intro x y hxy
  have hp := congrFun hxy (Sum.inl (⟨0, hN⟩ : Fin N))
  have hm := congrFun hxy (Sum.inr (⟨0, hN⟩ : Fin N))
  simp [stackedFeature, Matrix.mulVec, dotProduct,
    referenceLane] at hp
  simp [stackedFeature, Matrix.mulVec, dotProduct, nativeFiberLane,
    LFunctionPhasor.phasorTerm, LFunctionPhasor.mellinSpin, hw, cell_ne_zero] at hm
  funext j
  rcases j with j | j <;> fin_cases j
  · exact hp
  · exact hm

/-- The native three-spatial-coordinate metric is strictly positive at every nonempty stage. -/
theorem native_spatial_metric_posDef (w : ℕ → ℂ) (hw : w 1 ≠ 0) (s : ℂ)
    (N : ℕ) (hN : 0 < N) :
    (spatial (twoLaneB (referenceLane N) (nativeFiberLane w s N))).PosDef :=
  (native_metric_posDef w hw s N hN).kronecker Matrix.PosDef.one

/-- A fixed spatial state in the reference lane. -/
noncomputable def referenceState : (Fin 1 ⊕ Fin 1) × Fin 3 → ℂ :=
  Pi.single (Sum.inl 0, 0) 1

/-- The reference lane has exactly N units of Gram mass. -/
theorem referenceState_metric_mass (w : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    star referenceState ⬝ᵥ
      (spatial (twoLaneB (referenceLane N) (nativeFiberLane w s N))).mulVec referenceState =
        (N : ℂ) := by
  rw [twoLaneB_eq_blockDiag]
  simp [referenceState, spatial, Matrix.col_apply, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, referenceLane, dotProduct, Pi.single_apply]

end CriticalLinePhasor.Pencil3D

#print axioms CriticalLinePhasor.SpectralFiber.spectralFiber_readout_tendsto_LFunction
#print axioms CriticalLinePhasor.SpectralFiber.etaSpectralFiber_readout_tendsto_zeta
#print axioms CriticalLinePhasor.Pencil3D.cell_inverse_eq_conjugate
#print axioms CriticalLinePhasor.Pencil3D.nativeCoupling_eq_sum
#print axioms CriticalLinePhasor.Pencil3D.nativeCoupling_tendsto_LFunction
#print axioms CriticalLinePhasor.Pencil3D.zeta_zero_nativeCoupling_tendsto_zero
#print axioms CriticalLinePhasor.Pencil3D.native_spatial_isHermitian
#print axioms CriticalLinePhasor.Pencil3D.native_spatial_metric_posSemidef
#print axioms CriticalLinePhasor.Pencil3D.native_metric_posDef
#print axioms CriticalLinePhasor.Pencil3D.native_spatial_metric_posDef
#print axioms CriticalLinePhasor.Pencil3D.referenceState_metric_mass
