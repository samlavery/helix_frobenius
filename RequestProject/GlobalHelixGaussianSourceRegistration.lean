import RequestProject.GlobalHelixIndexedBankReflection
import RequestProject.GlobalHelixGaussianLatticeTheta

/-!
# Gaussian Poisson reflection registered on the 3D helix source

Every nonzero lattice mode is stored at positive multiplicative height `n²x`.  The zero mode is a
distinguished source channel with height `x` and constant kernel readout `1`.  Thus the full
Gaussian theta is first constructed as a sum of 3D source readouts.  The global helix involution
and the exact `hₙ²` shear build the reciprocal-height bank, after which Mathlib's Gaussian Poisson
theorem becomes an equality between the two complete 3D banks.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

open ConeProjection

/-- Positive height ledger for every lattice mode; the zero mode gets the unit height. -/
noncomputable def gaussianLatticeHeight (n : ℤ) : ℝ :=
  if n = 0 then 1 else ((n : ℝ) ^ 2)

theorem gaussianLatticeHeight_pos (n : ℤ) : 0 < gaussianLatticeHeight n := by
  by_cases hn : n = 0
  · simp [gaussianLatticeHeight, hn]
  · simp only [gaussianLatticeHeight, hn, if_false]
    exact sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hn)

/-- The Gaussian kernel on nonzero modes and the constant readout on the zero mode. -/
noncomputable def gaussianLatticeKernelTerm (n : ℤ) (t : ℝ) : ℂ :=
  if n = 0 then 1 else Real.exp (-Real.pi * t)

/-- The Gaussian lattice theta built first as a bank of 3D helix source points. -/
noncomputable def gaussianLattice3DBankReadout (x : ℝ) : ℂ :=
  ∑' n : ℤ,
    fiberPhasor
        (indexedCoefficientFiber (fun _ : ℤ => (1 : ℂ)) gaussianLatticeHeight n x) *
      gaussianLatticeKernelTerm n
        (multiplicativeHeight
          (indexedCoefficientFiber (fun _ : ℤ => (1 : ℂ)) gaussianLatticeHeight n x))

/-- The scalar projection of the 3D source bank is exactly the standard Gaussian theta. -/
theorem gaussianLattice3DBankReadout_eq (x : ℝ) (hx : 0 < x) :
    gaussianLattice3DBankReadout x = (gaussianLatticeTheta x : ℂ) := by
  unfold gaussianLattice3DBankReadout gaussianLatticeTheta
  rw [ofReal_tsum]
  apply tsum_congr
  intro n
  rw [fiberPhasor_indexedCoefficientFiber,
    multiplicativeHeight_indexedCoefficientFiber
      (fun _ : ℤ => (1 : ℂ)) gaussianLatticeHeight gaussianLatticeHeight_pos n hx]
  by_cases hn : n = 0
  · subst n
    norm_num [gaussianLatticeKernelTerm, gaussianLatticeHeight]
  · simp only [gaussianLatticeKernelTerm, hn, if_false, one_mul, ofReal_exp]
    congr 1
    simp only [gaussianLatticeHeight, hn, if_false]
    push_cast
    ring

/-- The Gaussian lattice bank after the global involution and exact height-ledger shear. -/
noncomputable def gaussianLattice3DTransformedReadout (x : ℝ) : ℂ :=
  ∑' n : ℤ,
    fiberPhasor
        (indexedReciprocalCoefficientFiber
          (fun _ : ℤ => (starRingEnd ℂ) 1) gaussianLatticeHeight n x) *
      gaussianLatticeKernelTerm n
        (multiplicativeHeight
          (indexedReciprocalCoefficientFiber
            (fun _ : ℤ => (starRingEnd ℂ) 1) gaussianLatticeHeight n x))

/-- The transformed 3D source bank projects to Gaussian theta at reciprocal external height. -/
theorem gaussianLattice3DTransformedReadout_eq (x : ℝ) (hx : 0 < x) :
    gaussianLattice3DTransformedReadout x =
      (gaussianLatticeTheta (1 / x) : ℂ) := by
  unfold gaussianLattice3DTransformedReadout gaussianLatticeTheta
  rw [ofReal_tsum]
  apply tsum_congr
  intro n
  rw [show (fun _ : ℤ => (starRingEnd ℂ) 1) =
      fun n => (starRingEnd ℂ) ((fun _ : ℤ => (1 : ℂ)) n) by rfl]
  rw [fiberPhasor_indexedReciprocalCoefficientFiber_conj,
    multiplicativeHeight_indexedReciprocalCoefficientFiber
      _ gaussianLatticeHeight gaussianLatticeHeight_pos n hx]
  by_cases hn : n = 0
  · subst n
    norm_num [gaussianLatticeKernelTerm, gaussianLatticeHeight]
  · simp only [gaussianLatticeKernelTerm, hn, if_false, one_mul, ofReal_exp]
    congr 1
    simp only [gaussianLatticeHeight, hn, if_false]
    push_cast
    ring

/-- Poisson summation as an exact equality of the primal and transformed 3D helix banks. -/
theorem gaussianLattice3D_globalHelixReflection {x : ℝ} (hx : 0 < x) :
    gaussianLattice3DBankReadout x =
      (((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
        gaussianLattice3DTransformedReadout x := by
  rw [gaussianLattice3DBankReadout_eq x hx,
    gaussianLattice3DTransformedReadout_eq x hx]
  rw [← ofReal_mul]
  norm_cast
  exact gaussianLatticeTheta_reflection hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeHeight_pos
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLattice3DBankReadout_eq
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLattice3DTransformedReadout_eq
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLattice3D_globalHelixReflection
