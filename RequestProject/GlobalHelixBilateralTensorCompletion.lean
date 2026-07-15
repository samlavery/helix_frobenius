import RequestProject.GlobalHelixGaussianPoissonLift

/-!
# Bilateral completion of the tensor-Euler source

Finite tensor-Euler coefficients are placed on the nonnegative orthant of the integral exponent
lattice.  Adding the reciprocal-index image with its Gaussian half-density produces a coefficient
bank fixed by the Poisson dual-amplitude transform.  The completed reflection is then an equality
of 3D helix banks.
-/

open Real Complex
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- The finite tensor-Euler coefficient seed, extended by zero off the nonnegative orthant. -/
noncomputable def bilateralTensorEulerSeed
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (k : (v : S) → ℤ) : ℂ :=
  if ∀ v, 0 ≤ k v then
    ∏ v : S, localEulerCoeff (W v) (k v).toNat
  else 0

/-- On a natural exponent vector the bilateral seed is the original finite Euler coefficient. -/
theorem bilateralTensorEulerSeed_natCast
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (k : (v : S) → ℕ) :
    bilateralTensorEulerSeed S W (fun v => (k v : ℤ)) =
      ∏ v : S, localEulerCoeff (W v) (k v) := by
  unfold bilateralTensorEulerSeed
  simp

/-- Bilateral Gaussian completion of an arbitrary coefficient seed. -/
noncomputable def bilateralGaussianCompletionAmplitude
    {V : Type*} (S : Finset V) (q : V → ℝ)
    (b : ((v : S) → ℤ) → ℂ) (k : (v : S) → ℤ) : ℂ :=
  b k + ((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) * b (-k)

/-- Reciprocal exponent heights have cancelling Gaussian half-densities. -/
theorem bilateralEulerHalfDensity_neg_mul
    {V : Type*} (S : Finset V) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) (k : (v : S) → ℤ) :
    (bilateralEulerHeight S q (-k)) ^ (1 / 2 : ℝ) *
        (bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) = 1 := by
  rw [bilateralEulerHeight_neg, Real.inv_rpow (bilateralEulerHeight_pos S q hq k).le]
  exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos
    (bilateralEulerHeight_pos S q hq k) _))

/-- The bilateral completion is fixed by reciprocal-index Gaussian transport. -/
theorem gaussianPoissonDualAmplitude_bilateralGaussianCompletion
    {V : Type*} (S : Finset V) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v)
    (b : ((v : S) → ℤ) → ℂ) (k : (v : S) → ℤ) :
    gaussianPoissonDualAmplitude
        (bilateralGaussianCompletionAmplitude S q b)
        (bilateralEulerHeight S q) (negExponentEquiv S) k =
      bilateralGaussianCompletionAmplitude S q b k := by
  unfold gaussianPoissonDualAmplitude bilateralGaussianCompletionAmplitude
  change
    (b (-k) +
        ((bilateralEulerHeight S q (-k)) ^ (1 / 2 : ℝ) : ℝ) * b (-(-k))) *
          ((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) =
      b k + ((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) * b (-k)
  rw [neg_neg]
  have hd := bilateralEulerHalfDensity_neg_mul S q hq k
  have hdC :
      (((bilateralEulerHeight S q (-k)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hd
  calc
    (b (-k) +
        (((bilateralEulerHeight S q (-k)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * b k) *
          (((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
        b (-k) * (((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
          ((((bilateralEulerHeight S q (-k)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            (((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) * b k := by
      ring
    _ = b k +
        (((bilateralEulerHeight S q k) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * b (-k) := by
      rw [hdC, one_mul]
      ring

/-- The completed tensor-Euler amplitude on the bilateral exponent lattice. -/
noncomputable def bilateralTensorEulerCompletionAmplitude
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) :
    ((v : S) → ℤ) → ℂ :=
  bilateralGaussianCompletionAmplitude S q (bilateralTensorEulerSeed S W)

/-- The completed tensor-Euler source, constructed first as a Gaussian-weighted 3D helix bank. -/
noncomputable def bilateralTensorEulerCompleted3DBankReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (x : ℝ) : ℂ :=
  indexedGaussian3DBankReadout
    (bilateralTensorEulerCompletionAmplitude S W q)
    (bilateralEulerHeight S q) x

/-- The globally reflected/sheared anti-helix bank of the completed tensor-Euler source. -/
noncomputable def bilateralTensorEulerCompleted3DTransformedReadout
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ) (x : ℝ) : ℂ :=
  indexedGaussian3DTransformedReadout
    (bilateralTensorEulerCompletionAmplitude S W q)
    (bilateralEulerHeight S q) (negExponentEquiv S) x

/-- The transformed 3D bank projects with the same completed tensor-Euler amplitude. -/
theorem bilateralTensorEulerCompleted3DTransformedReadout_eq_theta
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) {x : ℝ} (hx : 0 < x) :
    bilateralTensorEulerCompleted3DTransformedReadout S W q x =
      indexedTheta (bilateralTensorEulerCompletionAmplitude S W q)
        (bilateralEulerHeight S q) (fun t => (gaussianLatticeTheta t : ℂ)) (1 / x) := by
  rw [bilateralTensorEulerCompleted3DTransformedReadout,
    indexedGaussian3DTransformedReadout_eq_theta _ _ _
      (bilateralEulerHeight_pos S q hq) hx]
  congr 1
  funext k
  exact gaussianPoissonDualAmplitude_bilateralGaussianCompletion
    S q hq (bilateralTensorEulerSeed S W) k

/-- Exact global reflection of the completed tensor-Euler 3D helix bank. -/
theorem bilateralTensorEulerCompleted3D_globalHelixReflection
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 0 < q v) {x : ℝ} (hx : 0 < x) :
    bilateralTensorEulerCompleted3DBankReadout S W q x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        bilateralTensorEulerCompleted3DTransformedReadout S W q x := by
  unfold bilateralTensorEulerCompleted3DBankReadout
  exact indexedGaussian3D_globalHelixReflection
    (bilateralTensorEulerCompletionAmplitude S W q)
    (bilateralEulerHeight S q) (negExponentEquiv S)
    (bilateralEulerHeight_pos S q hq)
    (fun k => bilateralEulerHeight_neg S q k) hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.bilateralTensorEulerSeed_natCast
#print axioms CriticalLinePhasor.GlobalHelix.bilateralEulerHalfDensity_neg_mul
#print axioms CriticalLinePhasor.GlobalHelix.gaussianPoissonDualAmplitude_bilateralGaussianCompletion
#print axioms CriticalLinePhasor.GlobalHelix.bilateralTensorEulerCompleted3DTransformedReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.bilateralTensorEulerCompleted3D_globalHelixReflection
