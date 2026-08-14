import RequestProject.GeneralSeed
import RequestProject.MaassIdentification
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.NumberTheory.Divisors

/-!
# Genuine level-one Maass cusp forms

This file upgrades the coefficient recurrence package `MaassEigenData` to an
actual nonzero level-one cuspidal Maass wave.  The wave is definitionally its
Fourier--Whittaker expansion, so the analytic object, its Hecke eigenvalues, and
the Satake coefficients used by the CPS tower cannot be chosen independently.
-/

open Filter Topology
open scoped MatrixGroups UpperHalfPlane

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed
open CriticalLinePhasor.MaassIdentification

/-- The coefficient sequence occurring in the Fourier--Whittaker expansion. -/
def maassFourierCoefficient (M : MaassEigenData) (n : ℕ) : ℂ :=
  M.lam (n + 1)

/-- The normalized weight-zero Hecke operator in upper-half-plane coordinates.
For `ad = n`, the representatives are `z ↦ (az + b) / d`, `0 ≤ b < d`. -/
noncomputable def maassHeckeOperator (n : ℕ) (f : ℝ → ℝ → ℂ) : ℝ → ℝ → ℂ :=
  fun x y ↦ (Real.sqrt n : ℂ)⁻¹ *
    ∑ d ∈ n.divisors, ∑ b ∈ Finset.range d,
      f ((((n / d : ℕ) : ℝ) * x + b) / d)
        (((n / d : ℕ) : ℝ) * y / d)

/-- The positive hyperbolic Laplacian `-y²(∂²_x + ∂²_y)`. -/
noncomputable def maassHyperbolicLaplacian (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  -(y : ℂ) ^ 2 *
    (iteratedDeriv 2 (fun u ↦ f u y) x + iteratedDeriv 2 (fun v ↦ f x v) y)

/-- The coordinate Fourier--Whittaker series attached to normalized Hecke data. -/
noncomputable def maassWaveCoordinates (M : MaassEigenData) (K : ℝ → ℂ) :
    ℝ → ℝ → ℂ :=
  waveForm (maassFourierCoefficient M) K

/-- The same Fourier--Whittaker series as a function on the upper half-plane. -/
noncomputable def maassWave (M : MaassEigenData) (K : ℝ → ℂ) : UpperHalfPlane → ℂ :=
  waveFormH (maassFourierCoefficient M) K

/-- **The radial data as the pre-repair `radial_equation` stated it**: the modified Bessel equation
with its first-order term `y·K'` dropped, together with the decay and normalization that a genuine
Whittaker kernel must satisfy.

This bundle is kept, and named, because it is provably **uninhabited**
(`firstOrderFreeRadialData_false`): no kernel obeying it can also decay and carry the standard
Whittaker normalization `2√y·e^{2πy}·K(y) → 1`.  That is the certificate that the dropped term was
load-bearing, and it is why `GenuineMaassCuspForm3D.radial_equation` now carries it.

The mechanism is `sqrt_weight_sign_flip`: writing `S = 2√y·e^{2πy}·K`, this equation gives
`S'' − 4πS' = c·S/y²` with `c = +r² ≥ 0`, while the true Whittaker equation gives
`c = −(1/4 + r²) < 0`.  `no_positive_decaying_solution` rules out exactly `c ≥ 0`. -/
structure FirstOrderFreeRadialData where
  spectralParameter : ℝ
  radialKernel : ℝ → ℂ
  radial_smooth : ∀ k : ℕ, ContDiffOn ℝ k radialKernel (Set.Ioi 0)
  radial_equation : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * iteratedDeriv 2 radialKernel y =
      (((2 * Real.pi * y) ^ 2 + spectralParameter ^ 2 : ℝ) : ℂ) * radialKernel y
  radial_decay : Tendsto radialKernel atTop (nhds 0)
  radial_normalization :
    Tendsto
      (fun y : ℝ ↦
        ((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) * radialKernel y)
      atTop (nhds 1)

/-- A normalized nonzero even level-one Hecke--Maass cusp form.

The radial kernel is characterized on the positive ray by the modified Bessel
equation for `K_{it}(2πy)`, decay, and its standard leading asymptotic.  The
wave itself is definitionally the Fourier--Whittaker expansion whose coefficients
are the `MaassEigenData` consumed by the CPS construction. -/
structure GenuineMaassCuspForm3D where
  eigenData : MaassEigenData
  spectralParameter : ℝ
  radialKernel : ℝ → ℂ
  radial_smooth : ∀ k : ℕ, ContDiffOn ℝ k radialKernel (Set.Ioi 0)
  radial_equation : ∀ y : ℝ, 0 < y →
    (y : ℂ) ^ 2 * iteratedDeriv 2 radialKernel y + (y : ℂ) * deriv radialKernel y =
      (((2 * Real.pi * y) ^ 2 - spectralParameter ^ 2 : ℝ) : ℂ) * radialKernel y
  radial_decay : Tendsto radialKernel atTop (nhds 0)
  radial_normalization :
    Tendsto
      (fun y : ℝ ↦
        ((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) * radialKernel y)
      atTop (nhds 1)
  wave_smooth : ∀ k : ℕ,
    ContDiffOn ℝ k (Function.uncurry (maassWaveCoordinates eigenData radialKernel))
      (Set.univ ×ˢ Set.Ioi 0)
  wave_ne_zero : maassWave eigenData radialKernel ≠ 0
  level_one_invariant : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane),
    maassWave eigenData radialKernel (γ • τ) = maassWave eigenData radialKernel τ
  laplace_eigen : ∀ (x y : ℝ), 0 < y →
    maassHyperbolicLaplacian (maassWaveCoordinates eigenData radialKernel) x y =
      ((1 / 4 + spectralParameter ^ 2 : ℝ) : ℂ) *
        maassWaveCoordinates eigenData radialKernel x y
  cusp_decay : ∀ x : ℝ,
    Tendsto (maassWaveCoordinates eigenData radialKernel x) atTop (nhds 0)
  hecke_eigen : ∀ n : ℕ, 0 < n →
    maassHeckeOperator n (maassWaveCoordinates eigenData radialKernel) =
      fun x y ↦ eigenData.lam n * maassWaveCoordinates eigenData radialKernel x y

namespace GenuineMaassCuspForm3D

/-- The actual upper-half-plane wave carried by a genuine Maass cusp form. -/
noncomputable def wave (M : GenuineMaassCuspForm3D) : UpperHalfPlane → ℂ :=
  maassWave M.eigenData M.radialKernel

/-- Its coordinate realization on `y > 0`. -/
noncomputable def waveCoordinates (M : GenuineMaassCuspForm3D) : ℝ → ℝ → ℂ :=
  maassWaveCoordinates M.eigenData M.radialKernel

/-- Exact Fourier--Whittaker identification with the CPS coefficient projection. -/
theorem fourierWhittaker (M : GenuineMaassCuspForm3D) (x y : ℝ) :
    M.waveCoordinates x y =
      (Real.sqrt y : ℂ) *
        ∑' n : ℕ, M.eigenData.lam (n + 1) *
          (Real.cos (2 * Real.pi * (n + 1) * x) : ℂ) * M.radialKernel ((n + 1) * y) := by
  rfl

/-- The coefficient projection is normalized at `1`. -/
@[simp] theorem eigenData_lam_one (M : GenuineMaassCuspForm3D) :
    M.eigenData.lam 1 = 1 :=
  M.eigenData.one

/-- The defining wave is nonzero. -/
theorem wave_nonzero (M : GenuineMaassCuspForm3D) : M.wave ≠ 0 :=
  M.wave_ne_zero

/-- Full level-one modular invariance of the defining wave. -/
theorem wave_modular (M : GenuineMaassCuspForm3D) (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    M.wave (γ • τ) = M.wave τ :=
  M.level_one_invariant γ τ

/-- The defining wave tends to zero at the cusp on every vertical line. -/
theorem wave_tendsto_cusp (M : GenuineMaassCuspForm3D) (x : ℝ) :
    Tendsto (M.waveCoordinates x) atTop (nhds 0) :=
  M.cusp_decay x

/-- Every classical normalized Hecke operator acts by the projected coefficient. -/
theorem wave_hecke_eigen (M : GenuineMaassCuspForm3D) (n : ℕ) (hn : 0 < n) :
    maassHeckeOperator n M.waveCoordinates =
      fun x y ↦ M.eigenData.lam n * M.waveCoordinates x y :=
  M.hecke_eigen n hn

end GenuineMaassCuspForm3D

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.GenuineMaassCuspForm3D.fourierWhittaker
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineMaassCuspForm3D.wave_nonzero
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineMaassCuspForm3D.wave_modular
#print axioms CriticalLinePhasor.ThreeDConverse.GenuineMaassCuspForm3D.wave_hecke_eigen
