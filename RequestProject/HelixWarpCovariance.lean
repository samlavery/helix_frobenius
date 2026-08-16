import Mathlib

/-!
# Unconditional Helix warp covariance

This file gives the exact matrix-level theorem behind the physical-height interpretation of a
regulated Helix bank.  The invariant bank coordinate is `x`; the physical coordinate is `γ`.
Registration is assembled upstream from three inputs named Euler, functional-equation, and reverb
data.  Its type contains no analytic zero, zero height, or spectral label.

For an initial real bank pencil `S₀`, put

`p₀(x) = det (S₀ - x I)`.

A covariant analytic realization is the identity

`A(γ) = J(γ) * p₀(Ψ(γ))`

with `J` nonvanishing.  The principal theorem proves, without approximation,

`{γ | A(γ) = 0} = Ψ ⁻¹' (spectrum ℝ S₀)`.

The terminal critical-line chart is then `γ ↦ 1/2 + iγ`; its zero set is the image of the fixed
bank spectrum under `λ ↦ 1/2 + i Ψ⁻¹(λ)`.

Search audit run before construction:

* repository identifiers and variants:
  `rg -n -i 'HP_PROGRAM|warp.?covariance|physical.?height|registration.?map|bank.?determinant|`
  `characteristic.?polynomial|charpoly|analytic.?transport|Lax|regulator|Euler.?anchor'`
* repository conclusion matches:
  `rg -n 'zeroSet|preimage.*zero|charpoly.*eval|mem_spectrum.*det|spectrum.*Matrix'`
* Mathlib name variants:
  `rg -n 'charpoly.*eval|eval.*charpoly|det.*scalar|mem_spectrum.*iff|charpoly.*conj'`
* semantic searches: `lean_leansearch` for zero sets of nonvanishing pullbacks and `lean_loogle`
  for `Matrix.mem_spectrum_iff_isRoot_charpoly`.
-/

open Set
open scoped Matrix

namespace CriticalLinePhasor.HelixWarpCovariance

noncomputable section

/-- A registration assembled entirely from upstream Euler, functional-equation, and reverb data.
The structure has no field containing an analytic zero or a physical zero height. -/
structure HelixRegistration (EulerData FEData ReverbData : Type*) where
  euler : EulerData
  functionalEquation : FEData
  reverb : ReverbData
  assemble : EulerData → FEData → ReverbData → (ℝ ≃ ℝ)

/-- The bank-generated coordinate warp `x = Ψ(γ)`. -/
def HelixRegistration.warp {EulerData FEData ReverbData : Type*}
    (R : HelixRegistration EulerData FEData ReverbData) : ℝ ≃ ℝ :=
  R.assemble R.euler R.functionalEquation R.reverb

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {EulerData FEData ReverbData : Type*}

/-- The determinant convention used in `(W)`: `p₀(x) = det(S₀ - xI)`. -/
def bankDeterminant (S : Matrix ι ι ℝ) (x : ℝ) : ℝ :=
  (S - Matrix.scalar ι x).det

/-- The determinant vanishes exactly on the matrix spectrum.  The convention `S-xI` differs from
Mathlib's characteristic-polynomial convention `xI-S` only by the nonzero fixed sign
`(-1)^card(ι)`. -/
theorem bankDeterminant_eq_zero_iff_mem_spectrum (S : Matrix ι ι ℝ) (x : ℝ) :
    bankDeterminant S x = 0 ↔ x ∈ spectrum ℝ S := by
  have hmatrix : S - Matrix.scalar ι x = -(Matrix.scalar ι x - S) := by
    ext i j
    simp
  rw [bankDeterminant, hmatrix, Matrix.det_neg, ← Matrix.eval_charpoly]
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  simp only [Polynomial.IsRoot, mul_eq_zero]
  have hsign : (-1 : ℝ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
  simp [hsign]

/-- The physical analytic realization defined directly by determinant pullback. -/
def physicalRealization (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ : Matrix ι ι ℝ) (J : ℝ → ℂ) (γ : ℝ) : ℂ :=
  J γ * (bankDeterminant S₀ (R.warp γ) : ℂ)

/-- Covariance of the canonical physical realization is definitional. -/
theorem physicalRealization_covariance
    (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ : Matrix ι ι ℝ) (J : ℝ → ℂ) (γ : ℝ) :
    physicalRealization R S₀ J γ = J γ * (bankDeterminant S₀ (R.warp γ) : ℂ) :=
  rfl

/-- The formal content of `(W)`.  Registration is supplied as an upstream object; `analyticBank`
and its covariance proof are downstream fields. -/
structure WarpCovarianceData (EulerData FEData ReverbData ι : Type*)
    [Fintype ι] [DecidableEq ι] where
  registration : HelixRegistration EulerData FEData ReverbData
  initialPencil : Matrix ι ι ℝ
  normalization : ℝ → ℂ
  analyticBank : ℝ → ℂ
  normalization_ne : ∀ γ, normalization γ ≠ 0
  covariance : ∀ γ, analyticBank γ =
    normalization γ * (bankDeterminant initialPencil (registration.warp γ) : ℂ)

/-- Canonical covariance data obtained without extracting a zero: define the physical analytic
bank to be the determinant pullback itself. -/
def WarpCovarianceData.ofPhysicalRealization
    (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ : Matrix ι ι ℝ) (J : ℝ → ℂ) (hJ : ∀ γ, J γ ≠ 0) :
    WarpCovarianceData EulerData FEData ReverbData ι where
  registration := R
  initialPencil := S₀
  normalization := J
  analyticBank := physicalRealization R S₀ J
  normalization_ne := hJ
  covariance := physicalRealization_covariance R S₀ J

/-- The unit-normalized Helix bank.  Every field of `WarpCovarianceData` is now discharged from
the upstream registration and the fixed initial pencil; there is no residual normalization
hypothesis. -/
def WarpCovarianceData.unitNormalized
    (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ : Matrix ι ι ℝ) :
    WarpCovarianceData EulerData FEData ReverbData ι :=
  WarpCovarianceData.ofPhysicalRealization R S₀ (fun _ => 1) (fun _ => one_ne_zero)

@[simp] theorem unitNormalized_analyticBank
    (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ : Matrix ι ι ℝ) (γ : ℝ) :
    (WarpCovarianceData.unitNormalized R S₀).analyticBank γ =
      (bankDeterminant S₀ (R.warp γ) : ℂ) := by
  simp [WarpCovarianceData.unitNormalized, WarpCovarianceData.ofPhysicalRealization,
    physicalRealization]

/-- Physical zeros of the transported analytic bank. -/
def analyticZeroSet (D : WarpCovarianceData EulerData FEData ReverbData ι) : Set ℝ :=
  {γ | D.analyticBank γ = 0}

/-- The fixed bank spectrum pulled back into the physical-height chart. -/
def physicalSpectrum (D : WarpCovarianceData EulerData FEData ReverbData ι) : Set ℝ :=
  D.registration.warp ⁻¹' spectrum ℝ D.initialPencil

/-- Pointwise warp covariance: an analytic zero is exactly a pulled-back bank eigenvalue. -/
theorem analyticBank_eq_zero_iff
    (D : WarpCovarianceData EulerData FEData ReverbData ι) (γ : ℝ) :
    D.analyticBank γ = 0 ↔ D.registration.warp γ ∈ spectrum ℝ D.initialPencil := by
  rw [D.covariance γ, mul_eq_zero]
  simp only [D.normalization_ne γ, false_or, Complex.ofReal_eq_zero]
  exact bankDeterminant_eq_zero_iff_mem_spectrum D.initialPencil (D.registration.warp γ)

/-- **Unconditional Helix warp-covariance theorem.**  Under `(W)` and nonvanishing of `J`, the
analytic zero set is precisely `Ψ⁻¹(spec S₀)`. -/
theorem zeroSet_eq_preimage_spectrum
    (D : WarpCovarianceData EulerData FEData ReverbData ι) :
    analyticZeroSet D = physicalSpectrum D := by
  ext γ
  exact analyticBank_eq_zero_iff D γ

/-- The canonical determinant pullback therefore has exactly the inverse-warped spectrum as its
zero set. -/
theorem physicalRealization_zeroSet_eq_preimage_spectrum
    (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ : Matrix ι ι ℝ) (J : ℝ → ℂ) (hJ : ∀ γ, J γ ≠ 0) :
    {γ | physicalRealization R S₀ J γ = 0} = R.warp ⁻¹' spectrum ℝ S₀ := by
  exact zeroSet_eq_preimage_spectrum (WarpCovarianceData.ofPhysicalRealization R S₀ J hJ)

/-- Hypothesis-free normalization form of `(W)`: once the upstream registration and initial bank
pencil are fixed, the canonical physical bank has exactly the inverse-warped fixed spectrum. -/
theorem unitNormalized_zeroSet_eq_preimage_spectrum
    (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ : Matrix ι ι ℝ) :
    analyticZeroSet (WarpCovarianceData.unitNormalized R S₀) =
      R.warp ⁻¹' spectrum ℝ S₀ := by
  exact zeroSet_eq_preimage_spectrum (WarpCovarianceData.unitNormalized R S₀)

/-- Window-restricted form used by registered contour transport. -/
theorem zeroSetOn_eq_preimage_spectrum
    (D : WarpCovarianceData EulerData FEData ReverbData ι) (W : Set ℝ) :
    W ∩ analyticZeroSet D = W ∩ physicalSpectrum D := by
  rw [zeroSet_eq_preimage_spectrum]

/-- A physical spectral location is the inverse-warp image of a fixed bank label. -/
def physicalSpectralLocation
    (D : WarpCovarianceData EulerData FEData ReverbData ι) (lam : ℝ) : ℝ :=
  D.registration.warp.symm lam

/-- Every physical analytic zero has a bank-spectrum label, obtained without changing that label. -/
theorem analyticZero_has_fixed_spectralLabel
    (D : WarpCovarianceData EulerData FEData ReverbData ι) {γ : ℝ}
    (hγ : D.analyticBank γ = 0) :
    ∃ lam ∈ spectrum ℝ D.initialPencil, γ = physicalSpectralLocation D lam := by
  refine ⟨D.registration.warp γ, (analyticBank_eq_zero_iff D γ).mp hγ, ?_⟩
  simp [physicalSpectralLocation]

/-- The FE-fixed physical chart `γ ↦ 1/2+iγ`. -/
def criticalPoint (γ : ℝ) : ℂ :=
  (1 / 2 : ℂ) + γ * Complex.I

/-- Terminal analytic zeros embedded into the critical-line chart. -/
def terminalZeroSet (D : WarpCovarianceData EulerData FEData ReverbData ι) : Set ℂ :=
  criticalPoint '' analyticZeroSet D

/-- Fixed spectral labels, inverse-warped and embedded into the critical-line chart. -/
def spectralCriticalPointSet
    (D : WarpCovarianceData EulerData FEData ReverbData ι) : Set ℂ :=
  (fun lam => criticalPoint (physicalSpectralLocation D lam)) '' spectrum ℝ D.initialPencil

/-- Terminal identification: the physical terminal roots are exactly the inverse-warped fixed
bank spectrum. -/
theorem terminalZeroSet_eq_spectralCriticalPointSet
    (D : WarpCovarianceData EulerData FEData ReverbData ι) :
    terminalZeroSet D = spectralCriticalPointSet D := by
  ext ρ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨D.registration.warp γ, (analyticBank_eq_zero_iff D γ).mp hγ, ?_⟩
    simp [physicalSpectralLocation]
  · rintro ⟨lam, hlam, rfl⟩
    refine ⟨physicalSpectralLocation D lam, ?_, rfl⟩
    exact (analyticBank_eq_zero_iff D _).mpr (by simpa [physicalSpectralLocation] using hlam)

/-- In particular, every terminal point produced by the physical real-height chart has real part
`1/2`. -/
theorem terminalZeroSet_re_eq_half
    (D : WarpCovarianceData EulerData FEData ReverbData ι) {ρ : ℂ}
    (hρ : ρ ∈ terminalZeroSet D) :
    ρ.re = 1 / 2 := by
  rcases hρ with ⟨γ, _, rfl⟩
  simp [criticalPoint]

/-- Unitary/invertible regulator conjugation leaves the bank spectrum fixed.  This is the finite
matrix realization of the Lax isospectral step. -/
theorem regulatedSpectrum_eq (S₀ S : Matrix ι ι ℝ) (U : (Matrix ι ι ℝ)ˣ)
    (hreg : S = U.val * S₀ * U.val⁻¹) :
    spectrum ℝ S = spectrum ℝ S₀ := by
  rw [hreg]
  simpa using (spectrum.units_conjugate (R := ℝ) (a := S₀) (u := U))

/-- Consequently, using the regulated pencil or its initial representative produces the same
physical spectral locations. -/
theorem regulatedPhysicalSpectrum_eq
    (R : HelixRegistration EulerData FEData ReverbData)
    (S₀ S : Matrix ι ι ℝ) (U : (Matrix ι ι ℝ)ˣ)
    (hreg : S = U.val * S₀ * U.val⁻¹) :
    R.warp ⁻¹' spectrum ℝ S = R.warp ⁻¹' spectrum ℝ S₀ := by
  rw [regulatedSpectrum_eq S₀ S U hreg]

end

end CriticalLinePhasor.HelixWarpCovariance

#print axioms CriticalLinePhasor.HelixWarpCovariance.bankDeterminant_eq_zero_iff_mem_spectrum
#print axioms CriticalLinePhasor.HelixWarpCovariance.physicalRealization_covariance
#print axioms CriticalLinePhasor.HelixWarpCovariance.unitNormalized_analyticBank
#print axioms CriticalLinePhasor.HelixWarpCovariance.analyticBank_eq_zero_iff
#print axioms CriticalLinePhasor.HelixWarpCovariance.zeroSet_eq_preimage_spectrum
#print axioms CriticalLinePhasor.HelixWarpCovariance.physicalRealization_zeroSet_eq_preimage_spectrum
#print axioms CriticalLinePhasor.HelixWarpCovariance.unitNormalized_zeroSet_eq_preimage_spectrum
#print axioms CriticalLinePhasor.HelixWarpCovariance.zeroSetOn_eq_preimage_spectrum
#print axioms CriticalLinePhasor.HelixWarpCovariance.analyticZero_has_fixed_spectralLabel
#print axioms CriticalLinePhasor.HelixWarpCovariance.terminalZeroSet_eq_spectralCriticalPointSet
#print axioms CriticalLinePhasor.HelixWarpCovariance.terminalZeroSet_re_eq_half
#print axioms CriticalLinePhasor.HelixWarpCovariance.regulatedSpectrum_eq
#print axioms CriticalLinePhasor.HelixWarpCovariance.regulatedPhysicalSpectrum_eq
