import RequestProject.WeilIdentification
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The multiplier packaging: the q-expansion of a BV-package is a slash eigenform

`hecke_identification` ends at the two generator transformation laws.  This file
packages them along the closure induction: the set of `γ ∈ SL(2,ℤ)` under which a
function is a weight-`k` slash eigenvector is a **subgroup** (the slash-action axioms
are the cocycle), the two laws put `S` and `T` in it, and Mathlib's
`SpecialLinearGroup.SL2Z_generators` closes it to the whole group:

* `slashEigenSubgroup` — the eigen set as a subgroup of `SL(2,ℤ)`;
* `slashEigen_all` — eigen at `S` and `T` ⟹ eigen at every `γ`;
* `qForm_T_eigen` / `qForm_S_eigen` — the compiled laws in slash form: the
  q-expansion is a weight-`1` eigenvector at `T` (eigenvalue `1`) and at `S`
  (eigenvalue `-i·ε⁻¹`);
* `hecke_modularity` — **the headline**: the q-expansion of an entire BV-package at
  the `Γℂ` chart is a weight-`1` slash eigenform at every element of `SL(2,ℤ)` —
  a slash-invariant form with multiplier, typed in Mathlib's own slash action.

No `axiom`, no `sorry`.
-/

open Real Complex UpperHalfPlane MeasureTheory
open scoped MatrixGroups ModularForm

namespace CriticalLinePhasor.MultiplierPackaging

open CriticalLinePhasor.RamifiedMechanism CriticalLinePhasor.PhragmenBV
open CriticalLinePhasor.WeilIdentification CriticalLinePhasor.CarrierTheta

/-! ## The eigen subgroup -/

/-- The set of `γ` under which `f` is a weight-`k` slash eigenvector is a subgroup:
the slash-action axioms are the cocycle. -/
def slashEigenSubgroup (f : ℍ → ℂ) (k : ℤ) : Subgroup SL(2, ℤ) where
  carrier := {γ : SL(2, ℤ) | ∃ v : ℂ, v ≠ 0 ∧ f ∣[k] γ = v • f}
  one_mem' := ⟨1, one_ne_zero, by simp⟩
  mul_mem' := by
    rintro γ δ ⟨v, hv, hγ⟩ ⟨w, hw, hδ⟩
    refine ⟨v * w, mul_ne_zero hv hw, ?_⟩
    calc f ∣[k] (γ * δ) = (f ∣[k] γ) ∣[k] δ := SlashAction.slash_mul k γ δ f
      _ = (v • f) ∣[k] δ := by rw [hγ]
      _ = v • (f ∣[k] δ) := ModularForm.SL_smul_slash k δ f v
      _ = v • (w • f) := by rw [hδ]
      _ = (v * w) • f := smul_smul v w f
  inv_mem' := by
    rintro γ ⟨v, hv, hγ⟩
    refine ⟨v⁻¹, inv_ne_zero hv, ?_⟩
    have h1 : (f ∣[k] γ) ∣[k] γ⁻¹ = f := by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    rw [hγ, ModularForm.SL_smul_slash] at h1
    calc f ∣[k] γ⁻¹ = v⁻¹ • (v • (f ∣[k] γ⁻¹)) := by
          rw [smul_smul, inv_mul_cancel₀ hv, one_smul]
      _ = v⁻¹ • f := by rw [h1]

/-- **Eigen at the generators ⟹ eigen everywhere**, by `SL2Z_generators`. -/
theorem slashEigen_all (f : ℍ → ℂ) (k : ℤ)
    (hS : ∃ v : ℂ, v ≠ 0 ∧ f ∣[k] ModularGroup.S = v • f)
    (hT : ∃ v : ℂ, v ≠ 0 ∧ f ∣[k] ModularGroup.T = v • f) :
    ∀ γ : SL(2, ℤ), ∃ v : ℂ, v ≠ 0 ∧ f ∣[k] γ = v • f := by
  intro γ
  have hle : Subgroup.closure {ModularGroup.S, ModularGroup.T}
      ≤ slashEigenSubgroup f k := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hS
    · exact hT
  have hmem : γ ∈ slashEigenSubgroup f k := by
    apply hle
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  exact hmem

/-! ## The compiled laws in slash form -/

/-- The q-expansion as a function on the upper half-plane. -/
noncomputable def qForm (a : ℕ → ℂ) : ℍ → ℂ := fun τ => qSeries a (τ : ℂ)

/-- **The T-law in slash form**: eigenvalue `1` at weight `1`. -/
theorem qForm_T_eigen (a : ℕ → ℂ)
    (hT : ∀ τ : ℂ, qSeries a (τ + 1) = qSeries a τ) :
    qForm a ∣[(1 : ℤ)] ModularGroup.T = (1 : ℂ) • qForm a := by
  funext τ
  rw [ModularForm.SL_slash_apply, modular_T_smul]
  have hden : denom (ModularGroup.T) τ = 1 := by
    simp [ModularGroup.T, ModularGroup.denom_apply]
  rw [hden]
  simp only [Pi.smul_apply, smul_eq_mul, one_mul, one_zpow, mul_one, qForm]
  have hcoe : ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = 1 + (τ : ℂ) := by
    rw [coe_vadd]
    norm_num
  rw [hcoe, add_comm, hT]

/-- **The S-law in slash form**: eigenvalue `-i·ε⁻¹` at weight `1`. -/
theorem qForm_S_eigen (a : ℕ → ℂ) (ε : ℂ) (hε : ε ≠ 0)
    (hS : ∀ τ ∈ upperHalf,
      qSeries a τ = ε * ((-(Complex.I * τ))⁻¹ * qSeries a (-1 / τ))) :
    qForm a ∣[(1 : ℤ)] ModularGroup.S = (-Complex.I * ε⁻¹) • qForm a := by
  funext τ
  rw [ModularForm.SL_slash_apply, modular_S_smul, ModularGroup.denom_S]
  simp only [Pi.smul_apply, smul_eq_mul, qForm]
  have hτne : (τ : ℂ) ≠ 0 := ne_zero τ
  have hmem : (τ : ℂ) ∈ upperHalf := τ.2
  have hIτ : -(Complex.I * (τ : ℂ)) ≠ 0 := by
    simp only [neg_ne_zero]
    exact mul_ne_zero Complex.I_ne_zero hτne
  have h := hS (τ : ℂ) hmem
  have h2 : qSeries a (-1 / (τ : ℂ))
      = ε⁻¹ * (-(Complex.I * (τ : ℂ))) * qSeries a (τ : ℂ) := by
    have h3 := congrArg (fun z => ε⁻¹ * (-(Complex.I * (τ : ℂ))) * z) h
    rw [h3]
    field_simp
  have hinv : ((-(τ : ℂ))⁻¹) = -1 / (τ : ℂ) := by
    rw [inv_neg, neg_div, one_div]
  rw [hinv, h2]
  rw [zpow_neg_one]
  field_simp

/-! ## The headline -/

/-- **THE HECKE MODULARITY** — the q-expansion of an entire BV-package at the `Γℂ`
chart is a weight-`1` slash eigenform at every element of `SL(2,ℤ)`: a
slash-invariant form with multiplier, in Mathlib's own slash action. -/
theorem hecke_modularity (P : CoefficientSurface)
    (hdual : ∀ n : ℕ, P.adual n = P.a n)
    (ε : ℂ) (hε : ε ≠ 0)
    (pkg : KNicePackage (coefficientArithmetic P.a)
      (gammaCKernel 0 (by simp)).G
      (max (gammaCKernel 0 (by simp)).B0 ((P.A : ℝ) + 1)) ε)
    (σ : ℝ) (hσ : max (gammaCKernel 0 (by simp)).B0 ((P.A : ℝ) + 1) < σ)
    (C : ℝ) (hBV : ∀ z : ℂ, 1 - σ ≤ z.re → z.re ≤ σ → ‖pkg.lam z‖ ≤ C) :
    ∀ γ : SL(2, ℤ), ∃ v : ℂ, v ≠ 0 ∧
      qForm P.a ∣[(1 : ℤ)] γ = v • qForm P.a := by
  obtain ⟨hT, hS⟩ := hecke_identification P hdual ε pkg σ hσ C hBV
  exact slashEigen_all (qForm P.a) 1
    ⟨-Complex.I * ε⁻¹,
      mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (inv_ne_zero hε),
      qForm_S_eigen P.a ε hε hS⟩
    ⟨1, one_ne_zero, qForm_T_eigen P.a hT⟩

end CriticalLinePhasor.MultiplierPackaging

#print axioms CriticalLinePhasor.MultiplierPackaging.slashEigenSubgroup
#print axioms CriticalLinePhasor.MultiplierPackaging.slashEigen_all
#print axioms CriticalLinePhasor.MultiplierPackaging.qForm_T_eigen
#print axioms CriticalLinePhasor.MultiplierPackaging.qForm_S_eigen
#print axioms CriticalLinePhasor.MultiplierPackaging.hecke_modularity
