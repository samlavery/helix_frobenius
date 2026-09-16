import RequestProject.ZetaContourArgument

/-!
# The Eisenstein reflection coefficient of `SL₂(ℤ)` as a ratio of completed zetas

Scattering frame (RH_LEDGER 773, 778).  The constant term of the real-analytic Eisenstein series of
`SL₂(ℤ)` is `y^s + φ(s)·y^{1−s}` with `φ(s) = √π·Γ(s−½)·ζ(2s−1) / (Γ(s)·ζ(2s))`.  Through Mathlib's
completed zeta `Λ(w) = Gammaℝ(w)·ζ(w)` (`riemannZeta_def_of_ne_zero`) this is exactly
`φ(s) = Λ(2s−1)/Λ(2s)`, with no polynomial factor (the ratio `ξ(2s−1)/ξ(2s)` of the record differs
from it by `(s−1)/s`; ledger 773, line 4).

Compiled here: the definition; the Gamma–zeta form; the archimedean ratio
`Gammaℝ(2s−1)/Gammaℝ(2s) = π^{1/2}·Γ(s−½)/Γ(s)`; the functional equation `φ(1−s) = φ(s)⁻¹`
(unconditional, from `completedRiemannZeta_one_sub`); conjugation symmetry of `Λ`; and unimodularity
`‖φ(½+ir)‖ = 1` on the unitary line wherever `Λ(1+2ir) ≠ 0`.  The poles of `φ` in `0 < Re s < ½` are
the points `ρ/2` at the nontrivial zeros: the resonances of the modular surface (Faddeev–Pavlov,
Lax–Phillips; ledger 773).  This file is the algebra of the frame; the wave equation, the
incoming/outgoing subspaces, the semigroup and its generator are not compiled.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.ScatteringFrame

/-- The Eisenstein reflection coefficient `φ(s) = Λ(2s−1)/Λ(2s)`, `Λ = completedRiemannZeta`. -/
def eisReflect (s : ℂ) : ℂ := completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)

/-- `Λ(w) = Gammaℝ(w)·ζ(w)` away from `w = 0` and the zeros of `Gammaℝ`. -/
theorem completedRiemannZeta_eq_gammaR_mul {w : ℂ} (h0 : w ≠ 0) (hg : Gammaℝ w ≠ 0) :
    completedRiemannZeta w = Gammaℝ w * riemannZeta w := by
  rw [riemannZeta_def_of_ne_zero h0]
  field_simp

/-- The Gamma–zeta form of the reflection coefficient. -/
theorem eisReflect_eq_gammaR (s : ℂ) (h0 : 2 * s ≠ 0) (h1 : 2 * s - 1 ≠ 0)
    (hg0 : Gammaℝ (2 * s) ≠ 0) (hg1 : Gammaℝ (2 * s - 1) ≠ 0) :
    eisReflect s = (Gammaℝ (2 * s - 1) * riemannZeta (2 * s - 1)) /
      (Gammaℝ (2 * s) * riemannZeta (2 * s)) := by
  unfold eisReflect
  rw [completedRiemannZeta_eq_gammaR_mul h1 hg1, completedRiemannZeta_eq_gammaR_mul h0 hg0]

/-- The archimedean ratio: `Gammaℝ(2s−1)/Gammaℝ(2s) = π^{1/2}·Γ(s−½)/Γ(s)`. -/
theorem gammaR_two_sub_one_div_gammaR_two (s : ℂ) :
    Gammaℝ (2 * s - 1) / Gammaℝ (2 * s) =
      (Real.pi : ℂ) ^ ((1 : ℂ) / 2) * Gamma (s - 1 / 2) / Gamma s := by
  simp only [Gammaℝ_def]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (2 * s - 1) / 2 = s - 1 / 2 := by ring
  have h2 : (2 * s) / 2 = s := by ring
  have h3 : -(2 * s - 1) / 2 - (-(2 * s) / 2) = (1 : ℂ) / 2 := by ring
  rw [h1, h2, mul_div_mul_comm, ← cpow_sub _ _ hpi, h3, mul_div_assoc]

/-- Functional equation, unconditional: `φ(1−s) = φ(s)⁻¹`. -/
theorem eisReflect_one_sub (s : ℂ) : eisReflect (1 - s) = (eisReflect s)⁻¹ := by
  unfold eisReflect
  have h1 : 2 * (1 - s) - 1 = 1 - 2 * s := by ring
  have h2 : 2 * (1 - s) = 1 - (2 * s - 1) := by ring
  rw [h1, h2, completedRiemannZeta_one_sub (2 * s), completedRiemannZeta_one_sub (2 * s - 1),
    inv_div]

/-- `φ(1−s)·φ(s) = 1` wherever both completed zetas are nonzero. -/
theorem eisReflect_one_sub_mul (s : ℂ) (h0 : completedRiemannZeta (2 * s) ≠ 0)
    (h1 : completedRiemannZeta (2 * s - 1) ≠ 0) : eisReflect (1 - s) * eisReflect s = 1 := by
  rw [eisReflect_one_sub]
  apply inv_mul_cancel₀
  unfold eisReflect
  exact div_ne_zero h1 h0

/-- Conjugation symmetry of the completed zeta, from the entire version's symmetry. -/
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rw [completedRiemannZeta_eq (conj s), completedRiemannZeta_eq s,
    CriticalLinePhasor.ContourArgument.completedRiemannZeta₀_conj]
  simp only [map_sub, map_div₀, map_one]

/-- On the unitary line `s = ½ + ir`: `φ(s) = conj(Λ(1+2ir)) / Λ(1+2ir)`. -/
theorem eisReflect_line (r : ℝ) :
    eisReflect (1 / 2 + I * r) =
      conj (completedRiemannZeta (1 + 2 * I * r)) / completedRiemannZeta (1 + 2 * I * r) := by
  unfold eisReflect
  have h1 : 2 * (1 / 2 + I * (r : ℂ)) - 1 = 2 * I * r := by ring
  have h2 : 2 * (1 / 2 + I * (r : ℂ)) = 1 + 2 * I * r := by ring
  have h3 : conj (1 + 2 * I * (r : ℂ)) = 1 - 2 * I * r := by
    simp only [map_add, map_mul, map_one, conj_I, conj_ofReal, map_ofNat]
    ring
  rw [h1, h2, ← completedRiemannZeta_one_sub (2 * I * r), ← h3, completedRiemannZeta_conj]

/-- Unimodularity on the unitary line: `‖φ(½+ir)‖ = 1` wherever `Λ(1+2ir) ≠ 0`. -/
theorem norm_eisReflect_line (r : ℝ) (h : completedRiemannZeta (1 + 2 * I * r) ≠ 0) :
    ‖eisReflect (1 / 2 + I * r)‖ = 1 := by
  rw [eisReflect_line, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr h)]

end CriticalLinePhasor.ScatteringFrame

end

#print axioms CriticalLinePhasor.ScatteringFrame.norm_eisReflect_line
#print axioms CriticalLinePhasor.ScatteringFrame.eisReflect_one_sub_mul
#print axioms CriticalLinePhasor.ScatteringFrame.gammaR_two_sub_one_div_gammaR_two
