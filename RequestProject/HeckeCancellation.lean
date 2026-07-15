import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The GL(2) instance: smoothed coefficient cancellation from the fixed-kernel FE

The non-abelian rung of the cancellation target (`CoefficientCancellation.CancellationBound`).
For a level-one cusp form `f` of weight `k`, the vertical readout `x ↦ f(ix)` *is* the
exponentially-weighted coefficient sum `∑ a_n e^{-2πnx}` (Mathlib's `hasSum_qExpansion`, with
`a_0 = 0`), and Hecke's argument is two compiled facts:

* `hecke_inversion` — the fixed-kernel functional equation on the vertical line:
  `f(i/x) = (x·i)^k · f(ix)`, from the `S`-transformation — genuine modularity, the same law the
  converse seed consumed, not a synthesized completion, so the kernel-collapse pivot of the
  ledger does not apply here: the kernel is fixed and the coefficients do not cancel out;
* `CuspFormClass.exp_decay_atImInfty` — exponential decay of the cusp form.

Composed (`hecke_smoothed_cancellation`): the smoothed coefficient sums at parameter `x` are
`O(x^k e^{-2πx})` — exponentially small, where a random coefficient sequence of the same size
scales polynomially in `x`.  This is the cancellation content of modularity in one line, the
GL(2) analogue of the abelian orthogonality instance, with the weight explicit
(`ω(n) = e^{-2πn/x}`).  The sharp-cutoff form of the target is the Tauberian/contour step
(Chandrasekharan–Narasimhan) on top of this bound, named and not claimed.  No RH/GRH assumed or
proven.
-/

open UpperHalfPlane Complex Filter Asymptotics Matrix.SpecialLinearGroup
open scoped MatrixGroups Real

namespace CriticalLinePhasor.HeckeCancellation

/-- The vertical-line point `x·i ∈ ℍ`. -/
noncomputable def vert (x : ℝ) (hx : 0 < x) : ℍ :=
  ⟨(x : ℂ) * Complex.I, by simpa using hx⟩

@[simp] lemma vert_coe (x : ℝ) (hx : 0 < x) : (vert x hx : ℂ) = (x : ℂ) * Complex.I := rfl

@[simp] lemma vert_im (x : ℝ) (hx : 0 < x) : (vert x hx).im = x := by
  simp [vert, UpperHalfPlane.im]

/-- The image of the modular inversion `S` in `GL(2, ℝ)`. -/
noncomputable def Sgl : GL (Fin 2) ℝ := mapGL ℝ ModularGroup.S

lemma Sgl_mem : Sgl ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩

lemma Sgl_entries : (Sgl 1 0 : ℝ) = 1 ∧ (Sgl 1 1 : ℝ) = 0 ∧
    (Sgl 0 0 : ℝ) = 0 ∧ (Sgl 0 1 : ℝ) = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Sgl, ModularGroup.S]

lemma vert_ne_zero (x : ℝ) (hx : 0 < x) : ((x : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast hx.ne'
  · exact Complex.I_ne_zero

/-- The inversion carries the vertical line to itself, inverting the height. -/
lemma Sgl_smul_vert (x : ℝ) (hx : 0 < x) :
    Sgl • vert x hx = vert x⁻¹ (inv_pos.mpr hx) := by
  have hdet : (0 : ℝ) < Sgl.det.val := by
    simp [Sgl]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, vert_coe]
  obtain ⟨h10, h11, h00, h01⟩ := Sgl_entries
  rw [UpperHalfPlane.num, UpperHalfPlane.denom, h10, h11, h00, h01, vert_coe]
  push_cast
  rw [div_eq_iff (by simpa using vert_ne_zero x hx)]
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- **The fixed-kernel functional equation on the vertical line** (Hecke's inversion). -/
theorem hecke_inversion {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F 𝒮ℒ k]
    (f : F) (x : ℝ) (hx : 0 < x) :
    f (vert x⁻¹ (inv_pos.mpr hx)) = ((x : ℂ) * Complex.I) ^ k * f (vert x hx) := by
  rw [← Sgl_smul_vert x hx,
    SlashInvariantForm.slash_action_eqn' f Sgl_mem (vert x hx)]
  obtain ⟨h10, h11, _, _⟩ := Sgl_entries
  rw [h10, h11, vert_coe]
  push_cast
  ring_nf

/-- **Smoothed coefficient cancellation at GL(2).**  The vertical readout at height `1/x` — the
exponentially-weighted coefficient sum at parameter `x` — is `O(x^k e^{-2πx})`: exponentially
small, where a random sequence of the same coefficient size scales polynomially.  Modularity is
the entire mechanism: the fixed-kernel inversion plus cusp decay. -/
theorem hecke_smoothed_cancellation {k : ℤ}
    (f : CuspForm 𝒮ℒ k) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ hx : 0 < x,
      ‖f (vert x⁻¹ (inv_pos.mpr hx))‖ ≤ C * x ^ k * Real.exp (-(2 * π) * x) := by
  have hdecay := CuspFormClass.exp_decay_atImInfty (f := f) (h := 1) one_pos
    one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hdecay
  obtain ⟨C, hC⟩ := hdecay
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem] at hC
  obtain ⟨A, hA⟩ := hC
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (max A 1)] with x hxA hx
  have him : A ≤ (vert x hx).im := by
    rw [vert_im]
    exact le_trans (le_max_left A 1) hxA
  have hbound := hA (vert x hx) him
  simp only [Set.mem_setOf_eq] at hbound
  rw [hecke_inversion f x hx, norm_mul, norm_zpow]
  have hnorm : ‖(x : ℂ) * Complex.I‖ = x := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hx.le]
  rw [hnorm]
  calc x ^ k * ‖f (vert x hx)‖
      ≤ x ^ k * (C * ‖Real.exp (-2 * π * (vert x hx).im / 1)‖) := by
        have hxk : (0 : ℝ) ≤ x ^ k := zpow_nonneg hx.le k
        exact mul_le_mul_of_nonneg_left hbound hxk
    _ = C * x ^ k * Real.exp (-(2 * π) * x) := by
        rw [vert_im, Real.norm_of_nonneg (Real.exp_pos _).le,
          show (-2 * π * x / 1 : ℝ) = -(2 * π) * x by ring]
        ring

end CriticalLinePhasor.HeckeCancellation

#print axioms CriticalLinePhasor.HeckeCancellation.hecke_inversion
#print axioms CriticalLinePhasor.HeckeCancellation.hecke_smoothed_cancellation
