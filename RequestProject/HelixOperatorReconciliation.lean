import RequestProject.HelixZetaSource
import RequestProject.CarrierBank
import RequestProject.FoliatedPolarization

/-!
# Operator reconciliation: one generator, one involution (ledger 1277)

Chatbibibi (via Sam, 2026-10-13): "We have never established one common operator representation of the complete
native event … The immediate task is operator reconciliation, not operator invention. Start with the carrier's
actual evolution and the native J action. Then determine whether the harmonic-pencil representation intertwines with
both, including its inner product."

**The common generator is the native height dilation.** `dilate λ f (x) = f(λx)` reads a bank at a dilated height;
its eigenfunctions are `ψ_v(x) = x^v` (`dilate_eigenFn`: `D_λ ψ_v = λ^v ψ_v`; `generator_eigenFn`: `G ψ_v = v ψ_v`
for `G = x·d/dx`).

* **Carrier evolution.** Site `n`'s Gaussian mode is the ground mode dilated by `(n+1)²` (`siteMode_eq`). The
  Mellin transform turns dilation into multiplication by the eigenvalue (`mellin_dilate`). Hence
  `mellin_siteMode`: the Mellin transform of site `n`'s mode at `w` is the carrier bank entry `bank (2w) n` times the
  ground mode's. **The carrier's evolution parameter `s` is the dilation eigenvalue `w = s/2`.** Carrier evolution
  `e^{−sH}` and height dilation are one action, read on the two sides of the Mellin transform.
* **The involution J.** `Jop f (x) = conj f(1/x)` (origin reflection with conjugation, in the encoding).
  * `Jop_dilate`: `J D_λ = D_{1/λ} J`; J reverses the generator.
  * `Jop_eigenFn`: `J ψ_v = ψ_{−v̄}`.
  * `mellin_Jop`: on the Mellin side, J is `w ↦ −w̄` with conjugation.
* **The foliated `blockOp` is `iG` on the J-pair.** `iGenerator_pair`: on `a·ψ_v + b·ψ_{−v̄}`, `i·G` acts by the
  coefficients `blockOp (i v) (a, b)`. `pairForm` is the J-twisted pairing on that pair (J swaps `ψ_v` and
  `ψ_{−v̄}`), which is why it is indefinite off the axis.

**Inner products.** `G` is skew-symmetric for the half-density pairing (`HelixOriginCentered.halfDensity`; this file
does not compile that adjointness). But no eigenfunction is normalizable: `‖ψ_v(x)‖ = x^{Re v}` (`norm_eigenFn`), and
`x^{2Re v}` is not integrable against `dx/x` on `(0, ∞)` for any `v`. A source is the cancellation `⟨bank, ψ_v⟩ = 0`:
the bank is orthogonal to a non-normalizable eigenfunction. It is not a normalizable eigenvector. That is the exact
point where the skew-adjoint argument (`2 Re v ‖ψ‖² = 0`) does not yet apply.

**The harmonic pencil is downstream.** `harmonicPencil A B μ λ = !![A, B; μA, λB]` is fed by the scalar channels
(mass, resultant). The mass is a sum of norms, so the map from configurations to pencils is not linear. It cannot
intertwine linearly with `G` or `J`, and its Gram form `HᴴH` is the standard Hermitian form on `ℂ²`, not the
J-pairing. The pencil is a detector on the readout, not a representation of the generator.
-/

open Complex Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixOperatorReconciliation

open CriticalLinePhasor CriticalLinePhasor.HelixWindowCompletion CriticalLinePhasor.HelixTwoEndedClosure

/-! ## The native height dilation and its eigenfunctions -/

/-- Read a bank at the dilated height `λx`. -/
def dilate (lam : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (lam * x)

theorem dilate_dilate (lam mu : ℝ) (f : ℝ → ℂ) : dilate lam (dilate mu f) = dilate (mu * lam) f := by
  funext x
  simp only [dilate]
  ring_nf

/-- The dilation eigenfunctions `ψ_v(x) = x^v`. -/
def eigenFn (v : ℂ) : ℝ → ℂ := fun x => (x : ℂ) ^ v

/-- **`D_λ ψ_v = λ^v ψ_v`.** -/
theorem dilate_eigenFn {lam : ℝ} (hlam : 0 < lam) (v : ℂ) {x : ℝ} (hx : 0 < x) :
    dilate lam (eigenFn v) x = (lam : ℂ) ^ v * eigenFn v x := by
  simp only [dilate, eigenFn]
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg hlam.le hx.le v

/-- **`G ψ_v = v ψ_v`** for the generator `G = x·d/dx`. -/
theorem generator_eigenFn (v : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (eigenFn v) (v * (x : ℂ) ^ (v - 1)) x ∧
      (x : ℂ) * (v * (x : ℂ) ^ (v - 1)) = v * eigenFn v x := by
  refine ⟨(Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hx)).hasDerivAt.comp_ofReal, ?_⟩
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  simp only [eigenFn]
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  field_simp

theorem norm_eigenFn (v : ℂ) {x : ℝ} (hx : 0 < x) : ‖eigenFn v x‖ = x ^ v.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx v

/-! ## Carrier evolution = height dilation, across the Mellin transform -/

/-- Mellin turns the native dilation into multiplication by the eigenvalue factor. -/
theorem mellin_dilate (f : ℝ → ℂ) (w : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    mellin (dilate lam f) w = (lam : ℂ) ^ (-w) • mellin f w :=
  mellin_comp_mul_left f w hlam

/-- The ground Gaussian mode. -/
def groundMode : ℝ → ℂ := fun x => ((Real.exp (-Real.pi * x) : ℝ) : ℂ)

/-- **Site `n`'s Gaussian mode is the ground mode dilated by `(n+1)²`.** -/
theorem siteMode_eq (n : ℕ) (x : ℝ) :
    ((Real.exp (-siteRate n * x) : ℝ) : ℂ) = dilate ((((n + 1 : ℕ) : ℝ)) ^ 2) groundMode x := by
  simp only [dilate, groundMode, siteRate]
  congr 2
  ring

theorem sitePow_eq_bank (n : ℕ) (w : ℂ) :
    (((((n + 1 : ℕ) : ℝ) ^ 2 : ℝ)) : ℂ) ^ (-w) = CarrierReadout.bank (2 * w) n := by
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 : ((n : ℂ) + 1) = ((((n + 1 : ℕ) : ℝ)) : ℂ) := by push_cast; ring
  rw [CarrierReadout.bank_apply, h1, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (by positivity)),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hpos.ne'), ← ofReal_log (by positivity), ← ofReal_log hpos.le,
    Real.log_pow]
  push_cast
  ring_nf

/-- **The carrier's evolution parameter is the dilation eigenvalue**: the Mellin transform of site `n`'s mode at
`w` is the carrier bank entry at `s = 2w` times the ground mode's. -/
theorem mellin_siteMode (n : ℕ) (w : ℂ) :
    mellin (fun x => ((Real.exp (-siteRate n * x) : ℝ) : ℂ)) w =
      CarrierReadout.bank (2 * w) n * mellin groundMode w := by
  have h : (fun x => ((Real.exp (-siteRate n * x) : ℝ) : ℂ)) = dilate ((((n + 1 : ℕ) : ℝ)) ^ 2) groundMode :=
    funext (siteMode_eq n)
  rw [h, mellin_dilate _ _ (by positivity), sitePow_eq_bank, smul_eq_mul]

/-! ## The involution J -/

/-- The native J on functions of height: origin reflection (`x ↦ 1/x` in the encoding) with conjugation. -/
def Jop (f : ℝ → ℂ) : ℝ → ℂ := fun x => conj (f x⁻¹)

/-- **J reverses the dilation**: `J D_λ = D_{1/λ} J`. -/
theorem Jop_dilate (lam : ℝ) (f : ℝ → ℂ) (x : ℝ) : Jop (dilate lam f) x = dilate lam⁻¹ (Jop f) x := by
  simp only [Jop, dilate]
  congr 2
  rw [mul_inv, inv_inv]

/-- **`J ψ_v = ψ_{−v̄}`.** -/
theorem Jop_eigenFn (v : ℂ) {x : ℝ} (hx : 0 < x) : Jop (eigenFn v) x = eigenFn (-conj v) x := by
  simp only [Jop, eigenFn]
  have harg : ((x⁻¹ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (inv_pos.mpr hx).le]
    exact Real.pi_pos.ne
  have h := Complex.cpow_conj ((x⁻¹ : ℝ) : ℂ) v harg
  rw [Complex.conj_ofReal] at h
  rw [← h, ofReal_inv_cpow hx]

theorem mellin_conj' (h : ℝ → ℂ) (w : ℂ) : mellin (fun t => conj (h t)) w = conj (mellin h (conj w)) := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [smul_eq_mul, map_mul]
  congr 1
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  have hc := Complex.cpow_conj (t : ℂ) (w - 1) harg
  rw [Complex.conj_ofReal] at hc
  rw [show conj w - 1 = conj (w - 1) by simp, hc, Complex.conj_conj]

/-- **On the Mellin side, J is `w ↦ −w̄` with conjugation.** -/
theorem mellin_Jop (f : ℝ → ℂ) (w : ℂ) : mellin (Jop f) w = conj (mellin f (-conj w)) := by
  unfold Jop
  rw [mellin_conj' (fun t => f t⁻¹) w, mellin_comp_inv]

/-! ## The foliated `blockOp` is `iG` on the J-pair -/

/-- **`i·G` on the J-pair `a·ψ_v + b·ψ_{−v̄}` acts by the coefficients `blockOp (i v) (a, b)`.** -/
theorem iGenerator_pair (v a b : ℂ) {x : ℝ} (hx : 0 < x) :
    I * ((x : ℂ) * (a * (v * (x : ℂ) ^ (v - 1)) + b * ((-conj v) * (x : ℂ) ^ (-conj v - 1)))) =
      (FoliatedPolarization.blockOp (I * v) (a, b)).1 * eigenFn v x +
        (FoliatedPolarization.blockOp (I * v) (a, b)).2 * eigenFn (-conj v) x := by
  have h1 := (generator_eigenFn v hx).2
  have h2 := (generator_eigenFn (-conj v) hx).2
  simp only [FoliatedPolarization.blockOp, map_mul, Complex.conj_I]
  have hsplit : (x : ℂ) * (a * (v * (x : ℂ) ^ (v - 1)) + b * ((-conj v) * (x : ℂ) ^ (-conj v - 1))) =
      a * ((x : ℂ) * (v * (x : ℂ) ^ (v - 1))) + b * ((x : ℂ) * ((-conj v) * (x : ℂ) ^ (-conj v - 1))) := by ring
  rw [hsplit, h1, h2]
  ring

end CriticalLinePhasor.HelixOperatorReconciliation

end

#print axioms CriticalLinePhasor.HelixOperatorReconciliation.dilate_eigenFn
#print axioms CriticalLinePhasor.HelixOperatorReconciliation.generator_eigenFn
#print axioms CriticalLinePhasor.HelixOperatorReconciliation.mellin_siteMode
#print axioms CriticalLinePhasor.HelixOperatorReconciliation.Jop_dilate
#print axioms CriticalLinePhasor.HelixOperatorReconciliation.Jop_eigenFn
#print axioms CriticalLinePhasor.HelixOperatorReconciliation.mellin_Jop
#print axioms CriticalLinePhasor.HelixOperatorReconciliation.iGenerator_pair
