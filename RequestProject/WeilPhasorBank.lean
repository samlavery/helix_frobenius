import Mathlib
import RequestProject.WeilTestClass

/-!
# Track P1 — the Weil form on the prime phasor bank (ledger 537)

The lifted object. For a profile `g` (smooth, compact support) the phasor bank at height `τ` is the
family `Λ(n) n^{−½} e^{−iτ log n}`; the Weil form is the quadratic form

  `weilForm g = Σ'_ρ m_ρ · F_g(ρ) · conj(F_g(1 − conj ρ))`,   `F_g = laplaceTest g`,

which on the line reads `Σ_ρ m_ρ |ĝ(τ_ρ)|²`. Its expression on the bank comes from the compiled
explicit formula applied to the autocorrelation profile `G = g ⋆ g̃`, `g̃(x) = conj g(−x)`:

* `laplaceTest_conjReflect` — `F_{g̃}(s) = conj F_g(1 − conj s)`;
* `laplaceTest_convolution` — `F_{g ⋆ h} = F_g · F_h` (Fubini on compact supports);
* `weilForm_eq` — **the Weil form on the bank**:
  `weilForm g = (1/2π)[∫ F_G(b+it)E(b+it)dt + ∫ F_G(a+it)E(1−a−it)dt] − Σ_n Λ(n)n^{−½}(G(log n)+G(−log n))`.

The Archimedean part is the diagonal of the bank's Gram form, the prime part its off-diagonal
Toeplitz coefficients at the clock frequencies `±log n`. Positivity of `weilForm` for every `g` is
Weil's criterion; nothing here proves positivity.

No `sorry`, no `axiom`.
-/

open Complex MeasureTheory Filter Topology
open scoped Real Convolution ContDiff

noncomputable section

namespace CriticalLinePhasor.ContourArgument

/-- The reflected conjugate profile `g̃(x) = conj g(−x)`. -/
def conjReflect (g : ℝ → ℂ) (x : ℝ) : ℂ := (starRingEnd ℂ) (g (-x))

theorem conjReflect_continuous {g : ℝ → ℂ} (hg : Continuous g) : Continuous (conjReflect g) := by
  unfold conjReflect
  fun_prop

theorem conjReflect_hasCompactSupport {g : ℝ → ℂ} (hsupp : HasCompactSupport g) :
    HasCompactSupport (conjReflect g) := by
  have h1 : HasCompactSupport (fun x : ℝ => g (-x)) := hsupp.comp_homeomorph (Homeomorph.neg ℝ)
  exact h1.comp_left (map_zero (starRingEnd ℂ))

theorem conjReflect_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (conjReflect g) := by
  unfold conjReflect
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => g (-x)) := hg.comp contDiff_neg
  exact Complex.conjCLE.contDiff.comp h1

/-- `F_{g̃}(s) = conj F_g(1 − conj s)`. -/
theorem laplaceTest_conjReflect (g : ℝ → ℂ) (s : ℂ) :
    laplaceTest (conjReflect g) s = (starRingEnd ℂ) (laplaceTest g (1 - (starRingEnd ℂ) s)) := by
  unfold laplaceTest conjReflect
  rw [← integral_conj]
  have hR := integral_neg_eq_self (fun y : ℝ => (starRingEnd ℂ)
    (g y * Complex.exp ((1 - (starRingEnd ℂ) s - 1 / 2) * y))) volume
  rw [← hR]
  congr 1
  funext x
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_sub, map_one, map_div₀, map_ofNat, Complex.conj_conj,
    Complex.conj_ofReal]
  push_cast
  ring

/-- The pointwise convolution identity behind the Laplace product rule:
`((g e^{cx}) ⋆ (h e^{cx}))(x) = (g ⋆ h)(x) e^{cx}`. -/
theorem convolution_mul_exp (g h : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    ((fun y : ℝ => g y * Complex.exp (c * y)) ⋆[ContinuousLinearMap.mul ℝ ℂ]
        (fun y : ℝ => h y * Complex.exp (c * y))) x
      = (g ⋆[ContinuousLinearMap.mul ℝ ℂ] h) x * Complex.exp (c * x) := by
  rw [convolution_def, convolution_def, ← integral_mul_const]
  congr 1
  funext t
  simp only [ContinuousLinearMap.mul_apply']
  have : Complex.exp (c * t) * Complex.exp (c * ((x - t : ℝ) : ℂ)) = Complex.exp (c * x) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (g t * h (x - t)) * this

/-- **The Laplace product rule**: `F_{g ⋆ h} = F_g · F_h` for continuous compactly supported
profiles. -/
theorem laplaceTest_convolution {g h : ℝ → ℂ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hh : Continuous h) (hhs : HasCompactSupport h) (s : ℂ) :
    laplaceTest (g ⋆[ContinuousLinearMap.mul ℝ ℂ] h) s = laplaceTest g s * laplaceTest h s := by
  unfold laplaceTest
  have hgi : Integrable (fun y : ℝ => g y * Complex.exp ((s - 1 / 2) * y)) :=
    laplaceTest_integrand_integrable hg hgs s
  have hhi : Integrable (fun y : ℝ => h y * Complex.exp ((s - 1 / 2) * y)) :=
    laplaceTest_integrand_integrable hh hhs s
  have key := integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hgi hhi
  simp only [ContinuousLinearMap.mul_apply'] at key
  rw [← key]
  congr 1
  funext x
  exact (convolution_mul_exp g h (s - 1 / 2) x).symm

/-- The autocorrelation profile `G = g ⋆ g̃`. -/
def weilProfile (g : ℝ → ℂ) : ℝ → ℂ := g ⋆[ContinuousLinearMap.mul ℝ ℂ] conjReflect g

theorem weilProfile_hasCompactSupport {g : ℝ → ℂ} (hsupp : HasCompactSupport g) :
    HasCompactSupport (weilProfile g) :=
  HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℂ) hsupp
    (conjReflect_hasCompactSupport hsupp)

theorem weilProfile_contDiff {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hsupp : HasCompactSupport g) :
    ContDiff ℝ ∞ (weilProfile g) :=
  HasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (conjReflect_hasCompactSupport hsupp) hg.continuous.locallyIntegrable (conjReflect_contDiff hg)

/-- `F_G(s) = F_g(s) · conj F_g(1 − conj s)`. -/
theorem laplaceTest_weilProfile {g : ℝ → ℂ} (hg : Continuous g) (hsupp : HasCompactSupport g)
    (s : ℂ) :
    laplaceTest (weilProfile g) s
      = laplaceTest g s * (starRingEnd ℂ) (laplaceTest g (1 - (starRingEnd ℂ) s)) := by
  unfold weilProfile
  rw [laplaceTest_convolution hg hsupp (conjReflect_continuous hg)
    (conjReflect_hasCompactSupport hsupp), laplaceTest_conjReflect]

/-- **The Weil form on the phasor bank.** -/
def weilForm (g : ℝ → ℂ) : ℂ :=
  ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ)
    * (laplaceTest g ρ.val * (starRingEnd ℂ) (laplaceTest g (1 - (starRingEnd ℂ) ρ.val)))

/-- **The Weil form expressed on the bank** (compiled explicit formula applied to `G = g ⋆ g̃`). -/
theorem weilForm_eq {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hsupp : HasCompactSupport g)
    {a b : ℝ} (ha : a < 0) (hb : 1 < b) :
    weilForm g
      = (1 / (2 * π)) * ((∫ t : ℝ, laplaceTest (weilProfile g) (b + t * I) * weilArch (b + t * I))
          + (∫ t : ℝ, laplaceTest (weilProfile g) (a + t * I) * weilArch (1 - ((a : ℂ) + t * I))))
        - ∑' n : ℕ, primeWeight n * (weilProfile g (Real.log n) + weilProfile g (-Real.log n)) := by
  have h := weil_explicit_formula_smooth (weilProfile_contDiff hg hsupp)
    (weilProfile_hasCompactSupport hsupp) ha hb
  rw [← h]
  unfold weilForm
  congr 1
  funext ρ
  rw [laplaceTest_weilProfile hg.continuous hsupp]

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.laplaceTest_convolution
#print axioms CriticalLinePhasor.ContourArgument.weilForm_eq
