import Mathlib

/-!
# C3 batch 6, block A1 — the Macdonald function of imaginary order, from scratch

Adjudication batch 5 left as the "next literal Lean step":

> Instantiate `C3B5.A3.logDeriv_le_one` with a formal `z(A) = sqrt(A) * K_{i x}(A)` only
> after importing or proving a differentiable real-valued definition of `K_{i x}` and its
> modified-Bessel ODE.

SEARCH RECORD (obligation D), 2026-08-24, at source, before constructing anything:

* Mathlib: `Bessel`, `besselJ`, `besselK`, `Macdonald`, `modifiedBessel`, `cylinderFunction`,
  `Kelvin`, `hankel`, `Hankel` — **no definition of any Bessel function exists in Mathlib**
  (the only `Macdonald` hits are Atiyah–Macdonald citations in `RingTheory/Lasker.lean`).
* Repository: `Bessel`, `besselKix`, `Kix`, `macdonald`, `Real.cosh`, `exp (-A * Real.cosh`
  — the only hit is `RequestProject/BesselOrderLadder.lean`, whose `cosKernel n z`
  is the **order-`n` cosine channel** `∫_0^π cos(nθ)e^{-iz cos θ}dθ` (classically `J_n`),
  an integer-order oscillatory kernel on a compact interval.  It is not `K_{ix}` and
  cannot be specialized to it.

So the object is defined here, by its real integral representation on the half-line.

## Contents

* `kixTerm j x A w = (-cosh w)^j · e^{-A cosh w} · cos (x w)` — the `j`-th `A`-derivative
  of the integrand, as an explicit function.
* `kix j x A = ∫_{w>0} kixTerm j x A w` — so `kix 0` is `K_{ix}`, and `kix 1`, `kix 2` are
  the candidates for its first two `A`-derivatives (identified in block A2).
* `coshMaj j δ` — the explicit Gaussian majorant, from
  `e^w/2 ≤ cosh w ≤ e^w` and `1 + w + w²/2 ≤ e^w`, i.e.
  `cosh^j w · e^{-δ cosh w} ≤ e^{-δ/2}·exp((j − δ/2)w − (δ/4)w²)`
  for `w ≥ 0`.  Integrable by completing the square.
* `kixTerm_integrableOn`, `kix_bound`, `kix_tendsto_zero` — integrability, the explicit
  exponential decay bound `|kix j x A| ≤ C_j(δ)·e^{-(A-δ)}` for `A ≥ δ`, and the
  consequence that `√A · kix j x A → 0` at `+∞`.

SCOPE: nothing here mentions `Ξ`, zeros, positivity of a quadratic form, or RH.  It is the
construction of one classical special function and its elementary majorants.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Bessel

/-! ### 0. Elementary `cosh` bounds on the positive half-line -/

/-- `e^w / 2 ≤ cosh w`, on the whole line. -/
theorem exp_div_two_le_cosh (w : ℝ) : Real.exp w / 2 ≤ Real.cosh w := by
  rw [Real.cosh_eq]
  have h : 0 < Real.exp (-w) := Real.exp_pos _
  linarith

/-- `cosh w ≤ e^w` for `w ≥ 0`. -/
theorem cosh_le_exp {w : ℝ} (hw : 0 ≤ w) : Real.cosh w ≤ Real.exp w := by
  rw [Real.cosh_eq]
  have h : Real.exp (-w) ≤ Real.exp w := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- `1 ≤ cosh w`. -/
theorem one_le_cosh (w : ℝ) : 1 ≤ Real.cosh w := Real.one_le_cosh w

/-- **The quadratic minorant.**  `1 + w + w²/2 ≤ 2·cosh w` for `w ≥ 0`. -/
theorem quad_le_two_cosh {w : ℝ} (hw : 0 ≤ w) :
    1 + w + w ^ 2 / 2 ≤ 2 * Real.cosh w := by
  have h1 : 1 + w + w ^ 2 / 2 ≤ Real.exp w := Real.quadratic_le_exp_of_nonneg hw
  have h2 := exp_div_two_le_cosh w
  linarith

/-! ### 1. The integrand and the Macdonald function of imaginary order -/

/-- The `j`-th `A`-derivative of the Macdonald integrand:
`(-cosh w)^j · e^{-A cosh w} · cos(x w)`. -/
def kixTerm (j : ℕ) (x A w : ℝ) : ℝ :=
  (-Real.cosh w) ^ j * Real.exp (-(A * Real.cosh w)) * Real.cos (x * w)

/-- **`K_{ix}^{(j)}(A)`**, by the real integral representation on the half-line.
`kix 0 x A = K_{ix}(A) = ∫_0^∞ e^{-A cosh w} cos(x w) dw`. -/
def kix (j : ℕ) (x A : ℝ) : ℝ := ∫ w in Ioi (0 : ℝ), kixTerm j x A w

/-- The Macdonald function of imaginary order itself. -/
def besselKix (x A : ℝ) : ℝ := kix 0 x A

theorem besselKix_eq (x A : ℝ) :
    besselKix x A = ∫ w in Ioi (0 : ℝ), Real.exp (-(A * Real.cosh w)) * Real.cos (x * w) := by
  simp [besselKix, kix, kixTerm]

/-! ### 2. The Gaussian majorant -/

/-- The explicit majorant of `|kixTerm j x A w|` valid for every `A ≥ δ > 0` and `w ≥ 0`. -/
def coshMaj (j : ℕ) (δ w : ℝ) : ℝ :=
  Real.exp (-(δ / 2)) * Real.exp (((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2)

theorem coshMaj_nonneg (j : ℕ) (δ w : ℝ) : 0 ≤ coshMaj j δ w := by
  unfold coshMaj; positivity

/-- **The pointwise domination.**  For `0 < δ ≤ A` and `w ≥ 0`,
`cosh^j w · e^{-A cosh w} ≤ coshMaj j δ w`. -/
theorem cosh_pow_exp_le {j : ℕ} {A δ w : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) (hw : 0 ≤ w) :
    Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) ≤ coshMaj j δ w := by
  have hc1 : (1 : ℝ) ≤ Real.cosh w := one_le_cosh w
  have hc0 : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos hc1
  -- step 1: replace `A` by `δ`
  have hstep1 : Real.exp (-(A * Real.cosh w)) ≤ Real.exp (-(δ * Real.cosh w)) := by
    refine Real.exp_le_exp.mpr ?_
    have : δ * Real.cosh w ≤ A * Real.cosh w := by nlinarith
    linarith
  -- step 2: `cosh^j w ≤ e^{jw}`
  have hstep2 : Real.cosh w ^ j ≤ Real.exp ((j : ℝ) * w) := by
    have h := cosh_le_exp hw
    calc Real.cosh w ^ j ≤ Real.exp w ^ j := by
          exact pow_le_pow_left₀ hc0.le h j
      _ = Real.exp ((j : ℝ) * w) := by rw [← Real.exp_nat_mul]
  -- step 3: `-δ cosh w ≤ -δ/2 - (δ/2) w - (δ/4) w²`
  have hstep3 : -(δ * Real.cosh w) ≤ -(δ / 2) + (-(δ / 2)) * w - (δ / 4) * w ^ 2 := by
    have hq := quad_le_two_cosh hw
    nlinarith [hq, hδ]
  calc Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))
      ≤ Real.exp ((j : ℝ) * w) * Real.exp (-(δ * Real.cosh w)) := by
        exact mul_le_mul hstep2 hstep1 (Real.exp_pos _).le (Real.exp_pos _).le
    _ ≤ Real.exp ((j : ℝ) * w) *
          Real.exp (-(δ / 2) + (-(δ / 2)) * w - (δ / 4) * w ^ 2) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hstep3) (Real.exp_pos _).le
    _ = coshMaj j δ w := by
        unfold coshMaj
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- The absolute value of the integrand, before any majorant: the `cos` factor only ever
costs a factor `≤ 1`. -/
theorem kixTerm_abs_le_cosh (j : ℕ) (x A w : ℝ) :
    |kixTerm j x A w| ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by
  have hcos : |Real.cos (x * w)| ≤ 1 := Real.abs_cos_le_one _
  have hc0 : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos (one_le_cosh w)
  unfold kixTerm
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hc0.le,
    abs_of_nonneg (Real.exp_pos _).le]
  calc Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) * |Real.cos (x * w)|
      ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) * 1 := by
        refine mul_le_mul_of_nonneg_left hcos ?_
        positivity
    _ = Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by ring

/-- The absolute value of the integrand is dominated by the majorant. -/
theorem kixTerm_abs_le {j : ℕ} {x A δ w : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) (hw : 0 ≤ w) :
    |kixTerm j x A w| ≤ coshMaj j δ w :=
  (kixTerm_abs_le_cosh j x A w).trans (cosh_pow_exp_le hδ hA hw)

/-- **The majorant is integrable**, by completing the square. -/
theorem coshMaj_integrable (j : ℕ) {δ : ℝ} (hδ : 0 < δ) : Integrable (coshMaj j δ) := by
  obtain ⟨b, hbdef, hb0⟩ : ∃ b : ℝ, b = δ / 4 ∧ 0 < b := ⟨δ / 4, rfl, by linarith⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (j : ℝ) - δ / 2 := ⟨_, rfl⟩
  have hbne : b ≠ 0 := hb0.ne'
  have hg : Integrable (fun w : ℝ => Real.exp (-b * w ^ 2)) :=
    integrable_exp_neg_mul_sq hb0
  have hgt : Integrable (fun w : ℝ => Real.exp (-b * (w - c / (2 * b)) ^ 2)) := by
    simpa using hg.comp_sub_right (c / (2 * b))
  have hscaled := hgt.const_mul (Real.exp (-(δ / 2)) * Real.exp (c ^ 2 / (4 * b)))
  have hfun : coshMaj j δ = fun w : ℝ =>
      Real.exp (-(δ / 2)) * Real.exp (c ^ 2 / (4 * b)) *
        Real.exp (-b * (w - c / (2 * b)) ^ 2) := by
    funext w
    unfold coshMaj
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 1
    rw [Real.exp_eq_exp, hbdef, hcdef]
    field_simp
    ring
  rw [hfun]
  exact hscaled

theorem coshMaj_integrableOn (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (coshMaj j δ) (Ioi (0 : ℝ)) :=
  (coshMaj_integrable j hδ).integrableOn

/-! ### 3. Measurability and integrability of the integrand -/

theorem kixTerm_continuous (j : ℕ) (x A : ℝ) : Continuous (kixTerm j x A) := by
  unfold kixTerm
  exact (((Real.continuous_cosh.neg).pow j).mul
      ((Real.continuous_exp.comp ((continuous_const.mul Real.continuous_cosh).neg)))).mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))

theorem kixTerm_integrableOn (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (kixTerm j x A) (Ioi (0 : ℝ)) := by
  refine Integrable.mono (coshMaj_integrableOn j hA)
    (kixTerm_continuous j x A).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with w hw
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (coshMaj_nonneg j A w)]
  exact kixTerm_abs_le hA le_rfl (le_of_lt hw)

/-! ### 4. The exponential decay bound and the boundary behaviour -/

/-- The `j`-th moment constant `C_j(δ) = ∫_{w>0} cosh^j w · e^{-δ cosh w} dw`, written
through the majorant, is finite: this is the constant in the decay bound below. -/
def kixConst (j : ℕ) (δ : ℝ) : ℝ := ∫ w in Ioi (0 : ℝ), coshMaj j δ w

theorem kixConst_nonneg (j : ℕ) (δ : ℝ) : 0 ≤ kixConst j δ :=
  setIntegral_nonneg measurableSet_Ioi fun w _ => coshMaj_nonneg j δ w

/-- **The decay bound.**  For `0 < δ ≤ A`,
`|kix j x A| ≤ e^{-(A - δ)} · kixConst j δ`.

The mechanism is `cosh w ≥ 1`, so the excess exponential `e^{-(A-δ)cosh w}` is bounded by
`e^{-(A-δ)}` uniformly in `w`. -/
theorem kix_abs_le (j : ℕ) (x : ℝ) {A δ : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) :
    |kix j x A| ≤ Real.exp (-(A - δ)) * kixConst j δ := by
  have hA0 : 0 < A := lt_of_lt_of_le hδ hA
  have hint : IntegrableOn (kixTerm j x A) (Ioi (0 : ℝ)) := kixTerm_integrableOn j x hA0
  have hbound : IntegrableOn (fun w => Real.exp (-(A - δ)) * coshMaj j δ w) (Ioi (0 : ℝ)) :=
    (coshMaj_integrableOn j hδ).const_mul _
  have hpt : ∀ w ∈ Ioi (0 : ℝ),
      ‖kixTerm j x A w‖ ≤ Real.exp (-(A - δ)) * coshMaj j δ w := by
    intro w hw
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    have hc1 : (1 : ℝ) ≤ Real.cosh w := one_le_cosh w
    have hsplit : Real.exp (-(A * Real.cosh w))
        = Real.exp (-((A - δ) * Real.cosh w)) * Real.exp (-(δ * Real.cosh w)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hfac : Real.exp (-((A - δ) * Real.cosh w)) ≤ Real.exp (-(A - δ)) := by
      refine Real.exp_le_exp.mpr ?_
      have hAd : (0 : ℝ) ≤ A - δ := by linarith
      nlinarith
    have hbase : Real.cosh w ^ j * Real.exp (-(δ * Real.cosh w)) ≤ coshMaj j δ w :=
      cosh_pow_exp_le hδ le_rfl hw0
    have hcpos : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos hc1
    rw [Real.norm_eq_abs]
    refine (kixTerm_abs_le_cosh j x A w).trans ?_
    rw [hsplit]
    calc Real.cosh w ^ j *
          (Real.exp (-((A - δ) * Real.cosh w)) * Real.exp (-(δ * Real.cosh w)))
        = Real.exp (-((A - δ) * Real.cosh w)) *
            (Real.cosh w ^ j * Real.exp (-(δ * Real.cosh w))) := by ring
      _ ≤ Real.exp (-(A - δ)) * (Real.cosh w ^ j * Real.exp (-(δ * Real.cosh w))) := by
          refine mul_le_mul_of_nonneg_right hfac ?_
          positivity
      _ ≤ Real.exp (-(A - δ)) * coshMaj j δ w :=
          mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
  calc |kix j x A| = ‖∫ w in Ioi (0 : ℝ), kixTerm j x A w‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∫ w in Ioi (0 : ℝ), Real.exp (-(A - δ)) * coshMaj j δ w := by
        refine norm_integral_le_of_norm_le hbound ?_
        filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with w hw
        exact hpt w hw
    _ = Real.exp (-(A - δ)) * kixConst j δ := by
        rw [kixConst, integral_const_mul]

end C3B6.Bessel

section AxiomAudit
#print axioms C3B6.Bessel.exp_div_two_le_cosh
#print axioms C3B6.Bessel.quad_le_two_cosh
#print axioms C3B6.Bessel.cosh_pow_exp_le
#print axioms C3B6.Bessel.kixTerm_abs_le
#print axioms C3B6.Bessel.coshMaj_integrable
#print axioms C3B6.Bessel.kixTerm_integrableOn
#print axioms C3B6.Bessel.kix_abs_le
end AxiomAudit
