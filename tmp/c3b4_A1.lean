import RequestProject.WeightedTailPrimitive

/-!
# C3 batch 4 — attack A1.  Weighted single-crossing compensation (DECOMPOSITION A)

Uniform ramp positivity `T(r,x) ≥ 0` is FALSE: the four-precision Xi-route evaluation
gives `T(0,60) = -2.4411414711711282366e-36 < 0`.  So the batch-3 chain
`T ≥ 0 ⟹ target` is sound but its premise is refuted, and the analytic target moves to
a *compensated* inequality: the tail primitive is allowed to be negative on an initial
segment provided the later positive lobe outweighs it against an INCREASING weight.

This file is the abstract theorem, with no `Ξ`, no zeros, no spectral parameter:

  `weighted_single_crossing_nonneg` :
    `S ≤ 0` on `(0,r₀]`, `S ≥ 0` on `(r₀,∞)`, `∫_{(0,∞)} S ≥ 0`, `q` monotone on
    `[0,∞)` with `q 0 ≥ 0`  ⟹  `∫_{(0,∞)} q·S ≥ 0`.

The proof is the Chebyshev pivot: subtract the constant `q r₀`.  On `(0,r₀]` both
factors of `(q − q r₀)·S` are `≤ 0`; on `(r₀,∞)` both are `≥ 0`.  So the pivoted
integrand is pointwise nonnegative and the leftover `q r₀ · ∫S` is a product of two
nonnegative numbers.  Integrability enters only as the two honest hypotheses `hS`,
`hqS`; nothing is assumed about `q` beyond monotonicity (in particular `q` need not be
continuous, differentiable, or bounded).

Then `q := g_y″` for `g_y(u) = u·sinh(2yu)` is shown MONOTONE on `[0,∞)` for `y ≥ 0`
(`gY''_monotoneOn`), and the two are composed through
`weighted_tail_primitive_identity` into `sinh_pairing_nonneg_of_single_crossing`.
-/

open MeasureTheory Set

noncomputable section

namespace CriticalLinePhasor.C3B4

/-! ## The abstract compensation theorem -/

/-- **WEIGHTED SINGLE-CROSSING COMPENSATION.**  If `S` changes sign at most once on
`(0,∞)`, from `−` to `+`, has nonnegative total integral there, and `q` is nonnegative
at `0` and monotone on `[0,∞)`, then `∫ q·S ≥ 0`.

The hypothesis is strictly weaker than `S ≥ 0`: `S` may be negative on all of `(0,r₀]`.
Integrability is carried honestly by `hS` and `hqS`; no growth or continuity assumption
is made on `q`. -/
theorem weighted_single_crossing_nonneg {S q : ℝ → ℝ} {r0 : ℝ} (hr0 : 0 ≤ r0)
    (hSle : ∀ r ∈ Ioc (0 : ℝ) r0, S r ≤ 0)
    (hSge : ∀ r ∈ Ioi r0, 0 ≤ S r)
    (hq : MonotoneOn q (Ici (0 : ℝ)))
    (hq0 : 0 ≤ q 0)
    (hStot : 0 ≤ ∫ r in Ioi (0 : ℝ), S r)
    (hS : IntegrableOn S (Ioi (0 : ℝ)))
    (hqS : IntegrableOn (fun r => q r * S r) (Ioi (0 : ℝ))) :
    0 ≤ ∫ r in Ioi (0 : ℝ), q r * S r := by
  have hqr0 : 0 ≤ q r0 :=
    le_trans hq0 (hq (mem_Ici.mpr le_rfl) (mem_Ici.mpr hr0) hr0)
  -- the pivoted integrand is pointwise nonnegative
  have key : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ (q r - q r0) * S r := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    rcases le_total r r0 with h | h
    · have h1 : q r - q r0 ≤ 0 :=
        sub_nonpos.mpr (hq (mem_Ici.mpr hr'.le) (mem_Ici.mpr hr0) h)
      have h2 : S r ≤ 0 := hSle r ⟨hr', h⟩
      have h3 : 0 ≤ (-(q r - q r0)) * (-(S r)) :=
        mul_nonneg (neg_nonneg.mpr h1) (neg_nonneg.mpr h2)
      linarith [h3]
    · rcases eq_or_lt_of_le h with he | hlt
      · rw [← he]; simp
      · have h1 : 0 ≤ q r - q r0 :=
          sub_nonneg.mpr (hq (mem_Ici.mpr hr0) (mem_Ici.mpr hr'.le) h)
        exact mul_nonneg h1 (hSge r hlt)
  have hpos : 0 ≤ ∫ r in Ioi (0 : ℝ), (q r - q r0) * S r :=
    setIntegral_nonneg measurableSet_Ioi key
  have hcomb : (∫ r in Ioi (0 : ℝ), (q r - q r0) * S r)
      = (∫ r in Ioi (0 : ℝ), q r * S r) - q r0 * ∫ r in Ioi (0 : ℝ), S r := by
    have he : (fun r => (q r - q r0) * S r) = fun r => q r * S r - q r0 * S r :=
      funext fun r => by ring
    rw [he, integral_sub hqS (hS.const_mul _), integral_const_mul]
  linarith [mul_nonneg hqr0 hStot]

/-! ## The test function `g_y(u) = u · sinh (2yu)` and its monotone second derivative -/

/-- `g_y(u) = u · sinh (2 y u)`. -/
def gY (y u : ℝ) : ℝ := u * Real.sinh (2 * y * u)

/-- `g_y′(u) = sinh(2yu) + 2yu·cosh(2yu)`. -/
def gY' (y u : ℝ) : ℝ := Real.sinh (2 * y * u) + 2 * y * u * Real.cosh (2 * y * u)

/-- `g_y″(u) = 4y·cosh(2yu) + 4y²u·sinh(2yu)`. -/
def gY'' (y u : ℝ) : ℝ :=
  4 * y * Real.cosh (2 * y * u) + 4 * y ^ 2 * u * Real.sinh (2 * y * u)

theorem gY_hasDerivAt (y u : ℝ) : HasDerivAt (gY y) (gY' y u) u := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * y * t) (2 * y) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * y)
  have hs : HasDerivAt (fun t : ℝ => Real.sinh (2 * y * t))
      (Real.cosh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_sinh (2 * y * u)).comp u hlin
  have h := (hasDerivAt_id u).mul hs
  refine h.congr_deriv ?_
  simp only [gY', id_eq]
  ring

theorem gY'_hasDerivAt (y u : ℝ) : HasDerivAt (gY' y) (gY'' y u) u := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * y * t) (2 * y) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * y)
  have hs : HasDerivAt (fun t : ℝ => Real.sinh (2 * y * t))
      (Real.cosh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_sinh (2 * y * u)).comp u hlin
  have hc : HasDerivAt (fun t : ℝ => Real.cosh (2 * y * t))
      (Real.sinh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_cosh (2 * y * u)).comp u hlin
  have h := hs.add (hlin.mul hc)
  refine h.congr_deriv ?_
  simp only [gY'']
  ring

theorem gY_deriv_eq (y : ℝ) : deriv (gY y) = gY' y :=
  funext fun u => (gY_hasDerivAt y u).deriv

theorem gY_deriv2_eq (y : ℝ) : deriv (deriv (gY y)) = gY'' y := by
  rw [gY_deriv_eq]
  exact funext fun u => (gY'_hasDerivAt y u).deriv

theorem gY_contDiff (y : ℝ) : ContDiff ℝ 2 (gY y) := by
  have h1 : ContDiff ℝ 2 (fun t : ℝ => 2 * y * t) := contDiff_const.mul contDiff_id
  exact contDiff_id.mul (Real.contDiff_sinh.comp h1)

theorem gY_zero (y : ℝ) : gY y 0 = 0 := by simp [gY]

theorem gY_deriv_zero (y : ℝ) : deriv (gY y) 0 = 0 := by
  rw [gY_deriv_eq]; simp [gY']

theorem gY_deriv2_nonneg {y : ℝ} (hy : 0 ≤ y) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ gY'' y u := by
  have h1 : 0 ≤ 4 * y * Real.cosh (2 * y * u) :=
    mul_nonneg (by linarith) (Real.cosh_pos _).le
  have h2 : 0 ≤ 4 * y ^ 2 * u * Real.sinh (2 * y * u) := by
    have hs : 0 ≤ Real.sinh (2 * y * u) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr (by positivity)
    exact mul_nonneg (by positivity) hs
  simp only [gY'']
  linarith

/-- `g_y″` is EVEN, so the sign statement on `[0,∞)` extends to all of `ℝ`. -/
theorem gY_deriv2_even (y u : ℝ) : gY'' y u = gY'' y (-u) := by
  simp only [gY'']
  rw [show 2 * y * -u = -(2 * y * u) by ring, Real.cosh_neg, Real.sinh_neg]
  ring

theorem gY_deriv2_nonneg_all {y : ℝ} (hy : 0 ≤ y) (u : ℝ) : 0 ≤ gY'' y u := by
  rcases le_total 0 u with hu | hu
  · exact gY_deriv2_nonneg hy hu
  · rw [gY_deriv2_even]; exact gY_deriv2_nonneg hy (by linarith)

/-- **THE WEIGHT IS MONOTONE.**  `g_y″(u) = 4y·cosh(2yu) + 4y²u·sinh(2yu)` is
nondecreasing on `[0,∞)` whenever `y ≥ 0`.  This is the hypothesis that
`weighted_single_crossing_nonneg` consumes, and it is what makes the compensation
argument available at all: the weight DOWN-weights the early negative lobe of the tail
primitive and UP-weights the late positive lobe. -/
theorem gY''_monotoneOn {y : ℝ} (hy : 0 ≤ y) : MonotoneOn (gY'' y) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  have ha0 : (0 : ℝ) ≤ a := ha
  have hb0 : (0 : ℝ) ≤ b := hb
  have hya : (0 : ℝ) ≤ 2 * y * a := by positivity
  have hyb : (0 : ℝ) ≤ 2 * y * b := by positivity
  have hle : 2 * y * a ≤ 2 * y * b := by nlinarith
  have hcosh : Real.cosh (2 * y * a) ≤ Real.cosh (2 * y * b) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hya, abs_of_nonneg hyb]
    exact hle
  have hsinh : Real.sinh (2 * y * a) ≤ Real.sinh (2 * y * b) :=
    Real.sinh_le_sinh.mpr hle
  have hsa : 0 ≤ Real.sinh (2 * y * a) := by
    rw [← Real.sinh_zero]; exact Real.sinh_le_sinh.mpr hya
  have hmul : a * Real.sinh (2 * y * a) ≤ b * Real.sinh (2 * y * b) :=
    mul_le_mul hab hsinh hsa hb0
  have c1 : 4 * y * Real.cosh (2 * y * a) ≤ 4 * y * Real.cosh (2 * y * b) :=
    mul_le_mul_of_nonneg_left hcosh (by linarith)
  have c2 : 4 * y ^ 2 * (a * Real.sinh (2 * y * a))
      ≤ 4 * y ^ 2 * (b * Real.sinh (2 * y * b)) :=
    mul_le_mul_of_nonneg_left hmul (by positivity)
  simp only [gY'']
  nlinarith [c1, c2]

/-! ## Product integrability of the triangle integrand

`RequestProject.WeightedTailPrimitive` exports only `triF`, `inner_u`, `inner_r` and the
identity itself; the integrability reduction lives in the (unbuilt) sinh-bridge file, so
it is reproduced here so that this scratch file is self-contained. -/

open WeightedTail in
theorem triF_measurable {W g : ℝ → ℝ} (hW : Measurable W)
    (hg2 : Continuous (deriv (deriv g))) :
    Measurable (Function.uncurry (triF W g)) := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have hf : Measurable (fun p : ℝ × ℝ =>
      (p.1 - p.2) * deriv (deriv g) p.2 * W p.1) :=
    ((measurable_fst.sub measurable_snd).mul (hg2.measurable.comp measurable_snd)).mul
      (hW.comp measurable_fst)
  have heq : (Function.uncurry (triF W g)) = fun p : ℝ × ℝ =>
      if p.2 < p.1 then (p.1 - p.2) * deriv (deriv g) p.2 * W p.1 else 0 := by
    funext p; simp [Function.uncurry, triF]
  rw [heq]
  exact hf.ite hset measurable_const

open WeightedTail in
theorem inner_u_abs {W g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0) (hg2 : ∀ r, 0 ≤ deriv (deriv g) r) {u : ℝ} (hu : 0 < u) :
    ∫ r in Ioi (0 : ℝ), ‖triF W g u r‖ = g u * |W u| := by
  have hpt : (fun r => ‖triF W g u r‖) = fun r => triF (fun t => |W t|) g u r := by
    funext r
    by_cases hr : r < u
    · have h1 : (0 : ℝ) ≤ u - r := by linarith
      simp only [triF, if_pos hr, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg h1, abs_of_nonneg (hg2 r)]
    · simp [triF, if_neg hr]
  rw [hpt]
  exact inner_u (fun t => |W t|) g hg hg0 hg0' hu

open WeightedTail in
/-- **Φ-decay integrability, reduced.**  For `C²` `g` vanishing to second order with
`g″ ≥ 0`, the product-integrability side condition reduces to the single scalar bound
`∫_{u>0} g u·|W u| < ∞`, because `∫_0^u (u−r)g″(r)dr = g u`. -/
theorem triF_prod_integrable {W g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0) (hg2 : ∀ r, 0 ≤ deriv (deriv g) r)
    (hW : Measurable W)
    (hint : IntegrableOn (fun u => g u * |W u|) (Ioi (0 : ℝ))) :
    Integrable (Function.uncurry (triF W g))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hg1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hcont2 : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hmeas : AEStronglyMeasurable (Function.uncurry (triF W g))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (triF_measurable hW hcont2).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
    have hind : (fun r : ℝ => triF W g u r)
        = Set.indicator (Iio u) (fun r => (u - r) * deriv (deriv g) r * W u) := by
      funext r; simp [triF, Set.indicator_apply, Set.mem_Iio]
    have hcont : Continuous (fun r : ℝ => (u - r) * deriv (deriv g) r * W u) :=
      ((continuous_const.sub continuous_id).mul hcont2).mul continuous_const
    have hIoo : IntegrableOn (fun r : ℝ => (u - r) * deriv (deriv g) r * W u)
        (Ioo (0 : ℝ) u) :=
      (hcont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have hfin : IntegrableOn (Set.indicator (Iio u)
        (fun r => (u - r) * deriv (deriv g) r * W u)) (Ioi (0 : ℝ)) := by
      rw [IntegrableOn, MeasureTheory.integrable_indicator_iff measurableSet_Iio,
        IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio u ∩ Ioi (0 : ℝ) = Ioo 0 u := by
        ext r; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi]; tauto
      rw [hs]
      exact hIoo
    show Integrable (fun r => triF W g u r) _
    rw [hind]
    exact hfin
  · have hcongr : (fun u => ∫ r in Ioi (0 : ℝ), ‖Function.uncurry (triF W g) (u, r)‖)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u => g u * |W u| := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
      exact inner_u_abs hg hg0 hg0' hg2 hu
    exact (integrable_congr hcongr).mpr hint

/-! ## Composition: the compensated sinh pairing -/

/-- The tail primitive of a weight `W`. -/
def tailT (W : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u in Ioi r, (u - r) * W u

/-- **THE COMPENSATED SINH PAIRING.**  The batch-3 hypothesis `T ≥ 0` is replaced by the
strictly weaker triple: `T ≤ 0` on `(0,r₀]`, `T ≥ 0` on `(r₀,∞)`, and `∫_{(0,∞)} T ≥ 0`.

This is the exact shape measured at `x = 60`: `T(0,60) < 0`, one sign change in
`(0.2,0.3]`, and `∫_0^∞ T dr = L₁(60)/16 > 0`.  So the refutation of uniform ramp
positivity does not touch this statement. -/
theorem sinh_pairing_nonneg_of_single_crossing {W : ℝ → ℝ} {y r0 : ℝ}
    (hy : 0 ≤ y) (hr0 : 0 ≤ r0)
    (hW : Measurable W)
    (hint : IntegrableOn (fun u => gY y u * |W u|) (Ioi (0 : ℝ)))
    (hTint : IntegrableOn (tailT W) (Ioi (0 : ℝ)))
    (hqTint : IntegrableOn (fun r => gY'' y r * tailT W r) (Ioi (0 : ℝ)))
    (hTle : ∀ r ∈ Ioc (0 : ℝ) r0, tailT W r ≤ 0)
    (hTge : ∀ r ∈ Ioi r0, 0 ≤ tailT W r)
    (hTtot : 0 ≤ ∫ r in Ioi (0 : ℝ), tailT W r) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * W u := by
  have hprod : Integrable (Function.uncurry (WeightedTail.triF W (gY y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine triF_prod_integrable (gY_contDiff y) (gY_zero y)
      (gY_deriv_zero y) ?_ hW hint
    intro r
    rw [gY_deriv2_eq]
    exact gY_deriv2_nonneg_all hy r
  rw [WeightedTail.weighted_tail_primitive_identity W (gY y) (gY_contDiff y)
    (gY_zero y) (gY_deriv_zero y) hprod, gY_deriv2_eq]
  exact weighted_single_crossing_nonneg hr0 hTle hTge (gY''_monotoneOn hy)
    (gY_deriv2_nonneg hy le_rfl) hTtot hTint hqTint

end CriticalLinePhasor.C3B4

section AxiomAudit
#print axioms CriticalLinePhasor.C3B4.weighted_single_crossing_nonneg
#print axioms CriticalLinePhasor.C3B4.gY_deriv2_eq
#print axioms CriticalLinePhasor.C3B4.gY_deriv2_even
#print axioms CriticalLinePhasor.C3B4.gY_deriv2_nonneg_all
#print axioms CriticalLinePhasor.C3B4.gY''_monotoneOn
#print axioms CriticalLinePhasor.C3B4.sinh_pairing_nonneg_of_single_crossing
end AxiomAudit
