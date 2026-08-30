import RequestProject.WeightedTailPrimitive

/-!
# C3 batch 4 — attack A2.  The SECOND tail primitive (DECOMPOSITION B)

Decomposition A (`tmp/c3b4_A1.lean`) needs a *single* sign change of the tail primitive
`T`.  This file removes that hypothesis entirely.

The exact characterisation: for a nonnegative NONDECREASING weight `q`,
`∫_{(0,∞)} q·T ≥ 0` holds for every such `q` iff the SECOND tail primitive
`U(s) := ∫_{(s,∞)} T` is nonnegative at every `s ≥ 0`.  The mechanism is the layer
cake — write `q(r) = q(0) + ∫_0^r q′(s)ds`, swap, and every sign change of `T` beyond
the first is absorbed as long as the running tail integral never goes negative:

  `∫_{(0,∞)} q·T = q(0)·U(0) + ∫_{(0,∞)} q′(s)·U(s) ds`.

`U ≥ 0` is strictly weaker than `T ≥ 0` (refuted: `T(0,60) < 0`) and strictly weaker
than single crossing.  `U(0) = ∫_0^∞ T dr = L₁(x)/16`, so the `s = 0` instance of the
hypothesis is exactly `L₁ ≥ 0`.

Contents:
* `triG`, `inner_s`, `inner_r_shift`, `tail_shift_identity` — the layer-cake Fubini,
  written like `WeightedTailPrimitive` so no boundary term at infinity is ever needed.
* `triG_prod_integrable` — the product-integrability side condition REDUCED to the
  single scalar bound `∫_{r>0}(p r − p 0)·|V r| < ∞`.
* `weighted_second_tail_nonneg` — the abstract theorem.
* `gY'''`, `gY''_deriv_eq`, `gY'''_nonneg`, `gY''_contDiff` — the weight is `C¹` with a
  nonnegative derivative on `[0,∞)`, i.e. `g_y″` is nonneg and nondecreasing there.
* `sinh_pairing_nonneg_of_second_tail` — the composition with
  `weighted_tail_primitive_identity`.  THE deliverable of this file.
-/

open MeasureTheory Set

noncomputable section

namespace CriticalLinePhasor.C3B4B

/-! ## The test function `g_y(u) = u · sinh (2yu)` and its first three derivatives -/

/-- `g_y(u) = u · sinh (2 y u)`. -/
def gY (y u : ℝ) : ℝ := u * Real.sinh (2 * y * u)

/-- `g_y′(u) = sinh(2yu) + 2yu·cosh(2yu)`. -/
def gY' (y u : ℝ) : ℝ := Real.sinh (2 * y * u) + 2 * y * u * Real.cosh (2 * y * u)

/-- `g_y″(u) = 4y·cosh(2yu) + 4y²u·sinh(2yu)`. -/
def gY'' (y u : ℝ) : ℝ :=
  4 * y * Real.cosh (2 * y * u) + 4 * y ^ 2 * u * Real.sinh (2 * y * u)

/-- `g_y‴(u) = 12y²·sinh(2yu) + 8y³u·cosh(2yu)`. -/
def gY''' (y u : ℝ) : ℝ :=
  12 * y ^ 2 * Real.sinh (2 * y * u) + 8 * y ^ 3 * u * Real.cosh (2 * y * u)

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

/-- **The third derivative, as a function.**  So `deriv (deriv (deriv g))` is DISCHARGED,
not assumed. -/
theorem gY''_hasDerivAt (y u : ℝ) : HasDerivAt (gY'' y) (gY''' y u) u := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * y * t) (2 * y) u := by
    simpa using (hasDerivAt_id u).const_mul (2 * y)
  have hs : HasDerivAt (fun t : ℝ => Real.sinh (2 * y * t))
      (Real.cosh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_sinh (2 * y * u)).comp u hlin
  have hc : HasDerivAt (fun t : ℝ => Real.cosh (2 * y * t))
      (Real.sinh (2 * y * u) * (2 * y)) u :=
    (Real.hasDerivAt_cosh (2 * y * u)).comp u hlin
  have hlin2 : HasDerivAt (fun t : ℝ => 4 * y ^ 2 * t) (4 * y ^ 2) u := by
    simpa using (hasDerivAt_id u).const_mul (4 * y ^ 2)
  have h := (hc.const_mul (4 * y)).add (hlin2.mul hs)
  refine h.congr_deriv ?_
  simp only [gY''']
  ring

theorem gY_deriv_eq (y : ℝ) : deriv (gY y) = gY' y :=
  funext fun u => (gY_hasDerivAt y u).deriv

theorem gY_deriv2_eq (y : ℝ) : deriv (deriv (gY y)) = gY'' y := by
  rw [gY_deriv_eq]
  exact funext fun u => (gY'_hasDerivAt y u).deriv

theorem gY''_deriv_eq (y : ℝ) : deriv (gY'' y) = gY''' y :=
  funext fun u => (gY''_hasDerivAt y u).deriv

theorem gY_contDiff (y : ℝ) : ContDiff ℝ 2 (gY y) := by
  have h1 : ContDiff ℝ 2 (fun t : ℝ => 2 * y * t) := contDiff_const.mul contDiff_id
  exact contDiff_id.mul (Real.contDiff_sinh.comp h1)

theorem gY''_contDiff (y : ℝ) : ContDiff ℝ 1 (gY'' y) := by
  have h1 : ContDiff ℝ 1 (fun t : ℝ => 2 * y * t) := contDiff_const.mul contDiff_id
  have hc : ContDiff ℝ 1 (fun t : ℝ => 4 * y * Real.cosh (2 * y * t)) :=
    contDiff_const.mul (Real.contDiff_cosh.comp h1)
  have hs : ContDiff ℝ 1 (fun t : ℝ => 4 * y ^ 2 * t * Real.sinh (2 * y * t)) :=
    (contDiff_const.mul contDiff_id).mul (Real.contDiff_sinh.comp h1)
  exact hc.add hs

theorem gY_zero (y : ℝ) : gY y 0 = 0 := by simp [gY]

theorem gY_deriv_zero (y : ℝ) : deriv (gY y) 0 = 0 := by
  rw [gY_deriv_eq]; simp [gY']

theorem gY_deriv2_zero (y : ℝ) : gY'' y 0 = 4 * y := by simp [gY'']

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

theorem gY_deriv2_even (y u : ℝ) : gY'' y u = gY'' y (-u) := by
  simp only [gY'']
  rw [show 2 * y * -u = -(2 * y * u) by ring, Real.cosh_neg, Real.sinh_neg]
  ring

theorem gY_deriv2_nonneg_all {y : ℝ} (hy : 0 ≤ y) (u : ℝ) : 0 ≤ gY'' y u := by
  rcases le_total 0 u with hu | hu
  · exact gY_deriv2_nonneg hy hu
  · rw [gY_deriv2_even]; exact gY_deriv2_nonneg hy (by linarith)

/-- **`g_y‴ ≥ 0` on `[0,∞)`.**  Equivalently: the weight `g_y″` is NONDECREASING there.
This is what makes the layer-cake decomposition sign-definite. -/
theorem gY'''_nonneg {y : ℝ} (hy : 0 ≤ y) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ gY''' y u := by
  have hs : 0 ≤ Real.sinh (2 * y * u) := by
    rw [← Real.sinh_zero]
    exact Real.sinh_le_sinh.mpr (by positivity)
  have h1 : 0 ≤ 12 * y ^ 2 * Real.sinh (2 * y * u) := mul_nonneg (by positivity) hs
  have h2 : 0 ≤ 8 * y ^ 3 * u * Real.cosh (2 * y * u) := by
    have : 0 ≤ 8 * y ^ 3 * u := by positivity
    exact mul_nonneg this (Real.cosh_pos _).le
  simp only [gY''']
  linarith

/-! ## The layer-cake Fubini -/

/-- The shifted triangle integrand: `p′(s)·V(r)` on `{0 < s < r}`, zero elsewhere. -/
def triG (V p : ℝ → ℝ) (r s : ℝ) : ℝ := if s < r then deriv p s * V r else 0

/-- Inner `s`-integral: the fundamental theorem of calculus on `(0,r)`. -/
theorem inner_s (V p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioi (0 : ℝ), triG V p r s = (p r - p 0) * V r := by
  have hcont : Continuous (deriv p) := hp.continuous_deriv le_rfl
  have hdiff : Differentiable ℝ p := hp.differentiable (by norm_num)
  have hind : (fun s : ℝ => triG V p r s)
      = Set.indicator (Iio r) (fun s => deriv p s * V r) := by
    funext s; simp [triG, Set.indicator_apply, Set.mem_Iio]
  rw [hind, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hs : Ioi (0 : ℝ) ∩ Iio r = Ioo 0 r := by
    ext s; simp [Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
  rw [hs, MeasureTheory.integral_mul_const,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le]
  congr 1
  exact intervalIntegral.integral_deriv_eq_sub (fun x _ => hdiff x)
    (hcont.intervalIntegrable _ _)

/-- Inner `r`-integral: the tail of `V` above `s`. -/
theorem inner_r_shift (V p : ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ r in Ioi (0 : ℝ), triG V p r s = deriv p s * ∫ r in Ioi s, V r := by
  have hind : (fun r : ℝ => triG V p r s)
      = Set.indicator (Ioi s) (fun r => deriv p s * V r) := by
    funext r; simp [triG, Set.indicator_apply, Set.mem_Ioi]
  rw [hind, MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  have h2 : Ioi (0 : ℝ) ∩ Ioi s = Ioi s := by
    rw [Set.Ioi_inter_Ioi, max_eq_right hs.le]
  rw [h2]
  exact MeasureTheory.integral_const_mul _ _

/-- **THE LAYER-CAKE IDENTITY.**  `∫_{(0,∞)}(p − p 0)·V = ∫_{(0,∞)} p′(s)·(∫_{(s,∞)}V)`.
Pure real analysis; no boundary term at infinity. -/
theorem tail_shift_identity (V p : ℝ → ℝ) (hp : ContDiff ℝ 1 p)
    (hprod : Integrable (Function.uncurry (triG V p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) :
    ∫ r in Ioi (0 : ℝ), (p r - p 0) * V r
      = ∫ s in Ioi (0 : ℝ), deriv p s * ∫ r in Ioi s, V r := by
  have hswap := MeasureTheory.integral_integral_swap hprod
  have hL : ∫ r in Ioi (0 : ℝ), (∫ s in Ioi (0 : ℝ), triG V p r s)
      = ∫ r in Ioi (0 : ℝ), (p r - p 0) * V r :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun r hr => inner_s V p hp hr)
  have hR : ∫ s in Ioi (0 : ℝ), (∫ r in Ioi (0 : ℝ), triG V p r s)
      = ∫ s in Ioi (0 : ℝ), deriv p s * ∫ r in Ioi s, V r :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => inner_r_shift V p hs)
  rw [← hL, ← hR]
  exact hswap

/-! ## Product integrability of the layer-cake integrand -/

theorem triG_measurable {V p : ℝ → ℝ} (hV : Measurable V)
    (hp : Continuous (deriv p)) :
    Measurable (Function.uncurry (triG V p)) := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.2 < z.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have hf : Measurable (fun z : ℝ × ℝ => deriv p z.2 * V z.1) :=
    (hp.measurable.comp measurable_snd).mul (hV.comp measurable_fst)
  have heq : (Function.uncurry (triG V p)) = fun z : ℝ × ℝ =>
      if z.2 < z.1 then deriv p z.2 * V z.1 else 0 := by
    funext z; simp [Function.uncurry, triG]
  rw [heq]
  exact hf.ite hset measurable_const

/-- NB: the sign hypothesis is imposed only on `(0,∞)`, which is where the layer-cake
integral lives.  `g_y‴` is ODD, hence strictly negative on `(−∞,0)`, so a global
`0 ≤ deriv p` would be unprovable at the intended instance. -/
theorem inner_s_abs {V p : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
    (hpd : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ deriv p s) {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioi (0 : ℝ), ‖triG V p r s‖ = (p r - p 0) * |V r| := by
  have hcongr : ∀ s ∈ Ioi (0 : ℝ), ‖triG V p r s‖ = triG (fun t => |V t|) p r s := by
    intro s hs
    by_cases hlt : s < r
    · simp only [triG, if_pos hlt, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (hpd s hs)]
    · simp [triG, if_neg hlt]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
  exact inner_s (fun t => |V t|) p hp hr

/-- **Integrability, reduced.**  For `C¹` `p` with `p′ ≥ 0`, the product-integrability
side condition of the layer-cake identity follows from the single scalar bound
`∫_{r>0}(p r − p 0)·|V r| dr < ∞`. -/
theorem triG_prod_integrable {V p : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
    (hpd : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ deriv p s) (hV : Measurable V)
    (hint : IntegrableOn (fun r => (p r - p 0) * |V r|) (Ioi (0 : ℝ))) :
    Integrable (Function.uncurry (triG V p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hcont : Continuous (deriv p) := hp.continuous_deriv le_rfl
  have hmeas : AEStronglyMeasurable (Function.uncurry (triG V p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (triG_measurable hV hcont).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hmeas]
  constructor
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
    have hind : (fun s : ℝ => triG V p r s)
        = Set.indicator (Iio r) (fun s => deriv p s * V r) := by
      funext s; simp [triG, Set.indicator_apply, Set.mem_Iio]
    have hc : Continuous (fun s : ℝ => deriv p s * V r) := hcont.mul continuous_const
    have hIoo : IntegrableOn (fun s : ℝ => deriv p s * V r) (Ioo (0 : ℝ) r) :=
      (hc.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have hfin : IntegrableOn (Set.indicator (Iio r)
        (fun s => deriv p s * V r)) (Ioi (0 : ℝ)) := by
      rw [IntegrableOn, MeasureTheory.integrable_indicator_iff measurableSet_Iio,
        IntegrableOn, Measure.restrict_restrict measurableSet_Iio]
      have hs : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by
        ext s; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi]; tauto
      rw [hs]
      exact hIoo
    show Integrable (fun s => triG V p r s) _
    rw [hind]
    exact hfin
  · have hcongr : (fun r => ∫ s in Ioi (0 : ℝ), ‖Function.uncurry (triG V p) (r, s)‖)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => (p r - p 0) * |V r| := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with r hr
      exact inner_s_abs hp hpd hr
    exact (integrable_congr hcongr).mpr hint

/-! ## The abstract second-tail compensation theorem -/

/-- **WEIGHTED SECOND-TAIL COMPENSATION.**  If the SECOND tail primitive
`s ↦ ∫_{(s,∞)} V` is nonnegative for every `s ≥ 0`, and the weight `p` is `C¹` with
`p 0 ≥ 0` and `p′ ≥ 0` on `(0,∞)`, then `∫_{(0,∞)} p·V ≥ 0`.

No sign hypothesis whatsoever is placed on `V` itself: `V` may change sign arbitrarily
often.  This is what makes the statement survive the refutation of `T ≥ 0` and the
refutation of single crossing. -/
theorem weighted_second_tail_nonneg {V p : ℝ → ℝ} (hp : ContDiff ℝ 1 p)
    (hp0 : 0 ≤ p 0)
    (hpd : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ deriv p s)
    (hprod : Integrable (Function.uncurry (triG V p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hV : IntegrableOn V (Ioi (0 : ℝ)))
    (hpV : IntegrableOn (fun r => p r * V r) (Ioi (0 : ℝ)))
    (hU : ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ r in Ioi s, V r) :
    0 ≤ ∫ r in Ioi (0 : ℝ), p r * V r := by
  have hid := tail_shift_identity V p hp hprod
  have hsplit : ∫ r in Ioi (0 : ℝ), (p r - p 0) * V r
      = (∫ r in Ioi (0 : ℝ), p r * V r) - p 0 * ∫ r in Ioi (0 : ℝ), V r := by
    have he : (fun r => (p r - p 0) * V r) = fun r => p r * V r - p 0 * V r :=
      funext fun r => by ring
    rw [he, integral_sub hpV (hV.const_mul _), integral_const_mul]
  have h1 : 0 ≤ ∫ s in Ioi (0 : ℝ), deriv p s * ∫ r in Ioi s, V r :=
    setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (hpd s hs) (hU s (le_of_lt hs))
  have h2 : 0 ≤ p 0 * ∫ r in Ioi (0 : ℝ), V r := mul_nonneg hp0 (hU 0 le_rfl)
  rw [hid] at hsplit
  linarith

/-! ## Composition with the weighted-tail primitive identity -/

open WeightedTail in
theorem triF_measurable {W g : ℝ → ℝ} (hW : Measurable W)
    (hg2 : Continuous (deriv (deriv g))) :
    Measurable (Function.uncurry (triF W g)) := by
  have hset : MeasurableSet {z : ℝ × ℝ | z.2 < z.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have hf : Measurable (fun z : ℝ × ℝ =>
      (z.1 - z.2) * deriv (deriv g) z.2 * W z.1) :=
    ((measurable_fst.sub measurable_snd).mul (hg2.measurable.comp measurable_snd)).mul
      (hW.comp measurable_fst)
  have heq : (Function.uncurry (triF W g)) = fun z : ℝ × ℝ =>
      if z.2 < z.1 then (z.1 - z.2) * deriv (deriv g) z.2 * W z.1 else 0 := by
    funext z; simp [Function.uncurry, triF]
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

/-- The tail primitive of a weight `W`. -/
def tailT (W : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u in Ioi r, (u - r) * W u

/-- **THE DELIVERABLE.**  Nonnegativity of the SECOND tail primitive
`s ↦ ∫_{(s,∞)} T` at every `s ≥ 0` gives nonnegativity of the `sinh`-weighted pairing
at every `y ≥ 0` — with NO sign hypothesis on `T` itself.

At `s = 0` the hypothesis reads `∫_0^∞ T dr ≥ 0`, which in the `Ξ` chart is
`L₁(x)/16 ≥ 0`.  The refuted statements `T ≥ 0` (at `x=60`, `r=0`) and single crossing
are both strictly stronger than this and are not used. -/
theorem sinh_pairing_nonneg_of_second_tail {W : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hW : Measurable W)
    (hint : IntegrableOn (fun u => gY y u * |W u|) (Ioi (0 : ℝ)))
    (hprodG : Integrable (Function.uncurry (triG (tailT W) (gY'' y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hTint : IntegrableOn (tailT W) (Ioi (0 : ℝ)))
    (hqTint : IntegrableOn (fun r => gY'' y r * tailT W r) (Ioi (0 : ℝ)))
    (hU : ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ r in Ioi s, tailT W r) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * W u := by
  have hprod : Integrable (Function.uncurry (WeightedTail.triF W (gY y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine triF_prod_integrable (gY_contDiff y) (gY_zero y) (gY_deriv_zero y) ?_ hW hint
    intro r
    rw [gY_deriv2_eq]
    exact gY_deriv2_nonneg_all hy r
  rw [WeightedTail.weighted_tail_primitive_identity W (gY y) (gY_contDiff y)
    (gY_zero y) (gY_deriv_zero y) hprod, gY_deriv2_eq]
  show 0 ≤ ∫ r in Ioi (0 : ℝ), gY'' y r * tailT W r
  refine weighted_second_tail_nonneg (gY''_contDiff y) ?_ ?_ hprodG hTint hqTint hU
  · rw [gY_deriv2_zero]; linarith
  · intro s hs
    rw [gY''_deriv_eq]
    exact gY'''_nonneg hy (le_of_lt hs)

/-- The same, with the layer-cake product-integrability DISCHARGED from the scalar
bound `∫_{r>0}(g_y″(r) − 4y)·|T(r)| dr < ∞` plus measurability of the tail primitive. -/
theorem sinh_pairing_nonneg_of_second_tail' {W : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hW : Measurable W)
    (hint : IntegrableOn (fun u => gY y u * |W u|) (Ioi (0 : ℝ)))
    (hTmeas : Measurable (tailT W))
    (hscalar : IntegrableOn
      (fun r => (gY'' y r - 4 * y) * |tailT W r|) (Ioi (0 : ℝ)))
    (hTint : IntegrableOn (tailT W) (Ioi (0 : ℝ)))
    (hqTint : IntegrableOn (fun r => gY'' y r * tailT W r) (Ioi (0 : ℝ)))
    (hU : ∀ s : ℝ, 0 ≤ s → 0 ≤ ∫ r in Ioi s, tailT W r) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * W u := by
  refine sinh_pairing_nonneg_of_second_tail hy hW hint ?_ hTint hqTint hU
  refine triG_prod_integrable (gY''_contDiff y) ?_ hTmeas ?_
  · intro s hs
    rw [gY''_deriv_eq]
    exact gY'''_nonneg hy (le_of_lt hs)
  · have he : (fun r => (gY'' y r - gY'' y 0) * |tailT W r|)
        = fun r => (gY'' y r - 4 * y) * |tailT W r| := by
      funext r; rw [gY_deriv2_zero]
    rw [he]
    exact hscalar

end CriticalLinePhasor.C3B4B

section AxiomAudit
#print axioms CriticalLinePhasor.C3B4B.gY''_deriv_eq
#print axioms CriticalLinePhasor.C3B4B.gY'''_nonneg
#print axioms CriticalLinePhasor.C3B4B.inner_s
#print axioms CriticalLinePhasor.C3B4B.inner_r_shift
#print axioms CriticalLinePhasor.C3B4B.tail_shift_identity
#print axioms CriticalLinePhasor.C3B4B.triG_prod_integrable
#print axioms CriticalLinePhasor.C3B4B.weighted_second_tail_nonneg
#print axioms CriticalLinePhasor.C3B4B.sinh_pairing_nonneg_of_second_tail
#print axioms CriticalLinePhasor.C3B4B.sinh_pairing_nonneg_of_second_tail'
end AxiomAudit
