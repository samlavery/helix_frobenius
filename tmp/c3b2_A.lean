import Mathlib

open MeasureTheory intervalIntegral Set

/-! A1: pointwise Taylor step with integral remainder, order 2, base 0.
Route: build `G v = v·A v − B v` with `A,B` the two primitives of `g''`, show
`deriv G = deriv g`, then apply `integral_deriv_eq_sub` to BOTH `G` and `g`.
No `taylorWithinEval`, no `iteratedDerivWithin`, no constancy lemma. -/

theorem taylor2_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hg0 : g 0 = 0) (hg0' : deriv g 0 = 0) (u : ℝ) :
    g u = ∫ r in (0:ℝ)..u, (u - r) * deriv (deriv g) r := by
  have hg1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.mp hg).2.2
  have hcont2 : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hcont1 : Continuous (deriv g) := hg1.continuous
  have hdg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdg1 : Differentiable ℝ (deriv g) := hg1.differentiable (by norm_num)
  set A : ℝ → ℝ := fun v => ∫ r in (0:ℝ)..v, deriv (deriv g) r with hA
  set B : ℝ → ℝ := fun v => ∫ r in (0:ℝ)..v, r * deriv (deriv g) r with hB
  have hAd : ∀ v, HasDerivAt A (deriv (deriv g) v) v := fun v =>
    (hcont2.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hBd : ∀ v, HasDerivAt B (v * deriv (deriv g) v) v := fun v =>
    ((continuous_id'.mul hcont2).integral_hasStrictDerivAt 0 v).hasDerivAt
  -- A = deriv g
  have hAeq : ∀ v, A v = deriv g v := by
    intro v
    have h := intervalIntegral.integral_deriv_eq_sub (f := deriv g) (a := 0) (b := v)
      (fun x _ => hdg1 x) (hcont2.intervalIntegrable _ _)
    rw [hA]
    simp only []
    rw [h, hg0', sub_zero]
  set G : ℝ → ℝ := fun v => v * A v - B v with hG
  have hGd : ∀ v, HasDerivAt G (deriv g v) v := by
    intro v
    have h1 : HasDerivAt (fun w : ℝ => w * A w) (1 * A v + v * deriv (deriv g) v) v :=
      (hasDerivAt_id' (x := v)).mul (hAd v)
    have h2 := h1.sub (hBd v)
    have hval : 1 * A v + v * deriv (deriv g) v - v * deriv (deriv g) v = deriv g v := by
      rw [hAeq v]; ring
    rw [hval] at h2
    exact h2
  -- G u = g u, by FTC applied to both
  have hGdiff : Differentiable ℝ G := fun v => (hGd v).differentiableAt
  have hDG : deriv G = deriv g := funext fun v => (hGd v).deriv
  have hGint : ∫ t in (0:ℝ)..u, deriv G t = G u - G 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hGdiff x)
      (by rw [hDG]; exact hcont1.intervalIntegrable _ _)
  have hgint : ∫ t in (0:ℝ)..u, deriv g t = g u - g 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hdg x)
      (hcont1.intervalIntegrable _ _)
  have hG0 : G 0 = 0 := by simp [hG, hA, hB]
  have hEq : G u = g u := by
    rw [hDG, hgint, hG0, hg0] at hGint
    linarith
  -- unfold G
  have hi1 : IntervalIntegrable (fun r : ℝ => u * deriv (deriv g) r) volume 0 u :=
    (hcont2.const_mul u).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun r : ℝ => r * deriv (deriv g) r) volume 0 u :=
    (continuous_id.mul hcont2).intervalIntegrable _ _
  have hsplit : ∫ r in (0:ℝ)..u, (u - r) * deriv (deriv g) r = u * A u - B u := by
    calc ∫ r in (0:ℝ)..u, (u - r) * deriv (deriv g) r
        = ∫ r in (0:ℝ)..u, (u * deriv (deriv g) r - r * deriv (deriv g) r) :=
          intervalIntegral.integral_congr (fun r _ => by ring)
      _ = (∫ r in (0:ℝ)..u, u * deriv (deriv g) r)
            - ∫ r in (0:ℝ)..u, r * deriv (deriv g) r :=
          intervalIntegral.integral_sub hi1 hi2
      _ = u * A u - B u := by rw [intervalIntegral.integral_const_mul]
  rw [hsplit, ← hEq, hG]

/-! A2: the Fubini half on the triangle `0 < r < u`. -/

noncomputable def triF (W g : ℝ → ℝ) (u r : ℝ) : ℝ :=
  if r < u then (u - r) * deriv (deriv g) r * W u else 0

theorem inner_u (W g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0)
    (hg0' : deriv g 0 = 0) {u : ℝ} (hu : 0 < u) :
    ∫ r in Set.Ioi (0:ℝ), triF W g u r = g u * W u := by
  have hind : (fun r : ℝ => triF W g u r)
      = Set.indicator (Set.Iio u) (fun r => (u - r) * deriv (deriv g) r * W u) := by
    funext r; simp [triF, Set.indicator_apply, Set.mem_Iio]
  rw [hind, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hs : Set.Ioi (0:ℝ) ∩ Set.Iio u = Set.Ioo 0 u := by
    ext r; simp [Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]
  rw [hs, MeasureTheory.integral_mul_const,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hu.le, ← taylor2_zero hg hg0 hg0' u]

theorem inner_r (W g : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ u in Set.Ioi (0:ℝ), triF W g u r
      = deriv (deriv g) r * ∫ u in Set.Ioi r, (u - r) * W u := by
  have hind : (fun u : ℝ => triF W g u r)
      = Set.indicator (Set.Ioi r) (fun u => (u - r) * deriv (deriv g) r * W u) := by
    funext u; simp [triF, Set.indicator_apply, Set.mem_Ioi]
  rw [hind, MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  have hs : Set.Ioi (0:ℝ) ∩ Set.Ioi r = Set.Ioi r := by
    rw [Set.Ioi_inter_Ioi, max_eq_right hr.le]
  rw [hs]
  have hpt : ∀ u : ℝ, (u - r) * deriv (deriv g) r * W u
      = deriv (deriv g) r * ((u - r) * W u) := fun u => by ring
  simp_rw [hpt]
  exact MeasureTheory.integral_const_mul _ _

theorem weighted_tail_primitive_identity (W g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0) (hg0' : deriv g 0 = 0)
    (hprod : MeasureTheory.Integrable (Function.uncurry (triF W g))
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))))) :
    ∫ u in Set.Ioi (0:ℝ), g u * W u
      = ∫ r in Set.Ioi (0:ℝ),
          deriv (deriv g) r * ∫ u in Set.Ioi r, (u - r) * W u := by
  have hswap := MeasureTheory.integral_integral_swap hprod
  have hL : ∫ u in Set.Ioi (0:ℝ), (∫ r in Set.Ioi (0:ℝ), triF W g u r)
      = ∫ u in Set.Ioi (0:ℝ), g u * W u :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun u hu => inner_u W g hg hg0 hg0' hu)
  have hR : ∫ r in Set.Ioi (0:ℝ), (∫ u in Set.Ioi (0:ℝ), triF W g u r)
      = ∫ r in Set.Ioi (0:ℝ),
          deriv (deriv g) r * ∫ u in Set.Ioi r, (u - r) * W u :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun r hr => inner_r W g hr)
  rw [← hL, ← hR]
  exact hswap

#print axioms taylor2_zero
#print axioms inner_u
#print axioms inner_r
#print axioms weighted_tail_primitive_identity
