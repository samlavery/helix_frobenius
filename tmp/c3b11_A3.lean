import c3b11_A2

/-!
# C3 batch 11, block A3 — attacks on the four-moment leaf

`c3b11_A2` reduced the open target to an explicit bilinear form in four one-dimensional
moments of the theta kernel:

  `∫_{(0,∞)} u sinh(2yu) C(x,u) du = ¼ (A·A' + B·B')`,
  `A = cosMom (wQ y) x`, `A' = cosMom (wP y) x`, `B = sinMom (wS y) x`, `B' = sinMom (wR y) x`.

This block records what each attack on that form actually yields.

* **Even-kernel simplification** (`cosMom_xiWeight`, `sinMom_xiWeight`): the parity of `Φ`
  collapses the batch-10 *four*-square value to *two* squares, and identifies the two
  squares as `A²` and `B²` — the same `A` and `B` that appear in the leaf.  So the compiled
  family and the open leaf are built from **the same two moments**; the family uses
  `(A,B)`, the leaf uses `(A,B)` paired against `(A',B')`.

* **Cauchy–Schwarz completion** (`leaf_cauchy_schwarz`): bounds the leaf's *magnitude* by
  `√(A²+B²)·√(A'²+B'²)`, and — this is the point — is an equality precisely when
  `(A,B) ∥ (A',B')`.  A magnitude bound is sign-blind: **this instrument cannot decide the
  leaf**, and the reason is visible in the statement, not asserted.

* **Sign agreement** (`leaf_nonneg_of_products`): the smallest sufficient condition, one
  scalar per channel.

* **The `x = 0` fibre** (`target_zero_nonneg`): unconditionally nonnegative, because at
  `x = 0` the chart clock is `1` and both surviving moments are integrals of nonnegative
  integrands.  This is the one member of the family that closes by pointwise positivity.

* **The `y = 0` fibre** (`target_y_zero`): exactly `0`.  The leaf is an odd function of the
  tilt through the cell centre, so `y = 0` is its stationary point, not a boundary case.

SCOPE: identities, one unconditional nonnegativity (`x = 0`), one unconditional bound.
Nothing here mentions zeros, and nothing here decides the general sign.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B11

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open CriticalLinePhasor.C3B4B
open C3B6.Theta
open C3B10

/-! ### 1. The even-kernel simplification: four squares become two -/

theorem xiWeight_split (lam t : ℝ) : xiWeight lam t = wQ lam t + wS lam t := by
  unfold xiWeight wQ wS
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

theorem wQ_cos_integrable (lam x : ℝ) :
    Integrable (fun t : ℝ => wQ lam t * Real.cos (x * t)) := by
  refine (wQ_integrable lam).mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with t; simpa using Real.abs_cos_le_one (x * t)

theorem wS_cos_integrable (lam x : ℝ) :
    Integrable (fun t : ℝ => wS lam t * Real.cos (x * t)) := by
  refine (wS_integrable lam).mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with t; simpa using Real.abs_cos_le_one (x * t)

theorem wQ_sin_integrable (lam x : ℝ) :
    Integrable (fun t : ℝ => wQ lam t * Real.sin (x * t)) := by
  refine (wQ_integrable lam).mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with t; simpa using Real.abs_sin_le_one (x * t)

theorem wS_sin_integrable (lam x : ℝ) :
    Integrable (fun t : ℝ => wS lam t * Real.sin (x * t)) := by
  refine (wS_integrable lam).mul_bdd (c := 1) ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with t; simpa using Real.abs_sin_le_one (x * t)

/-- The cosine moment of the tilted kernel **is** the cosine moment of its even part. -/
theorem cosMom_xiWeight (lam x : ℝ) : cosMom (xiWeight lam) x = cosMom (wQ lam) x := by
  have hpt : ∀ t : ℝ, xiWeight lam t * Real.cos (x * t)
      = wQ lam t * Real.cos (x * t) + wS lam t * Real.cos (x * t) := by
    intro t; rw [xiWeight_split lam t]; ring
  have hadd : (∫ t : ℝ, wQ lam t * Real.cos (x * t) + wS lam t * Real.cos (x * t))
      = (∫ t : ℝ, wQ lam t * Real.cos (x * t)) + ∫ t : ℝ, wS lam t * Real.cos (x * t) :=
    integral_add (wQ_cos_integrable lam x) (wS_cos_integrable lam x)
  have hz : cosMom (wS lam) x = 0 := cosMom_wS lam x
  unfold cosMom at hz ⊢
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hadd, hz, add_zero]

/-- The sine moment of the tilted kernel **is** the sine moment of its odd part. -/
theorem sinMom_xiWeight (lam x : ℝ) : sinMom (xiWeight lam) x = sinMom (wS lam) x := by
  have hpt : ∀ t : ℝ, xiWeight lam t * Real.sin (x * t)
      = wQ lam t * Real.sin (x * t) + wS lam t * Real.sin (x * t) := by
    intro t; rw [xiWeight_split lam t]; ring
  have hadd : (∫ t : ℝ, wQ lam t * Real.sin (x * t) + wS lam t * Real.sin (x * t))
      = (∫ t : ℝ, wQ lam t * Real.sin (x * t)) + ∫ t : ℝ, wS lam t * Real.sin (x * t) :=
    integral_add (wQ_sin_integrable lam x) (wS_sin_integrable lam x)
  have hz : sinMom (wQ lam) x = 0 := sinMom_wQ lam x
  unfold sinMom at hz ⊢
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), hadd, hz, zero_add]

/-- **THE TWO-SQUARE FORM.**  Batch 10's `cosh` family, with the parity of `Φ` used: the
four squares collapse to two, and they are the squares of the very moments `A`, `B` that
the open leaf pairs against `A'`, `B'`. -/
theorem cellDensity_cosh_Ioi_sq (x lam : ℝ) :
    (∫ u in Ioi (0 : ℝ), Real.cosh (2 * lam * u) * cellDensity x u)
      = 4⁻¹ * (cosMom (wQ lam) x ^ 2 + sinMom (wS lam) x ^ 2) := by
  rw [cellDensity_cosh_Ioi, cellDensity_cosh_full,
    cosMom_xiWeight, sinMom_xiWeight, cosMom_xiWeight, sinMom_xiWeight]
  have h1 : cosMom (wQ (-lam)) x = cosMom (wQ lam) x := by
    unfold cosMom
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show wQ (-lam) t * Real.cos (x * t) = wQ lam t * Real.cos (x * t)
    unfold wQ
    rw [show (-lam) * t = -(lam * t) by ring, Real.cosh_neg]
  have h2 : sinMom (wS (-lam)) x = -sinMom (wS lam) x := by
    unfold sinMom
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show wS (-lam) t * Real.sin (x * t) = -(wS lam t * Real.sin (x * t))
    unfold wS
    rw [show (-lam) * t = -(lam * t) by ring, Real.sinh_neg]
    ring
  rw [h1, h2]
  ring

/-! ### 2. Cauchy–Schwarz: a magnitude bound, and why it is sign-blind -/

/-- **THE CAUCHY–SCHWARZ COMPLETION.**  The leaf is bounded in magnitude by the product of
the two channel norms.  Equality holds exactly when `(A,B)` and `(A',B')` are parallel, and
the bound is symmetric under `(A',B') ↦ (−A',−B')`: it constrains size, never sign. -/
theorem leaf_cauchy_schwarz (A A' B B' : ℝ) :
    (A * A' + B * B') ^ 2 ≤ (A ^ 2 + B ^ 2) * (A' ^ 2 + B' ^ 2) := by
  nlinarith [sq_nonneg (A * B' - B * A'), sq_nonneg (A * A' + B * B')]

/-- The leaf is bounded below by minus the Cauchy–Schwarz radius; the two-sidedness is the
statement that no norm bound can produce the sign. -/
theorem leaf_abs_le (A A' B B' : ℝ) :
    |A * A' + B * B'| ≤ Real.sqrt ((A ^ 2 + B ^ 2) * (A' ^ 2 + B' ^ 2)) := by
  have h := leaf_cauchy_schwarz A A' B B'
  have hnn : (0 : ℝ) ≤ (A ^ 2 + B ^ 2) * (A' ^ 2 + B' ^ 2) := by positivity
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq_eq_abs] at this

/-! ### 3. Sign agreement: the smallest sufficient condition -/

/-- **THE SUFFICIENT CONDITION, MINIMAL.**  One scalar per channel: the cosine channel and
the sine channel each contribute nonnegatively. -/
theorem leaf_nonneg_of_products (x y : ℝ)
    (hc : 0 ≤ cosMom (wQ y) x * cosMom (wP y) x)
    (hs : 0 ≤ sinMom (wS y) x * sinMom (wR y) x) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u := by
  rw [target_eq x y]
  have : (0 : ℝ) ≤ cosMom (wQ y) x * cosMom (wP y) x + sinMom (wS y) x * sinMom (wR y) x := by
    linarith
  linarith

/-! ### 4. The `x = 0` fibre: unconditional -/

theorem sinMom_at_zero (W : ℝ → ℝ) : sinMom W 0 = 0 := by
  unfold sinMom
  simp

theorem cosMom_at_zero (W : ℝ → ℝ) : cosMom W 0 = ∫ t : ℝ, W t := by
  unfold cosMom
  simp

theorem t_sinh_nonneg {y : ℝ} (hy : 0 ≤ y) (t : ℝ) : 0 ≤ t * Real.sinh (y * t) := by
  rcases le_total 0 t with h | h
  · have : 0 ≤ Real.sinh (y * t) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr (by positivity)
    positivity
  · have hyt : y * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy h
    have : Real.sinh (y * t) ≤ 0 := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr hyt
    nlinarith [h, this]

/-- **THE `x = 0` MEMBER, UNCONDITIONALLY NONNEGATIVE.**  At `x = 0` the chart clock is `1`,
the sine channel vanishes identically, and both surviving moments are integrals of
pointwise nonnegative integrands: `cosh(yt)Φ(t) ≥ 0` and `t·sinh(yt)Φ(t) ≥ 0`. -/
theorem target_zero_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ∫ u in Ioi (0 : ℝ), gY y u * cellDensity 0 u := by
  rw [target_eq 0 y, sinMom_at_zero, cosMom_at_zero, cosMom_at_zero]
  have hQ : (0 : ℝ) ≤ ∫ t : ℝ, wQ y t := by
    refine integral_nonneg fun t => ?_
    have hpos : 0 < riemannXiKernel t := C3B5.A1.riemannXiKernel_pos_all t
    have : (0 : ℝ) < Real.cosh (y * t) := Real.cosh_pos _
    unfold wQ
    positivity
  have hP : (0 : ℝ) ≤ ∫ t : ℝ, wP y t := by
    refine integral_nonneg fun t => ?_
    have hpos : 0 < riemannXiKernel t := C3B5.A1.riemannXiKernel_pos_all t
    have hts := t_sinh_nonneg hy t
    unfold wP
    have : t * Real.sinh (y * t) * riemannXiKernel t
        = (t * Real.sinh (y * t)) * riemannXiKernel t := by ring
    rw [this]
    exact mul_nonneg hts hpos.le
  have : (0 : ℝ) ≤ (∫ t : ℝ, wQ y t) * ∫ t : ℝ, wP y t := mul_nonneg hQ hP
  nlinarith [this]

/-! ### 5. The `y = 0` fibre: exactly zero -/

theorem wP_zero (t : ℝ) : wP 0 t = 0 := by
  unfold wP
  rw [show (0 : ℝ) * t = 0 by ring, Real.sinh_zero]
  ring

theorem wS_zero (t : ℝ) : wS 0 t = 0 := by
  unfold wS
  rw [show (0 : ℝ) * t = 0 by ring, Real.sinh_zero]
  ring

/-- **THE `y = 0` MEMBER, EXACTLY ZERO.**  The leaf is stationary at zero tilt. -/
theorem target_y_zero (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), gY 0 u * cellDensity x u) = 0 := by
  rw [target_eq x 0]
  have hP : cosMom (wP 0) x = 0 := by
    unfold cosMom
    have : ∀ t : ℝ, wP 0 t * Real.cos (x * t) = 0 := by
      intro t; rw [wP_zero t]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall this)]
    simp
  have hS : sinMom (wS 0) x = 0 := by
    unfold sinMom
    have : ∀ t : ℝ, wS 0 t * Real.sin (x * t) = 0 := by
      intro t; rw [wS_zero t]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall this)]
    simp
  rw [hP, hS]
  ring

end C3B11

section AxiomAudit
#print axioms C3B11.xiWeight_split
#print axioms C3B11.cosMom_xiWeight
#print axioms C3B11.sinMom_xiWeight
#print axioms C3B11.cellDensity_cosh_Ioi_sq
#print axioms C3B11.leaf_cauchy_schwarz
#print axioms C3B11.leaf_abs_le
#print axioms C3B11.leaf_nonneg_of_products
#print axioms C3B11.t_sinh_nonneg
#print axioms C3B11.target_zero_nonneg
#print axioms C3B11.target_y_zero
end AxiomAudit
