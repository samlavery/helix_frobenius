import c3b10_A3
import c3b11_A1

/-!
# C3 batch 11, block A2 — **the target, evaluated exactly**

The open leaf of batch 9/10 is

  `0 ≤ ∫_{(0,∞)} u·sinh(2yu) · C(x,u) du`,     `C(x,u) = ∫_ℝ Φ(u+p)Φ(u−p)cos(2xp) dp`.

Batch 10 evaluated the `cosh` family exactly and observed (`gY_eq_cosh_deriv`) that the
target is its `λ`-derivative.  That framing needs differentiation under the integral sign.
**This block does not differentiate anything.**  It evaluates the target directly, by the
same shear that evaluated the family, using the two-weight engine of `c3b11_A1`.

## The mechanism: the cell centre is a sum, the legs are a product

The `cosh` family works because the tilt factorises across the cell:
`e^{λ(u+p)}e^{λ(u−p)} = e^{2λu}`.  The target weight `u·sinh(2yu)` does **not** factorise —
but it is a sum of four factorised terms, because `2u = (u+p) + (u−p)` and
`sinh(y(u+p) + y(u−p)) = sinh cosh + cosh sinh`.  With the four carrier weights

  `Q = cosh(y·)Φ`,   `S = sinh(y·)Φ`,   `P = (·)sinh(y·)Φ`,   `R = (·)cosh(y·)Φ`,

the identity is pointwise and exact:

  `2·u·sinh(2yu)·Φ(u+p)Φ(u−p) = P(u+p)Q(u−p) + R(u+p)S(u−p) + S(u+p)R(u−p) + Q(u+p)P(u−p)`.

Four two-weight pairings, each evaluated exactly by `C3B11.carrier_pairing2`.  Then the
parity of `Φ` kills half of the eight moments — `S` and `R` are odd, `Q` and `P` are even —
and what survives is

  `∫_{(0,∞)} u sinh(2yu) C(x,u) du  =  ¼ ( A·A' + B·B' )`

with the four explicit moments
  `A  = ∫ cosh(yt)Φ(t)cos(xt) dt`,   `A' = ∫ t sinh(yt)Φ(t)cos(xt) dt`,
  `B  = ∫ sinh(yt)Φ(t)sin(xt) dt`,   `B' = ∫ t cosh(yt)Φ(t)sin(xt) dt`.

Nothing is estimated and nothing is truncated: the oscillatory two-dimensional integral is
replaced by a bilinear form in four one-dimensional moments.

CHART NOTE.  All of this lives on the **carrier**: `u` is the cell centre, `p` the half-gap
between the two phasor legs, `t = u+p` and `s = u−p` the legs themselves.  The clock
`cos(2xp)` is the **chart** readout.  No convergence abscissa is used anywhere; the weights
are entire and the phasor legs enter at magnitude `0`.

SCOPE: identities and one nonnegativity (at `x = 0`).  Nothing here mentions zeros.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B11

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open CriticalLinePhasor.C3B4B
open C3B6.Theta
open C3B10

/-! ### 1. The four carrier weights -/

/-- `Q_y(t) = cosh(yt)Φ(t)` — even. -/
def wQ (y t : ℝ) : ℝ := Real.cosh (y * t) * riemannXiKernel t

/-- `S_y(t) = sinh(yt)Φ(t)` — odd. -/
def wS (y t : ℝ) : ℝ := Real.sinh (y * t) * riemannXiKernel t

/-- `P_y(t) = t·sinh(yt)Φ(t)` — even. -/
def wP (y t : ℝ) : ℝ := t * Real.sinh (y * t) * riemannXiKernel t

/-- `R_y(t) = t·cosh(yt)Φ(t)` — odd. -/
def wR (y t : ℝ) : ℝ := t * Real.cosh (y * t) * riemannXiKernel t

/-! ### 2. Integrability -/

/-- `|t| ≤ e^t + e^{−t}`: the linear factor is absorbed by shifting the tilt by one. -/
theorem abs_le_exp_add_exp (t : ℝ) : |t| ≤ Real.exp t + Real.exp (-t) := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    have h1 := Real.add_one_le_exp t
    have h2 := Real.exp_pos (-t)
    linarith
  · rw [abs_of_nonpos h]
    have h1 := Real.add_one_le_exp (-t)
    have h2 := Real.exp_pos t
    linarith

/-- The linear moment of the tilted kernel is integrable: `t·e^{λt}Φ(t) ∈ L¹`.
The linear factor costs exactly one unit of tilt, and the tilt family is unbounded. -/
theorem t_xiWeight_integrable (lam : ℝ) : Integrable (fun t : ℝ => t * xiWeight lam t) := by
  have hmaj : Integrable (fun t : ℝ => xiWeight (lam + 1) t + xiWeight (lam - 1) t) :=
    (xiWeight_integrable (lam + 1)).add (xiWeight_integrable (lam - 1))
  have hm : Measurable (fun t : ℝ => t * xiWeight lam t) :=
    measurable_id.mul (xiWeight_measurable lam)
  refine Integrable.mono hmaj hm.aestronglyMeasurable ?_
  filter_upwards with t
  have hpos : 0 < riemannXiKernel t := C3B5.A1.riemannXiKernel_pos_all t
  have hsum : xiWeight (lam + 1) t + xiWeight (lam - 1) t
      = (Real.exp t + Real.exp (-t)) * (Real.exp (lam * t) * riemannXiKernel t) := by
    unfold xiWeight
    rw [show (lam + 1) * t = lam * t + t by ring, show (lam - 1) * t = lam * t + -t by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hsum,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (Real.exp t + Real.exp (-t)) * (Real.exp (lam * t) * riemannXiKernel t))]
  unfold xiWeight
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos (lam * t)).le, abs_of_nonneg hpos.le]
  have hb := abs_le_exp_add_exp t
  have hE : (0 : ℝ) < Real.exp (lam * t) * riemannXiKernel t := by positivity
  nlinarith [hb, hE]

theorem wQ_eq (y t : ℝ) : wQ y t = 2⁻¹ * (xiWeight y t + xiWeight (-y) t) := by
  unfold wQ xiWeight
  rw [Real.cosh_eq, show (-y) * t = -(y * t) by ring]
  ring

theorem wS_eq (y t : ℝ) : wS y t = 2⁻¹ * (xiWeight y t - xiWeight (-y) t) := by
  unfold wS xiWeight
  rw [Real.sinh_eq, show (-y) * t = -(y * t) by ring]
  ring

theorem wP_eq (y t : ℝ) : wP y t = 2⁻¹ * (t * xiWeight y t - t * xiWeight (-y) t) := by
  unfold wP xiWeight
  rw [Real.sinh_eq, show (-y) * t = -(y * t) by ring]
  ring

theorem wR_eq (y t : ℝ) : wR y t = 2⁻¹ * (t * xiWeight y t + t * xiWeight (-y) t) := by
  unfold wR xiWeight
  rw [Real.cosh_eq, show (-y) * t = -(y * t) by ring]
  ring

theorem wQ_integrable (y : ℝ) : Integrable (wQ y) := by
  refine (((xiWeight_integrable y).add (xiWeight_integrable (-y))).const_mul (2⁻¹ : ℝ)).congr ?_
  filter_upwards with t; exact (wQ_eq y t).symm

theorem wS_integrable (y : ℝ) : Integrable (wS y) := by
  refine (((xiWeight_integrable y).sub (xiWeight_integrable (-y))).const_mul (2⁻¹ : ℝ)).congr ?_
  filter_upwards with t; exact (wS_eq y t).symm

theorem wP_integrable (y : ℝ) : Integrable (wP y) := by
  refine (((t_xiWeight_integrable y).sub (t_xiWeight_integrable (-y))).const_mul
    (2⁻¹ : ℝ)).congr ?_
  filter_upwards with t; exact (wP_eq y t).symm

theorem wR_integrable (y : ℝ) : Integrable (wR y) := by
  refine (((t_xiWeight_integrable y).add (t_xiWeight_integrable (-y))).const_mul
    (2⁻¹ : ℝ)).congr ?_
  filter_upwards with t; exact (wR_eq y t).symm

theorem wQ_measurable (y : ℝ) : Measurable (wQ y) :=
  (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).measurable.mul
    riemannXiKernel_measurable

theorem wS_measurable (y : ℝ) : Measurable (wS y) :=
  (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).measurable.mul
    riemannXiKernel_measurable

theorem wP_measurable (y : ℝ) : Measurable (wP y) :=
  (measurable_id.mul
    (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).measurable).mul
    riemannXiKernel_measurable

theorem wR_measurable (y : ℝ) : Measurable (wR y) :=
  (measurable_id.mul
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).measurable).mul
    riemannXiKernel_measurable

/-! ### 3. Parity, and the four moments that die -/

theorem wQ_even (y t : ℝ) : wQ y (-t) = wQ y t := by
  unfold wQ
  rw [show y * -t = -(y * t) by ring, Real.cosh_neg, riemannXiKernel_neg]

theorem wS_odd (y t : ℝ) : wS y (-t) = -wS y t := by
  unfold wS
  rw [show y * -t = -(y * t) by ring, Real.sinh_neg, riemannXiKernel_neg]
  ring

theorem wP_even (y t : ℝ) : wP y (-t) = wP y t := by
  unfold wP
  rw [show y * -t = -(y * t) by ring, Real.sinh_neg, riemannXiKernel_neg]
  ring

theorem wR_odd (y t : ℝ) : wR y (-t) = -wR y t := by
  unfold wR
  rw [show y * -t = -(y * t) by ring, Real.cosh_neg, riemannXiKernel_neg]
  ring

theorem sinMom_wQ (y x : ℝ) : sinMom (wQ y) x = 0 := sinMom_of_even (wQ_even y) x
theorem sinMom_wP (y x : ℝ) : sinMom (wP y) x = 0 := sinMom_of_even (wP_even y) x
theorem cosMom_wS (y x : ℝ) : cosMom (wS y) x = 0 := cosMom_of_odd (wS_odd y) x
theorem cosMom_wR (y x : ℝ) : cosMom (wR y) x = 0 := cosMom_of_odd (wR_odd y) x

/-! ### 4. The pointwise four-term split of the cell-centre weight -/

/-- **THE SPLIT.**  `2u·sinh(2yu)` is the sum of four products, one per ordered pair of
legs.  This is the whole mechanism: `2u = (u+p) + (u−p)` and `sinh` adds. -/
theorem cell_weight_split (y u p : ℝ) :
    wP y (u + p) * wQ y (u - p) + wR y (u + p) * wS y (u - p)
      + wS y (u + p) * wR y (u - p) + wQ y (u + p) * wP y (u - p)
      = 2 * (gY y u * (riemannXiKernel (u + p) * riemannXiKernel (u - p))) := by
  unfold wP wQ wR wS gY
  have hadd : Real.sinh (y * (u + p) + y * (u - p))
      = Real.sinh (y * (u + p)) * Real.cosh (y * (u - p))
        + Real.cosh (y * (u + p)) * Real.sinh (y * (u - p)) := Real.sinh_add _ _
  have hcol : y * (u + p) + y * (u - p) = 2 * y * u := by ring
  rw [hcol] at hadd
  linear_combination (-(2 * u * riemannXiKernel (u + p) * riemannXiKernel (u - p))) * hadd

/-! ### 5. The four pairings, and the exact value -/

/-- The `u`-slice of a carrier pairing is integrable for a.e. cell centre. -/
theorem slice_ae {P Q : ℝ → ℝ} (hIP : Integrable P) (hmP : Measurable P)
    (hIQ : Integrable Q) (hmQ : Measurable Q) (x : ℝ) :
    ∀ᵐ u : ℝ, Integrable (fun p : ℝ => P (u + p) * Q (u - p) * Real.cos (2 * x * p)) := by
  have h := (carrierBilin2_prod_integrable hIP hmP hIQ hmQ x).prod_right_ae
  filter_upwards [h] with u hu
  exact hu

/-- The four carrier pairings of the target, as functions of the cell centre. -/
def leg1 (x y u : ℝ) : ℝ := ∫ p : ℝ, wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
def leg2 (x y u : ℝ) : ℝ := ∫ p : ℝ, wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p)
def leg3 (x y u : ℝ) : ℝ := ∫ p : ℝ, wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p)
def leg4 (x y u : ℝ) : ℝ := ∫ p : ℝ, wQ y (u + p) * wP y (u - p) * Real.cos (2 * x * p)

theorem gY_cellDensity_ae (x y : ℝ) :
    (fun u : ℝ => gY y u * cellDensity x u)
      =ᵐ[volume] fun u : ℝ => 2⁻¹ * (leg1 x y u + leg2 x y u + leg3 x y u + leg4 x y u) := by
  filter_upwards [slice_ae (wP_integrable y) (wP_measurable y)
      (wQ_integrable y) (wQ_measurable y) x,
    slice_ae (wR_integrable y) (wR_measurable y) (wS_integrable y) (wS_measurable y) x,
    slice_ae (wS_integrable y) (wS_measurable y) (wR_integrable y) (wR_measurable y) x,
    slice_ae (wQ_integrable y) (wQ_measurable y) (wP_integrable y) (wP_measurable y) x]
    with u h1 h2 h3 h4
  show gY y u * cellDensity x u = 2⁻¹ * (leg1 x y u + leg2 x y u + leg3 x y u + leg4 x y u)
  -- the pointwise split, integrated with the constant cell-centre weight pulled inside
  have hA : gY y u * cellDensity x u
      = ∫ p : ℝ, 2⁻¹ * (wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
          + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p)
          + wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p)
          + wQ y (u + p) * wP y (u - p) * Real.cos (2 * x * p)) := by
    unfold cellDensity
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show gY y u * (riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p))
        = 2⁻¹ * (wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
          + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p)
          + wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p)
          + wQ y (u + p) * wP y (u - p) * Real.cos (2 * x * p))
    have h := cell_weight_split y u p
    linear_combination (-(Real.cos (2 * x * p)) / 2) * h
  -- and the four-fold additivity of the slice integral
  have hf12 : Integrable (fun p : ℝ => wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
      + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p)) := h1.add h2
  have hf123 : Integrable (fun p : ℝ => (wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
      + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p))
      + wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p)) := hf12.add h3
  have a12 : (∫ p : ℝ, wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
        + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p))
      = leg1 x y u + leg2 x y u := integral_add h1 h2
  have a123 : (∫ p : ℝ, (wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
        + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p))
        + wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p))
      = (∫ p : ℝ, wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
        + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p)) + leg3 x y u :=
    integral_add hf12 h3
  have a1234 : (∫ p : ℝ, ((wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
        + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p))
        + wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p))
        + wQ y (u + p) * wP y (u - p) * Real.cos (2 * x * p))
      = (∫ p : ℝ, (wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
        + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p))
        + wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p)) + leg4 x y u :=
    integral_add hf123 h4
  rw [hA, integral_const_mul]
  have hsum : (∫ p : ℝ, wP y (u + p) * wQ y (u - p) * Real.cos (2 * x * p)
        + wR y (u + p) * wS y (u - p) * Real.cos (2 * x * p)
        + wS y (u + p) * wR y (u - p) * Real.cos (2 * x * p)
        + wQ y (u + p) * wP y (u - p) * Real.cos (2 * x * p))
      = leg1 x y u + leg2 x y u + leg3 x y u + leg4 x y u := by
    rw [a1234, a123, a12]
  rw [hsum]

/-- The target integrand is integrable on the whole carrier. -/
theorem gY_cellDensity_integrable (x y : ℝ) :
    Integrable (fun u : ℝ => gY y u * cellDensity x u) := by
  have i1 := carrier_pairing2_integrable (wP_integrable y) (wP_measurable y)
    (wQ_integrable y) (wQ_measurable y) x
  have i2 := carrier_pairing2_integrable (wR_integrable y) (wR_measurable y)
    (wS_integrable y) (wS_measurable y) x
  have i3 := carrier_pairing2_integrable (wS_integrable y) (wS_measurable y)
    (wR_integrable y) (wR_measurable y) x
  have i4 := carrier_pairing2_integrable (wQ_integrable y) (wQ_measurable y)
    (wP_integrable y) (wP_measurable y) x
  exact ((((i1.add i2).add i3).add i4).const_mul (2⁻¹ : ℝ)).congr (gY_cellDensity_ae x y).symm

/-- **THE TARGET ON THE WHOLE CARRIER, EXACTLY.** -/
theorem gY_cellDensity_full (x y : ℝ) :
    (∫ u : ℝ, gY y u * cellDensity x u)
      = 2⁻¹ * (cosMom (wQ y) x * cosMom (wP y) x + sinMom (wS y) x * sinMom (wR y) x) := by
  have i1 := carrier_pairing2_integrable (wP_integrable y) (wP_measurable y)
    (wQ_integrable y) (wQ_measurable y) x
  have i2 := carrier_pairing2_integrable (wR_integrable y) (wR_measurable y)
    (wS_integrable y) (wS_measurable y) x
  have i3 := carrier_pairing2_integrable (wS_integrable y) (wS_measurable y)
    (wR_integrable y) (wR_measurable y) x
  have i4 := carrier_pairing2_integrable (wQ_integrable y) (wQ_measurable y)
    (wP_integrable y) (wP_measurable y) x
  have e1 := carrier_pairing2 (wP_integrable y) (wP_measurable y)
    (wQ_integrable y) (wQ_measurable y) x
  have e2 := carrier_pairing2 (wR_integrable y) (wR_measurable y)
    (wS_integrable y) (wS_measurable y) x
  have e3 := carrier_pairing2 (wS_integrable y) (wS_measurable y)
    (wR_integrable y) (wR_measurable y) x
  have e4 := carrier_pairing2 (wQ_integrable y) (wQ_measurable y)
    (wP_integrable y) (wP_measurable y) x
  have j1 : Integrable (leg1 x y) := i1
  have j2 : Integrable (leg2 x y) := i2
  have j3 : Integrable (leg3 x y) := i3
  have j4 : Integrable (leg4 x y) := i4
  have b12 : (∫ u : ℝ, leg1 x y u + leg2 x y u)
      = (∫ u : ℝ, leg1 x y u) + ∫ u : ℝ, leg2 x y u := integral_add j1 j2
  have b123 : (∫ u : ℝ, (leg1 x y u + leg2 x y u) + leg3 x y u)
      = (∫ u : ℝ, leg1 x y u + leg2 x y u) + ∫ u : ℝ, leg3 x y u :=
    integral_add (j1.add j2) j3
  have b1234 : (∫ u : ℝ, ((leg1 x y u + leg2 x y u) + leg3 x y u) + leg4 x y u)
      = (∫ u : ℝ, (leg1 x y u + leg2 x y u) + leg3 x y u) + ∫ u : ℝ, leg4 x y u :=
    integral_add ((j1.add j2).add j3) j4
  have v1 : (∫ u : ℝ, leg1 x y u)
      = 2⁻¹ * (cosMom (wP y) x * cosMom (wQ y) x + sinMom (wP y) x * sinMom (wQ y) x) := e1
  have v2 : (∫ u : ℝ, leg2 x y u)
      = 2⁻¹ * (cosMom (wR y) x * cosMom (wS y) x + sinMom (wR y) x * sinMom (wS y) x) := e2
  have v3 : (∫ u : ℝ, leg3 x y u)
      = 2⁻¹ * (cosMom (wS y) x * cosMom (wR y) x + sinMom (wS y) x * sinMom (wR y) x) := e3
  have v4 : (∫ u : ℝ, leg4 x y u)
      = 2⁻¹ * (cosMom (wQ y) x * cosMom (wP y) x + sinMom (wQ y) x * sinMom (wP y) x) := e4
  rw [integral_congr_ae (gY_cellDensity_ae x y), integral_const_mul,
    b1234, b123, b12, v1, v2, v3, v4,
    cosMom_wS y x, cosMom_wR y x, sinMom_wQ y x, sinMom_wP y x]
  ring

/-! ### 6. Folding to the half line — the target as stated -/

theorem gY_cellDensity_even (x y u : ℝ) :
    gY y (-u) * cellDensity x (-u) = gY y u * cellDensity x u := by
  unfold gY
  rw [show 2 * y * -u = -(2 * y * u) by ring, Real.sinh_neg, cellDensity_even]
  ring

/-- **THE TARGET, EXACTLY.**  For every real `x` and every real `y`:
`∫_{(0,∞)} u sinh(2yu) C(x,u) du = ¼(A·A' + B·B')`, an explicit bilinear form in four
one-dimensional moments of the theta kernel.  No estimate, no truncation, no
differentiation under the integral sign. -/
theorem target_eq (x y : ℝ) :
    (∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u)
      = 4⁻¹ * (cosMom (wQ y) x * cosMom (wP y) x + sinMom (wS y) x * sinMom (wR y) x) := by
  have habs := integral_comp_abs (f := fun u : ℝ => gY y u * cellDensity x u)
  have hcongr : (∫ u : ℝ, gY y |u| * cellDensity x |u|)
      = ∫ u : ℝ, gY y u * cellDensity x u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show gY y |u| * cellDensity x |u| = gY y u * cellDensity x u
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      exact gY_cellDensity_even x y u
  rw [hcongr, gY_cellDensity_full x y] at habs
  linarith [habs]

/-- **THE LEAF, AS A SIGN CONDITION ON FOUR MOMENTS.**  The target is nonnegative exactly
when the bilinear form is.  This is the statement the batch-9 chain consumes. -/
theorem target_nonneg_iff (x y : ℝ) :
    0 ≤ (∫ u in Ioi (0 : ℝ), gY y u * cellDensity x u)
      ↔ 0 ≤ cosMom (wQ y) x * cosMom (wP y) x + sinMom (wS y) x * sinMom (wR y) x := by
  rw [target_eq x y]
  constructor
  · intro h; linarith
  · intro h; linarith

end C3B11

section AxiomAudit
#print axioms C3B11.abs_le_exp_add_exp
#print axioms C3B11.t_xiWeight_integrable
#print axioms C3B11.wQ_integrable
#print axioms C3B11.wS_integrable
#print axioms C3B11.wP_integrable
#print axioms C3B11.wR_integrable
#print axioms C3B11.sinMom_wQ
#print axioms C3B11.sinMom_wP
#print axioms C3B11.cosMom_wS
#print axioms C3B11.cosMom_wR
#print axioms C3B11.cell_weight_split
#print axioms C3B11.gY_cellDensity_ae
#print axioms C3B11.gY_cellDensity_integrable
#print axioms C3B11.gY_cellDensity_full
#print axioms C3B11.target_eq
#print axioms C3B11.target_nonneg_iff
end AxiomAudit
