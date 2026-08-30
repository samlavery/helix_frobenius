import c3b11_A3

/-!
# C3 batch 12, block A1 — the **even-moment ladder** of the cell density

Batch 11 evaluated the target `∫_{(0,∞)} u sinh(2yu) C(x,u) du` exactly as a bilinear form
in four moments.  This block evaluates the *individual even moments*
`∫_{(0,∞)} u^{2k} C(x,u) du`, which are the Taylor coefficients of that family in `y`, and
finds that they are the classical **Laguerre expressions of the readout**.

## The mechanism, again: the cell centre is a sum

`(2u)^{2k} = ((u+p) + (u−p))^{2k}` expands binomially into two-leg products, so the
two-weight engine `C3B11.carrier_pairing2` evaluates every even moment exactly.  At `k = 1`:

  `4u²·Φ(u+p)Φ(u−p) = M₂(u+p)M₀(u−p) + 2·M₁(u+p)M₁(u−p) + M₀(u+p)M₂(u−p)`,
  `M_j(t) = t^j Φ(t)`.

Three pairings, then parity kills three of the six moments (`M₀`, `M₂` even; `M₁` odd):

  `∫_{(0,∞)} u² C(x,u) du = ⅛ ( c₀·c₂ + s₁² )`,
  `c₀ = cosMom Φ x`,  `c₂ = cosMom (t²Φ) x`,  `s₁ = sinMom (tΦ) x`.

## Why this is the sharp form of the `y → 0⁺` edge

With `Ξ(x) := ∫Φ(t)cos(xt)dt` one has `c₀ = Ξ`, `s₁ = −Ξ′`, `c₂ = −Ξ″`, so the bracket is

  `c₀c₂ + s₁² = Ξ′(x)² − Ξ(x)Ξ″(x)`,

the **first Laguerre expression**.  The `s₁²` summand is a manifest square; the whole
difficulty is concentrated in the single product `c₀·c₂`.  That is a strictly smaller target
than the four-moment leaf, and it yields two unconditional fibres immediately:

* wherever the two cosine moments have the same sign, the moment is nonnegative;
* **wherever `c₀` vanishes — i.e. at every real zero of the readout — the moment is a
  perfect square**, `⅛ s₁²`, hence nonnegative with no hypothesis at all.

The second is the sharp one: the zeros of `Ξ` are exactly where a Laguerre-type inequality is
most delicate, and there the cell density's second moment closes by identity.

SCOPE: identities and unconditional nonnegativity on two fibres.  Nothing here mentions zeros
of `ζ`, and nothing here decides the general sign.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B12

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open CriticalLinePhasor.C3B4B
open C3B6.Theta
open C3B10
open C3B11

/-! ### 1. The polynomial carrier weights -/

/-- `M₁(t) = t·Φ(t)` — odd. -/
def kM1 (t : ℝ) : ℝ := t * riemannXiKernel t

/-- `M₂(t) = t²·Φ(t)` — even. -/
def kM2 (t : ℝ) : ℝ := t ^ 2 * riemannXiKernel t

/-! ### 2. Integrability: the quadratic factor costs one unit of tilt -/

/-- `x² ≤ 4e^x` on `x ≥ 0`, from `1 + x/2 ≤ e^{x/2}` squared. -/
theorem sq_le_four_mul_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ 4 * Real.exp x := by
  have h := Real.add_one_le_exp (x / 2)
  have hp : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have hsq : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsq]
  nlinarith [h, hp, hx]

theorem sq_le_four_mul_exp_add_exp (t : ℝ) :
    t ^ 2 ≤ 4 * (Real.exp t + Real.exp (-t)) := by
  rcases le_total 0 t with h | h
  · have h1 := sq_le_four_mul_exp h
    have h2 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
    linarith
  · have hneg : (0 : ℝ) ≤ -t := by linarith
    have h1 := sq_le_four_mul_exp hneg
    have h2 : (0 : ℝ) < Real.exp t := Real.exp_pos _
    have hsq : (-t) ^ 2 = t ^ 2 := by ring
    rw [hsq] at h1
    linarith

theorem xiKernel_integrable : Integrable riemannXiKernel := by
  have h := xiWeight_integrable 0
  rwa [xiWeight_zero] at h

theorem kM1_integrable : Integrable kM1 := by
  have h := t_xiWeight_integrable 0
  rw [xiWeight_zero] at h
  exact h

theorem kM2_integrable : Integrable kM2 := by
  have hmaj : Integrable (fun t : ℝ => 4 * (xiWeight 1 t + xiWeight (-1) t)) :=
    ((xiWeight_integrable 1).add (xiWeight_integrable (-1))).const_mul 4
  have hm : Measurable kM2 :=
    (measurable_id.pow_const 2).mul riemannXiKernel_measurable
  refine Integrable.mono hmaj hm.aestronglyMeasurable ?_
  filter_upwards with t
  have hpos : 0 < riemannXiKernel t := C3B5.A1.riemannXiKernel_pos_all t
  have hsum : 4 * (xiWeight 1 t + xiWeight (-1) t)
      = 4 * (Real.exp t + Real.exp (-t)) * riemannXiKernel t := by
    unfold xiWeight
    rw [show (1 : ℝ) * t = t by ring, show (-1 : ℝ) * t = -t by ring]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hsum,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 4 * (Real.exp t + Real.exp (-t)) * riemannXiKernel t)]
  unfold kM2
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2), abs_of_nonneg hpos.le]
  have hb := sq_le_four_mul_exp_add_exp t
  nlinarith [hb, hpos]

theorem kM1_measurable : Measurable kM1 :=
  measurable_id.mul riemannXiKernel_measurable

theorem kM2_measurable : Measurable kM2 :=
  (measurable_id.pow_const 2).mul riemannXiKernel_measurable

/-! ### 3. Parity, and the three moments that die -/

theorem kM1_odd (t : ℝ) : kM1 (-t) = -kM1 t := by
  unfold kM1; rw [riemannXiKernel_neg]; ring

theorem kM2_even (t : ℝ) : kM2 (-t) = kM2 t := by
  unfold kM2; rw [riemannXiKernel_neg]; ring

theorem sinMom_xiKernel (x : ℝ) : sinMom riemannXiKernel x = 0 :=
  sinMom_of_even (fun t => riemannXiKernel_neg t) x

theorem cosMom_kM1 (x : ℝ) : cosMom kM1 x = 0 := cosMom_of_odd kM1_odd x

theorem sinMom_kM2 (x : ℝ) : sinMom kM2 x = 0 := sinMom_of_even kM2_even x

/-! ### 4. The `k = 0` moment: the first tail is a perfect square -/

/-- **THE FIRST TAIL, AS A SQUARE.**  Batch 10 evaluated this as a sum of two squares; the
parity of `Φ` kills the sine channel outright, so it is one square. -/
theorem cellDensity_Ioi_eq_sq (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), cellDensity x u) = 4⁻¹ * cosMom riemannXiKernel x ^ 2 := by
  rw [cellDensity_Ioi_eq, sinMom_xiKernel]
  ring

/-! ### 5. The `k = 1` moment: the split, the pairings, the value -/

/-- **THE QUADRATIC SPLIT.**  `(2u)² = ((u+p)+(u−p))²`, read on the two legs. -/
theorem cell_u2_split (u p : ℝ) :
    kM2 (u + p) * riemannXiKernel (u - p) + 2 * (kM1 (u + p) * kM1 (u - p))
      + riemannXiKernel (u + p) * kM2 (u - p)
      = 4 * (u ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p))) := by
  unfold kM1 kM2
  ring

def qleg1 (x u : ℝ) : ℝ := ∫ p : ℝ, kM2 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
def qleg2 (x u : ℝ) : ℝ := ∫ p : ℝ, kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p)
def qleg3 (x u : ℝ) : ℝ := ∫ p : ℝ, riemannXiKernel (u + p) * kM2 (u - p) * Real.cos (2 * x * p)

theorem u2_cellDensity_ae (x : ℝ) :
    (fun u : ℝ => u ^ 2 * cellDensity x u)
      =ᵐ[volume] fun u : ℝ => 4⁻¹ * (qleg1 x u + 2 * qleg2 x u + qleg3 x u) := by
  filter_upwards [slice_ae kM2_integrable kM2_measurable
      xiKernel_integrable riemannXiKernel_measurable x,
    slice_ae kM1_integrable kM1_measurable kM1_integrable kM1_measurable x,
    slice_ae xiKernel_integrable riemannXiKernel_measurable kM2_integrable kM2_measurable x]
    with u h1 h2 h3
  show u ^ 2 * cellDensity x u = 4⁻¹ * (qleg1 x u + 2 * qleg2 x u + qleg3 x u)
  have hA : u ^ 2 * cellDensity x u
      = ∫ p : ℝ, 4⁻¹ * (kM2 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
          + 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p))
          + riemannXiKernel (u + p) * kM2 (u - p) * Real.cos (2 * x * p)) := by
    unfold cellDensity
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show u ^ 2 * (riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p))
        = 4⁻¹ * (kM2 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
          + 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p))
          + riemannXiKernel (u + p) * kM2 (u - p) * Real.cos (2 * x * p))
    have h := cell_u2_split u p
    linear_combination (-(Real.cos (2 * x * p)) / 4) * h
  have h2' : Integrable (fun p : ℝ =>
      2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p))) := h2.const_mul 2
  have hf12 : Integrable (fun p : ℝ =>
      kM2 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
      + 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p))) := h1.add h2'
  have a2 : (∫ p : ℝ, 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p)))
      = 2 * qleg2 x u := integral_const_mul _ _
  have a12 : (∫ p : ℝ, kM2 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
        + 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p)))
      = qleg1 x u + ∫ p : ℝ, 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p)) :=
    integral_add h1 h2'
  have a123 : (∫ p : ℝ, (kM2 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
        + 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p)))
        + riemannXiKernel (u + p) * kM2 (u - p) * Real.cos (2 * x * p))
      = (∫ p : ℝ, kM2 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
        + 2 * (kM1 (u + p) * kM1 (u - p) * Real.cos (2 * x * p))) + qleg3 x u :=
    integral_add hf12 h3
  rw [hA, integral_const_mul, a123, a12, a2]

theorem u2_cellDensity_integrable (x : ℝ) :
    Integrable (fun u : ℝ => u ^ 2 * cellDensity x u) := by
  have i1 := carrier_pairing2_integrable kM2_integrable kM2_measurable
    xiKernel_integrable riemannXiKernel_measurable x
  have i2 := carrier_pairing2_integrable kM1_integrable kM1_measurable
    kM1_integrable kM1_measurable x
  have i3 := carrier_pairing2_integrable xiKernel_integrable riemannXiKernel_measurable
    kM2_integrable kM2_measurable x
  have j1 : Integrable (qleg1 x) := i1
  have j2 : Integrable (qleg2 x) := i2
  have j3 : Integrable (qleg3 x) := i3
  exact (((j1.add (j2.const_mul 2)).add j3).const_mul (4⁻¹ : ℝ)).congr
    (u2_cellDensity_ae x).symm

/-- **THE SECOND MOMENT ON THE WHOLE CARRIER, EXACTLY.** -/
theorem u2_cellDensity_full (x : ℝ) :
    (∫ u : ℝ, u ^ 2 * cellDensity x u)
      = 4⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2) := by
  have i1 := carrier_pairing2_integrable kM2_integrable kM2_measurable
    xiKernel_integrable riemannXiKernel_measurable x
  have i2 := carrier_pairing2_integrable kM1_integrable kM1_measurable
    kM1_integrable kM1_measurable x
  have i3 := carrier_pairing2_integrable xiKernel_integrable riemannXiKernel_measurable
    kM2_integrable kM2_measurable x
  have j1 : Integrable (qleg1 x) := i1
  have j2 : Integrable (qleg2 x) := i2
  have j3 : Integrable (qleg3 x) := i3
  have v1 : (∫ u : ℝ, qleg1 x u)
      = 2⁻¹ * (cosMom kM2 x * cosMom riemannXiKernel x
          + sinMom kM2 x * sinMom riemannXiKernel x) :=
    carrier_pairing2 kM2_integrable kM2_measurable
      xiKernel_integrable riemannXiKernel_measurable x
  have v2 : (∫ u : ℝ, qleg2 x u)
      = 2⁻¹ * (cosMom kM1 x * cosMom kM1 x + sinMom kM1 x * sinMom kM1 x) :=
    carrier_pairing2 kM1_integrable kM1_measurable kM1_integrable kM1_measurable x
  have v3 : (∫ u : ℝ, qleg3 x u)
      = 2⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x
          + sinMom riemannXiKernel x * sinMom kM2 x) :=
    carrier_pairing2 xiKernel_integrable riemannXiKernel_measurable
      kM2_integrable kM2_measurable x
  have b2 : (∫ u : ℝ, 2 * qleg2 x u) = 2 * ∫ u : ℝ, qleg2 x u := integral_const_mul _ _
  have b12 : (∫ u : ℝ, qleg1 x u + 2 * qleg2 x u)
      = (∫ u : ℝ, qleg1 x u) + ∫ u : ℝ, 2 * qleg2 x u := integral_add j1 (j2.const_mul 2)
  have b123 : (∫ u : ℝ, (qleg1 x u + 2 * qleg2 x u) + qleg3 x u)
      = (∫ u : ℝ, qleg1 x u + 2 * qleg2 x u) + ∫ u : ℝ, qleg3 x u :=
    integral_add (j1.add (j2.const_mul 2)) j3
  rw [integral_congr_ae (u2_cellDensity_ae x), integral_const_mul, b123, b12, b2,
    v1, v2, v3, cosMom_kM1 x, sinMom_kM2 x, sinMom_xiKernel x]
  ring

theorem u2_cellDensity_even (x u : ℝ) :
    (-u) ^ 2 * cellDensity x (-u) = u ^ 2 * cellDensity x u := by
  rw [cellDensity_even]
  ring

/-- **THE SECOND MOMENT OF THE CELL DENSITY, EXACTLY.**  One product plus one square.
In readout coordinates `Ξ(x) = ∫Φcos(xt)dt` this bracket is `Ξ′(x)² − Ξ(x)Ξ″(x)`, the first
Laguerre expression. -/
theorem momentTwo_eq (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u)
      = 8⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x + sinMom kM1 x ^ 2) := by
  have habs := integral_comp_abs (f := fun u : ℝ => u ^ 2 * cellDensity x u)
  have hcongr : (∫ u : ℝ, |u| ^ 2 * cellDensity x |u|)
      = ∫ u : ℝ, u ^ 2 * cellDensity x u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show |u| ^ 2 * cellDensity x |u| = u ^ 2 * cellDensity x u
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      exact u2_cellDensity_even x u
  rw [hcongr, u2_cellDensity_full x] at habs
  linarith [habs]

/-! ### 6. The two unconditional fibres -/

/-- **THE SQUARE FLOOR.**  The sine channel contributes a manifest square, so the second
moment is bounded below by the cosine product alone — with no hypothesis. -/
theorem momentTwo_ge (x : ℝ) :
    8⁻¹ * (cosMom riemannXiKernel x * cosMom kM2 x)
      ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  rw [momentTwo_eq x]
  nlinarith [sq_nonneg (sinMom kM1 x)]

/-- Same-sign cosine moments suffice. -/
theorem momentTwo_nonneg_of_cos (x : ℝ)
    (h : 0 ≤ cosMom riemannXiKernel x * cosMom kM2 x) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  have := momentTwo_ge x
  nlinarith [this, h]

/-- **THE ZERO FIBRE, UNCONDITIONALLY.**  Wherever the readout's cosine moment vanishes —
i.e. at every real zero of `Ξ` — the second moment of the cell density is a perfect square,
`⅛·(sinMom (tΦ) x)²`, hence nonnegative with no hypothesis whatever. -/
theorem momentTwo_eq_sq_of_cosMom_zero {x : ℝ} (hx : cosMom riemannXiKernel x = 0) :
    (∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u) = 8⁻¹ * sinMom kM1 x ^ 2 := by
  rw [momentTwo_eq x, hx]
  ring

theorem momentTwo_nonneg_of_cosMom_zero {x : ℝ} (hx : cosMom riemannXiKernel x = 0) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  rw [momentTwo_eq_sq_of_cosMom_zero hx]
  positivity

/-- The `x = 0` fibre of the second moment: both surviving moments are integrals of
nonnegative integrands, and the sine channel is identically zero. -/
theorem momentTwo_zero_nonneg :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity 0 u := by
  rw [momentTwo_eq 0, sinMom_at_zero, cosMom_at_zero, cosMom_at_zero]
  have h0 : (0 : ℝ) ≤ ∫ t : ℝ, riemannXiKernel t :=
    integral_nonneg fun t => (C3B5.A1.riemannXiKernel_pos_all t).le
  have h2 : (0 : ℝ) ≤ ∫ t : ℝ, kM2 t := by
    refine integral_nonneg fun t => ?_
    have hpos : 0 < riemannXiKernel t := C3B5.A1.riemannXiKernel_pos_all t
    unfold kM2
    positivity
  nlinarith [mul_nonneg h0 h2]

end C3B12

section AxiomAudit
#print axioms C3B12.sq_le_four_mul_exp
#print axioms C3B12.sq_le_four_mul_exp_add_exp
#print axioms C3B12.xiKernel_integrable
#print axioms C3B12.kM1_integrable
#print axioms C3B12.kM2_integrable
#print axioms C3B12.sinMom_xiKernel
#print axioms C3B12.cosMom_kM1
#print axioms C3B12.sinMom_kM2
#print axioms C3B12.cellDensity_Ioi_eq_sq
#print axioms C3B12.cell_u2_split
#print axioms C3B12.u2_cellDensity_ae
#print axioms C3B12.u2_cellDensity_integrable
#print axioms C3B12.u2_cellDensity_full
#print axioms C3B12.momentTwo_eq
#print axioms C3B12.momentTwo_ge
#print axioms C3B12.momentTwo_nonneg_of_cos
#print axioms C3B12.momentTwo_eq_sq_of_cosMom_zero
#print axioms C3B12.momentTwo_nonneg_of_cosMom_zero
#print axioms C3B12.momentTwo_zero_nonneg
end AxiomAudit
