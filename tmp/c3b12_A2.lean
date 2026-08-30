import c3b12_A1

/-!
# C3 batch 12, block A2 — structural attacks on the four-moment leaf

Six attacks, each carried to a compiled statement or an explicit failure.

**(A) The elementary factor.**

> **UNCOMPILED ANALYTIC BRIDGE, NAMED (OpenAI adjudication, 2026-08-25).**  What compiles
> below is **only the algebraic identity** `elementary_factor_split`, a statement about three
> arbitrary complex numbers `z, N, Nd`.  The *analytic bridge* that would instantiate it at
> the actual `Ξ`-kernel — `M(z) = (z²−¼)N(z)` with `N(z) = ∫ψ(t)e^{zt}dt`, obtained by
> integrating by parts twice against `Φ = ψ″ − ψ/4`
> (`CriticalLinePhasor.XiKernelBridge.riemannXiKernel_eq_op`) — is **NOT COMPILED** anywhere
> in this batch.  It needs decay of `ψ` and `ψ′` to kill the boundary terms plus a
> differentiation-under-the-integral step; neither is formalised.  The factorisation is used
> here only as pencil reasoning, and is checked numerically at
> `tmp/c3b12_num_out.txt` §P3.  Do not cite it as compiled.

Informally: `d²/dt²[cosh(yt)cos(xt)] = (y²−x²)cosh cos − 2xy sinh sin` acts on the surviving
moment pair as multiplication by `z² = (y+ix)²`, so the leaf `Re[M′·conj M]` would split as

  `Re[M′ conj M] = 2·Re z·(|z|² − ¼)·|N|²  +  |z²−¼|²·Re[N′ conj N]`.

`elementary_factor_split` compiles that identity as pure complex algebra, with no hypothesis.
Conditional on the uncompiled bridge, it localises the difficulty: the elementary factor's
contribution is **negative inside the disc `|s−½| < ½`** and positive outside.  Measured
(§P3) — and this corrects an earlier draft of this file — the **`Γζ` term has the opposite
sign at every sampled point**, so it is *not* the case that both are positive outside the
disc; which of the two carries the leaf swaps exactly across the circle.

**(B) The Gram/Hankel instrument, exactly.**  `lagrange_identity` says the leaf and the
"rotation" `A·B′ − B·A′` are the two orthogonal components of a vector of *known* length
`√((A²+B²)(A′²+B′²))`.  The Gram determinant reads the length; the leaf is the other
component.  **A determinant instrument therefore cannot decide the leaf**, and the reason is
in the identity, not in a claim about it.

**(C) The helix/anti-helix branch combination.**  `antihelix_swap` compiles the exchange
`p ↔ u` of the two branches, and shows the carrier measure is invariant under it.  The
conjugate branch therefore **equals** the helix branch rather than cancelling against it:
there is no anti-helix cancellation available for this functional.

**(D) The theta-mode diagonal.**  `modeLam_diag` compiles `modeLam n n = 0`, so every
diagonal mode carries the chart clock at value `cos 0 = 1`: the diagonal is sign-definite.
Domination of the off-diagonal by the diagonal is refuted numerically (batch 9); recorded in
the ledger, not asserted here.

**(E) The half-line odd moments are outside the engine.**  `carrier_pairing2` evaluates
full-line integrals; folding to `(0,∞)` needs the integrand even in the cell centre.  The
Hankel matrix of the moments `mₖ = ∫_{(0,∞)} u^k C` needs `m₁`, whose integrand `u·C(x,u)`
is **odd**, so its full-line integral is `0` and carries no information about the half-line
value.  `u_cellDensity_integrable` compiles the genuine integrability and
`oddMoment_full_zero` the genuine evaluation — **not** a parity argument resting on Lean's
zero-convention for non-integrable functions (see §(E) below).  The Hankel/Stieltjes route of
`hp_pencil_v2` Prop. 3.5 is therefore not reachable from this engine without a new device.

**(F) The complex dictionary.**  `leaf_eq_re` records the leaf as the real part of a single
complex product, which is the form every one of the above attacks actually uses.

**(G) The honest reduction of the sub-leaf.**  `momentTwo_nonneg_of_square_dominates`
replaces the ledger's earlier *false* proposal `0 ≤ c₀·c₂` (refuted at `x = 7`).

SCOPE: algebraic identities, one genuine integrability + evaluation, one reduction.
Nothing here decides the leaf.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B12

open CriticalLinePhasor.ThetaWronskianSuzukiGram
open C3B6.Theta
open C3B10
open C3B11

/-! ### (A) The elementary factor `z² − c` -/

/-- **THE ELEMENTARY-FACTOR SPLIT.**  If `M = (z²−c)·N` with `c` real, then the leaf
functional of `M` splits exactly into an explicit scalar term and the leaf functional of `N`,
scaled by `|z²−c|²`.  No hypothesis. -/
theorem elementary_factor_split (c : ℝ) (z N Nd : ℂ) :
    ((z * N + z * N + (z ^ 2 - (c : ℂ)) * Nd) * (starRingEnd ℂ) ((z ^ 2 - (c : ℂ)) * N)).re
      = 2 * z.re * (Complex.normSq z - c) * Complex.normSq N
        + Complex.normSq (z ^ 2 - (c : ℂ)) * (Nd * (starRingEnd ℂ) N).re := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The scalar contributed by the elementary factor, at `z = y + ix` and `c = ¼`. -/
theorem elementary_scalar (y x : ℝ) :
    2 * ((y : ℂ) + (x : ℂ) * Complex.I).re
        * (Complex.normSq ((y : ℂ) + (x : ℂ) * Complex.I) - 4⁻¹)
      = 2 * y * (y ^ 2 + x ^ 2 - 4⁻¹) := by
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.normSq_apply]
  ring

/-- **OUTSIDE THE DISC the elementary factor helps.**  For `y ≥ 0` and `|z|² ≥ ¼` its
contribution to the leaf is nonnegative. -/
theorem elementary_term_nonneg {y x n : ℝ} (hy : 0 ≤ y) (hd : 4⁻¹ ≤ y ^ 2 + x ^ 2)
    (hn : 0 ≤ n) : 0 ≤ 2 * y * (y ^ 2 + x ^ 2 - 4⁻¹) * n := by
  have h1 : (0 : ℝ) ≤ y ^ 2 + x ^ 2 - 4⁻¹ := by linarith
  positivity

/-- **INSIDE THE DISC it fights.**  For `y > 0`, `|z|² < ¼` and `N ≠ 0` the elementary
factor's contribution is strictly negative: on `|s − ½| < ½` the leaf's sign must come
entirely from the non-elementary part. -/
theorem elementary_term_neg {y x n : ℝ} (hy : 0 < y) (hd : y ^ 2 + x ^ 2 < 4⁻¹)
    (hn : 0 < n) : 2 * y * (y ^ 2 + x ^ 2 - 4⁻¹) * n < 0 := by
  have h1 : y ^ 2 + x ^ 2 - 4⁻¹ < 0 := by linarith
  have h2 : (0 : ℝ) < 2 * y := by linarith
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h2 h1) hn

/-! ### (B) The Gram/Hankel instrument -/

/-- **THE LAGRANGE IDENTITY.**  The leaf `A A′ + B B′` and the rotation `A B′ − B A′` are
orthogonal components of a vector whose length is fixed by the two channel norms.  A
determinant/Gram instrument measures the length; the leaf is the *other* component, so no
such instrument can produce its sign. -/
theorem lagrange_identity (A A' B B' : ℝ) :
    (A * A' + B * B') ^ 2 + (A * B' - B * A') ^ 2 = (A ^ 2 + B ^ 2) * (A' ^ 2 + B' ^ 2) := by
  ring

/-- The `2×2` Gram determinant of the two channel vectors is the squared rotation — again
sign-blind in the leaf. -/
theorem gram_det_eq (A A' B B' : ℝ) :
    (A ^ 2 + B ^ 2) * (A' ^ 2 + B' ^ 2) - (A * A' + B * B') ^ 2 = (A * B' - B * A') ^ 2 := by
  ring

/-! ### (C) Helix / anti-helix: the branches coincide -/

/-- **THE ANTI-HELIX SWAP.**  Exchanging the cell centre `u` with the half-gap `p` leaves the
carrier product invariant, because `Φ` is even.  Hence the conjugate (anti-helix) branch of
the symmetrised leaf **equals** the helix branch; there is no cancellation between them. -/
theorem antihelix_swap (u p : ℝ) :
    riemannXiKernel (p + u) * riemannXiKernel (p - u)
      = riemannXiKernel (u + p) * riemannXiKernel (u - p) := by
  have h : riemannXiKernel (p - u) = riemannXiKernel (u - p) := by
    rw [show p - u = -(u - p) by ring, riemannXiKernel_neg]
  rw [h, add_comm p u]

/-- The cell density is invariant under the same swap composed with the chart clock: this is
the exact sense in which the carrier weight and the chart clock exchange places. -/
theorem antihelix_cellDensity (x u : ℝ) : cellDensity x (-u) = cellDensity x u :=
  cellDensity_even x u

/-! ### (D) The theta-mode diagonal -/

open C3B6.Bessel in
/-- The diagonal mode carries no chart clock: `modeLam n n = 0`, so `cos(x·modeLam n n) = 1`
for every `x`.  The diagonal of the theta double sum is therefore sign-definite. -/
theorem modeLam_diag (n : ℕ) : modeLam n n = 0 := by
  unfold modeLam
  rw [div_self (by positivity : ((n : ℝ) + 1) ≠ 0), Real.log_one]

open C3B6.Bessel in
theorem modeLam_diag_cos (x : ℝ) (n : ℕ) : Real.cos (x * modeLam n n) = 1 := by
  rw [modeLam_diag, mul_zero, Real.cos_zero]

/-! ### (E) The half-line odd moments are outside this engine

**CORRECTED (OpenAI adjudication, 2026-08-25).**  The first draft proved `∫_ℝ u·C = 0` by
parity alone, with no integrability hypothesis.  That proof is **not admissible**: Lean's
Bochner integral is `0` by convention on non-integrable functions, so a parity argument
without integrability proves the statement in a way that carries no analytic content.  It is
replaced by the genuine route — the first moment is evaluated by the *same* two-weight
engine, which supplies integrability and the value together.  The split is
`2u = (u+p) + (u−p)`: two legs instead of the three used for `u²`. -/

def uleg1 (x u : ℝ) : ℝ :=
  ∫ p : ℝ, kM1 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
def uleg2 (x u : ℝ) : ℝ :=
  ∫ p : ℝ, riemannXiKernel (u + p) * kM1 (u - p) * Real.cos (2 * x * p)

theorem cell_u1_split (u p : ℝ) :
    kM1 (u + p) * riemannXiKernel (u - p) + riemannXiKernel (u + p) * kM1 (u - p)
      = 2 * (u * (riemannXiKernel (u + p) * riemannXiKernel (u - p))) := by
  unfold kM1
  ring

theorem u_cellDensity_ae (x : ℝ) :
    (fun u : ℝ => u * cellDensity x u)
      =ᵐ[volume] fun u : ℝ => 2⁻¹ * (uleg1 x u + uleg2 x u) := by
  filter_upwards [slice_ae kM1_integrable kM1_measurable
      xiKernel_integrable riemannXiKernel_measurable x,
    slice_ae xiKernel_integrable riemannXiKernel_measurable kM1_integrable kM1_measurable x]
    with u h1 h2
  show u * cellDensity x u = 2⁻¹ * (uleg1 x u + uleg2 x u)
  have hA : u * cellDensity x u
      = ∫ p : ℝ, 2⁻¹ * (kM1 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
          + riemannXiKernel (u + p) * kM1 (u - p) * Real.cos (2 * x * p)) := by
    unfold cellDensity
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show u * (riemannXiKernel (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p))
        = 2⁻¹ * (kM1 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
          + riemannXiKernel (u + p) * kM1 (u - p) * Real.cos (2 * x * p))
    have h := cell_u1_split u p
    linear_combination (-(Real.cos (2 * x * p)) / 2) * h
  have a12 : (∫ p : ℝ, kM1 (u + p) * riemannXiKernel (u - p) * Real.cos (2 * x * p)
        + riemannXiKernel (u + p) * kM1 (u - p) * Real.cos (2 * x * p))
      = uleg1 x u + uleg2 x u := integral_add h1 h2
  rw [hA, integral_const_mul, a12]

/-- **THE FIRST MOMENT IS GENUINELY INTEGRABLE** — proved from the engine, not assumed and
not sidestepped. -/
theorem u_cellDensity_integrable (x : ℝ) :
    Integrable (fun u : ℝ => u * cellDensity x u) := by
  have j1 : Integrable (uleg1 x) :=
    carrier_pairing2_integrable kM1_integrable kM1_measurable
      xiKernel_integrable riemannXiKernel_measurable x
  have j2 : Integrable (uleg2 x) :=
    carrier_pairing2_integrable xiKernel_integrable riemannXiKernel_measurable
      kM1_integrable kM1_measurable x
  exact ((j1.add j2).const_mul (2⁻¹ : ℝ)).congr (u_cellDensity_ae x).symm

/-- **THE ENGINE'S BOUNDARY, PROVED PROPERLY.**  The first moment's full-line integral is
`0`, and this is a genuine evaluation: the integrand is integrable
(`u_cellDensity_integrable`) and the value comes from the two-weight pairing, whose two
terms vanish because `cosMom kM1 = 0` and `sinMom Φ = 0`.  No appeal to the zero-convention.

Consequence for the Hankel/Stieltjes route: this engine computes full-line integrals, and
the full-line first moment is `0`, so it carries **no** information about the half-line value
`∫_{(0,∞)} u·C` that the route requires. -/
theorem oddMoment_full_zero (x : ℝ) : (∫ u : ℝ, u * cellDensity x u) = 0 := by
  have j1 : Integrable (uleg1 x) :=
    carrier_pairing2_integrable kM1_integrable kM1_measurable
      xiKernel_integrable riemannXiKernel_measurable x
  have j2 : Integrable (uleg2 x) :=
    carrier_pairing2_integrable xiKernel_integrable riemannXiKernel_measurable
      kM1_integrable kM1_measurable x
  have v1 : (∫ u : ℝ, uleg1 x u)
      = 2⁻¹ * (cosMom kM1 x * cosMom riemannXiKernel x
          + sinMom kM1 x * sinMom riemannXiKernel x) :=
    carrier_pairing2 kM1_integrable kM1_measurable
      xiKernel_integrable riemannXiKernel_measurable x
  have v2 : (∫ u : ℝ, uleg2 x u)
      = 2⁻¹ * (cosMom riemannXiKernel x * cosMom kM1 x
          + sinMom riemannXiKernel x * sinMom kM1 x) :=
    carrier_pairing2 xiKernel_integrable riemannXiKernel_measurable
      kM1_integrable kM1_measurable x
  have b12 : (∫ u : ℝ, uleg1 x u + uleg2 x u)
      = (∫ u : ℝ, uleg1 x u) + ∫ u : ℝ, uleg2 x u := integral_add j1 j2
  rw [integral_congr_ae (u_cellDensity_ae x), integral_const_mul, b12, v1, v2,
    cosMom_kM1 x, sinMom_xiKernel x]
  ring

/-! ### (G) The honest reduction of the sub-leaf

**CORRECTED (OpenAI adjudication).**  The batch-12 ledger proposed
`0 ≤ cosMom Φ x · cosMom kM2 x` as a "smallest sub-fibre".  **That is false**: at `x = 7`,
`cosMom Φ 7 = +3.0440904857e-01` and `cosMom kM2 7 = −1.9494121616e-02`
(`tmp/c3b12_num_out.txt` §P2), so the product is negative.  The correct decomposition splits
on the sign of that product; only the negative region is open, and there the whole content is
square domination. -/

/-- On `{c₀·c₂ ≥ 0}` the sub-leaf is already compiled (`momentTwo_nonneg_of_cos`); on
`{c₀·c₂ < 0}` the entire content is that the sine square dominates.  This is the reduction,
and it asserts no sign that is not proved. -/
theorem momentTwo_nonneg_of_square_dominates {x : ℝ}
    (h : cosMom riemannXiKernel x * cosMom kM2 x < 0 →
      |cosMom riemannXiKernel x * cosMom kM2 x| ≤ sinMom kM1 x ^ 2) :
    0 ≤ ∫ u in Ioi (0 : ℝ), u ^ 2 * cellDensity x u := by
  rw [momentTwo_eq x]
  rcases lt_or_ge (cosMom riemannXiKernel x * cosMom kM2 x) 0 with hneg | hpos
  · have hb := h hneg
    rw [abs_of_neg hneg] at hb
    nlinarith [hb]
  · nlinarith [sq_nonneg (sinMom kM1 x), hpos]

/-! ### (F) The complex dictionary -/

/-- The leaf is the real part of one complex product: `A A′ + B B′ = Re[(A′+iB′)·conj(A+iB)]`.
Every attack above is this identity read in a different chart. -/
theorem leaf_eq_re (A A' B B' : ℝ) :
    A * A' + B * B'
      = (((A' : ℂ) + (B' : ℂ) * Complex.I)
          * (starRingEnd ℂ) ((A : ℂ) + (B : ℂ) * Complex.I)).re := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- And the rotation is its imaginary part. -/
theorem rotation_eq_im (A A' B B' : ℝ) :
    B' * A - A' * B
      = (((A' : ℂ) + (B' : ℂ) * Complex.I)
          * (starRingEnd ℂ) ((A : ℂ) + (B : ℂ) * Complex.I)).im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

end C3B12

section AxiomAudit
#print axioms C3B12.elementary_factor_split
#print axioms C3B12.elementary_scalar
#print axioms C3B12.elementary_term_nonneg
#print axioms C3B12.elementary_term_neg
#print axioms C3B12.lagrange_identity
#print axioms C3B12.gram_det_eq
#print axioms C3B12.antihelix_swap
#print axioms C3B12.antihelix_cellDensity
#print axioms C3B12.modeLam_diag
#print axioms C3B12.modeLam_diag_cos
#print axioms C3B12.cell_u1_split
#print axioms C3B12.u_cellDensity_ae
#print axioms C3B12.u_cellDensity_integrable
#print axioms C3B12.oddMoment_full_zero
#print axioms C3B12.momentTwo_nonneg_of_square_dominates
#print axioms C3B12.leaf_eq_re
#print axioms C3B12.rotation_eq_im
end AxiomAudit
