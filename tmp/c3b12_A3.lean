import c3b12_A2

/-!
# C3 batch 12, block A3 — the leaf identity for an **arbitrary even kernel**

Batch 11's `target_eq` was proved at the Riemann theta kernel.  Inspecting that proof, the
only properties of `Φ` it consumed are:

* `Φ` is even (`riemannXiKernel_neg`), and
* the four tilted weights `cosh(y·)Φ`, `sinh(y·)Φ`, `(·)sinh(y·)Φ`, `(·)cosh(y·)Φ` are
  integrable.

Nothing arithmetic, nothing about zeros, nothing about the theta series.  So the identity is
a **carrier fact**, not a zeta fact, and this block states it that way:

  `∫_{(0,∞)} u sinh(2yu) C_W(x,u) du = ¼ ( c_Q·c_P + s_S·s_R )`

for every even `W` whose four tilts are integrable, with `C_W(x,u) = ∫W(u+p)W(u−p)cos(2xp)dp`.

## What this does and does not generalise to

> **SCOPE CORRECTION (OpenAI adjudication, 2026-08-25).**  An earlier draft of this file and
> of the batch-12 ledger said that "any Dirichlet character's theta kernel — or any even
> kernel of an automorphic completed `L`-function — is admissible here with no new work" and
> that the engine is "character-blind".  **That claim is withdrawn: it is false as stated.**
>
> `gen_target_eq` is a theorem about a **real-valued** `W : ℝ → ℝ` that is **even**, with the
> four real tilts integrable.  Every ingredient is real: `cosMom`/`sinMom` are real integrals,
> `carrier_pairing2` is stated for `ℝ → ℝ`, and the parity lemmas use `W(−t) = W(t)`.
>
> The theta kernel of a **complex** (non-real) Dirichlet character is **complex-valued**, and
> its reflection law is not `W(−t) = W(t)` but a conjugation-and-root-number law relating the
> kernel of `χ` to the kernel of `χ̄` with the factor `ε(χ)`.  Extending the leaf identity to
> that setting therefore needs **three things that do not exist in this repository**:
>   1. a **complex-kernel** two-weight pairing theorem (`carrier_pairing2` re-proved for
>      `ℝ → ℂ`, with `conj` in the correct slot, since `|M|²` becomes `M·conj M` across a
>      `χ`/`χ̄` pair rather than a square);
>   2. the **root-number / conjugation law** `W_χ(−t) = ε(χ)·W_{χ̄}(t)` (or its completed
>      analogue) in compiled form, replacing `hev`;
>   3. its **own integrability bridge** — the Gaussian majorant of batch 10 is proved for
>      `riemannXiKernel` only, and a per-character majorant with conductor dependence would
>      have to be established.
>
> What *is* covered with no new work: real even kernels — e.g. the trivial character, and any
> **real** (quadratic) character's kernel once its evenness and four integrabilities are
> supplied.  Nothing beyond that is claimed, and no GRH statement follows from this file.

**The generalisation is the exact statement of the instrument's limit.**  Because the
identity holds for *every* even integrable kernel, and because `Φ_c(t) = e^{−t²}(2 + cos 2t)`
is such a kernel with a strictly negative leaf at `x₀ = arccosh(2e)`, `y ∈ [2.34, 3.10]`
(batch 11 FAILED §F1, closed form `M_c(z) = √π e^{z²/4}(2 + e^{−1}cos z)`), **no argument
that uses only evenness, positivity and this engine can produce the sign.**  That is a
property of the certificate class, exhibited by a counterexample rather than asserted.

SCOPE: one identity, with its hypotheses displayed.  The Φ-instance is batch 11's
`C3B11.target_eq`; nothing here mentions zeros.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B12

open CriticalLinePhasor.C3B4B
open C3B10
open C3B11

variable (W : ℝ → ℝ)

/-- The cell density of a general carrier kernel. -/
def genCell (W : ℝ → ℝ) (x u : ℝ) : ℝ :=
  ∫ p : ℝ, W (u + p) * W (u - p) * Real.cos (2 * x * p)

def gQ (W : ℝ → ℝ) (y t : ℝ) : ℝ := Real.cosh (y * t) * W t
def gS (W : ℝ → ℝ) (y t : ℝ) : ℝ := Real.sinh (y * t) * W t
def gP (W : ℝ → ℝ) (y t : ℝ) : ℝ := t * Real.sinh (y * t) * W t
def gR (W : ℝ → ℝ) (y t : ℝ) : ℝ := t * Real.cosh (y * t) * W t

variable {W}

theorem gQ_measurable (hm : Measurable W) (y : ℝ) : Measurable (gQ W y) :=
  (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).measurable.mul hm

theorem gS_measurable (hm : Measurable W) (y : ℝ) : Measurable (gS W y) :=
  (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).measurable.mul hm

theorem gP_measurable (hm : Measurable W) (y : ℝ) : Measurable (gP W y) :=
  (measurable_id.mul
    (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).measurable).mul hm

theorem gR_measurable (hm : Measurable W) (y : ℝ) : Measurable (gR W y) :=
  (measurable_id.mul
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).measurable).mul hm

/-! ### Parity -/

theorem gQ_even (hev : ∀ t : ℝ, W (-t) = W t) (y t : ℝ) : gQ W y (-t) = gQ W y t := by
  unfold gQ; rw [show y * -t = -(y * t) by ring, Real.cosh_neg, hev]

theorem gS_odd (hev : ∀ t : ℝ, W (-t) = W t) (y t : ℝ) : gS W y (-t) = -gS W y t := by
  unfold gS; rw [show y * -t = -(y * t) by ring, Real.sinh_neg, hev]; ring

theorem gP_even (hev : ∀ t : ℝ, W (-t) = W t) (y t : ℝ) : gP W y (-t) = gP W y t := by
  unfold gP; rw [show y * -t = -(y * t) by ring, Real.sinh_neg, hev]; ring

theorem gR_odd (hev : ∀ t : ℝ, W (-t) = W t) (y t : ℝ) : gR W y (-t) = -gR W y t := by
  unfold gR; rw [show y * -t = -(y * t) by ring, Real.cosh_neg, hev]; ring

/-! ### The split, verbatim from batch 11 with `W` in place of `Φ` -/

theorem gen_cell_weight_split (W : ℝ → ℝ) (y u p : ℝ) :
    gP W y (u + p) * gQ W y (u - p) + gR W y (u + p) * gS W y (u - p)
      + gS W y (u + p) * gR W y (u - p) + gQ W y (u + p) * gP W y (u - p)
      = 2 * (gY y u * (W (u + p) * W (u - p))) := by
  unfold gP gQ gR gS gY
  have hadd : Real.sinh (y * (u + p) + y * (u - p))
      = Real.sinh (y * (u + p)) * Real.cosh (y * (u - p))
        + Real.cosh (y * (u + p)) * Real.sinh (y * (u - p)) := Real.sinh_add _ _
  have hcol : y * (u + p) + y * (u - p) = 2 * y * u := by ring
  rw [hcol] at hadd
  linear_combination (-(2 * u * W (u + p) * W (u - p))) * hadd

def gleg1 (W : ℝ → ℝ) (x y u : ℝ) : ℝ :=
  ∫ p : ℝ, gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
def gleg2 (W : ℝ → ℝ) (x y u : ℝ) : ℝ :=
  ∫ p : ℝ, gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p)
def gleg3 (W : ℝ → ℝ) (x y u : ℝ) : ℝ :=
  ∫ p : ℝ, gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p)
def gleg4 (W : ℝ → ℝ) (x y u : ℝ) : ℝ :=
  ∫ p : ℝ, gQ W y (u + p) * gP W y (u - p) * Real.cos (2 * x * p)

variable (hm : Measurable W)
  (hQ : ∀ y : ℝ, Integrable (gQ W y)) (hS : ∀ y : ℝ, Integrable (gS W y))
  (hP : ∀ y : ℝ, Integrable (gP W y)) (hR : ∀ y : ℝ, Integrable (gR W y))

include hm hQ hS hP hR in
theorem gen_gY_ae (x y : ℝ) :
    (fun u : ℝ => gY y u * genCell W x u)
      =ᵐ[volume] fun u : ℝ =>
        2⁻¹ * (gleg1 W x y u + gleg2 W x y u + gleg3 W x y u + gleg4 W x y u) := by
  filter_upwards [slice_ae (hP y) (gP_measurable hm y) (hQ y) (gQ_measurable hm y) x,
    slice_ae (hR y) (gR_measurable hm y) (hS y) (gS_measurable hm y) x,
    slice_ae (hS y) (gS_measurable hm y) (hR y) (gR_measurable hm y) x,
    slice_ae (hQ y) (gQ_measurable hm y) (hP y) (gP_measurable hm y) x]
    with u h1 h2 h3 h4
  show gY y u * genCell W x u
      = 2⁻¹ * (gleg1 W x y u + gleg2 W x y u + gleg3 W x y u + gleg4 W x y u)
  have hA : gY y u * genCell W x u
      = ∫ p : ℝ, 2⁻¹ * (gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
          + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p)
          + gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p)
          + gQ W y (u + p) * gP W y (u - p) * Real.cos (2 * x * p)) := by
    unfold genCell
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show gY y u * (W (u + p) * W (u - p) * Real.cos (2 * x * p))
        = 2⁻¹ * (gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
          + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p)
          + gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p)
          + gQ W y (u + p) * gP W y (u - p) * Real.cos (2 * x * p))
    have h := gen_cell_weight_split W y u p
    linear_combination (-(Real.cos (2 * x * p)) / 2) * h
  have hf12 : Integrable (fun p : ℝ =>
      gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
      + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p)) := h1.add h2
  have hf123 : Integrable (fun p : ℝ =>
      (gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
      + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p))
      + gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p)) := hf12.add h3
  have a12 : (∫ p : ℝ, gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
        + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p))
      = gleg1 W x y u + gleg2 W x y u := integral_add h1 h2
  have a123 : (∫ p : ℝ, (gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
        + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p))
        + gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p))
      = (∫ p : ℝ, gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
        + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p)) + gleg3 W x y u :=
    integral_add hf12 h3
  have a1234 : (∫ p : ℝ, ((gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
        + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p))
        + gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p))
        + gQ W y (u + p) * gP W y (u - p) * Real.cos (2 * x * p))
      = (∫ p : ℝ, (gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
        + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p))
        + gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p)) + gleg4 W x y u :=
    integral_add hf123 h4
  rw [hA, integral_const_mul]
  have hsum : (∫ p : ℝ, gP W y (u + p) * gQ W y (u - p) * Real.cos (2 * x * p)
        + gR W y (u + p) * gS W y (u - p) * Real.cos (2 * x * p)
        + gS W y (u + p) * gR W y (u - p) * Real.cos (2 * x * p)
        + gQ W y (u + p) * gP W y (u - p) * Real.cos (2 * x * p))
      = gleg1 W x y u + gleg2 W x y u + gleg3 W x y u + gleg4 W x y u := by
    rw [a1234, a123, a12]
  rw [hsum]

include hm hQ hS hP hR in
theorem gen_gY_full (x y : ℝ) :
    (∫ u : ℝ, gY y u * genCell W x u)
      = 2⁻¹ * (cosMom (gQ W y) x * cosMom (gP W y) x
          + sinMom (gS W y) x * sinMom (gR W y) x
          + (cosMom (gR W y) x * cosMom (gS W y) x + sinMom (gP W y) x * sinMom (gQ W y) x)) := by
  have j1 : Integrable (gleg1 W x y) :=
    carrier_pairing2_integrable (hP y) (gP_measurable hm y) (hQ y) (gQ_measurable hm y) x
  have j2 : Integrable (gleg2 W x y) :=
    carrier_pairing2_integrable (hR y) (gR_measurable hm y) (hS y) (gS_measurable hm y) x
  have j3 : Integrable (gleg3 W x y) :=
    carrier_pairing2_integrable (hS y) (gS_measurable hm y) (hR y) (gR_measurable hm y) x
  have j4 : Integrable (gleg4 W x y) :=
    carrier_pairing2_integrable (hQ y) (gQ_measurable hm y) (hP y) (gP_measurable hm y) x
  have v1 : (∫ u : ℝ, gleg1 W x y u)
      = 2⁻¹ * (cosMom (gP W y) x * cosMom (gQ W y) x
          + sinMom (gP W y) x * sinMom (gQ W y) x) :=
    carrier_pairing2 (hP y) (gP_measurable hm y) (hQ y) (gQ_measurable hm y) x
  have v2 : (∫ u : ℝ, gleg2 W x y u)
      = 2⁻¹ * (cosMom (gR W y) x * cosMom (gS W y) x
          + sinMom (gR W y) x * sinMom (gS W y) x) :=
    carrier_pairing2 (hR y) (gR_measurable hm y) (hS y) (gS_measurable hm y) x
  have v3 : (∫ u : ℝ, gleg3 W x y u)
      = 2⁻¹ * (cosMom (gS W y) x * cosMom (gR W y) x
          + sinMom (gS W y) x * sinMom (gR W y) x) :=
    carrier_pairing2 (hS y) (gS_measurable hm y) (hR y) (gR_measurable hm y) x
  have v4 : (∫ u : ℝ, gleg4 W x y u)
      = 2⁻¹ * (cosMom (gQ W y) x * cosMom (gP W y) x
          + sinMom (gQ W y) x * sinMom (gP W y) x) :=
    carrier_pairing2 (hQ y) (gQ_measurable hm y) (hP y) (gP_measurable hm y) x
  have b12 : (∫ u : ℝ, gleg1 W x y u + gleg2 W x y u)
      = (∫ u : ℝ, gleg1 W x y u) + ∫ u : ℝ, gleg2 W x y u := integral_add j1 j2
  have b123 : (∫ u : ℝ, (gleg1 W x y u + gleg2 W x y u) + gleg3 W x y u)
      = (∫ u : ℝ, gleg1 W x y u + gleg2 W x y u) + ∫ u : ℝ, gleg3 W x y u :=
    integral_add (j1.add j2) j3
  have b1234 : (∫ u : ℝ, ((gleg1 W x y u + gleg2 W x y u) + gleg3 W x y u) + gleg4 W x y u)
      = (∫ u : ℝ, (gleg1 W x y u + gleg2 W x y u) + gleg3 W x y u) + ∫ u : ℝ, gleg4 W x y u :=
    integral_add ((j1.add j2).add j3) j4
  rw [integral_congr_ae (gen_gY_ae hm hQ hS hP hR x y), integral_const_mul,
    b1234, b123, b12, v1, v2, v3, v4]
  ring

include hm hQ hS hP hR in
/-- **THE LEAF IDENTITY, FOR EVERY REAL-VALUED EVEN KERNEL.**  Hypotheses displayed in full:
`W : ℝ → ℝ` measurable, `W(−t) = W(t)`, and integrability of the four real tilted weights.
Nothing arithmetic — and, equally, nothing complex: this does **not** cover complex Dirichlet
characters, whose kernels are complex-valued and obey a root-number/conjugation law rather
than `hev`.  See the scope correction in the file header. -/
theorem gen_target_eq (hev : ∀ t : ℝ, W (-t) = W t) (x y : ℝ) :
    (∫ u in Ioi (0 : ℝ), gY y u * genCell W x u)
      = 4⁻¹ * (cosMom (gQ W y) x * cosMom (gP W y) x
          + sinMom (gS W y) x * sinMom (gR W y) x) := by
  have hcell_even : ∀ u : ℝ, genCell W x (-u) = genCell W x u := by
    intro u
    unfold genCell
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show W (-u + p) * W (-u - p) * Real.cos (2 * x * p)
        = W (u + p) * W (u - p) * Real.cos (2 * x * p)
    have h1 : W (-u + p) = W (u - p) := by rw [show -u + p = -(u - p) by ring, hev]
    have h2 : W (-u - p) = W (u + p) := by rw [show -u - p = -(u + p) by ring, hev]
    rw [h1, h2]; ring
  have habs := integral_comp_abs (f := fun u : ℝ => gY y u * genCell W x u)
  have hcongr : (∫ u : ℝ, gY y |u| * genCell W x |u|)
      = ∫ u : ℝ, gY y u * genCell W x u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show gY y |u| * genCell W x |u| = gY y u * genCell W x u
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, hcell_even u]
      unfold gY
      rw [show 2 * y * -u = -(2 * y * u) by ring, Real.sinh_neg]
      ring
  rw [hcongr, gen_gY_full hm hQ hS hP hR x y,
    sinMom_of_even (gQ_even hev y) x, sinMom_of_even (gP_even hev y) x,
    cosMom_of_odd (gS_odd hev y) x, cosMom_of_odd (gR_odd hev y) x] at habs
  linarith [habs]

end C3B12

section AxiomAudit
#print axioms C3B12.gen_cell_weight_split
#print axioms C3B12.gQ_even
#print axioms C3B12.gS_odd
#print axioms C3B12.gP_even
#print axioms C3B12.gR_odd
#print axioms C3B12.gen_gY_ae
#print axioms C3B12.gen_gY_full
#print axioms C3B12.gen_target_eq
end AxiomAudit
