import c3b6_A2
import c3b5_A2
import c3b5_A3

/-!
# C3 batch 6, block A3 — obligation A discharged: the radial combination is positive

Batch 5 left `C3B5.A3.logDeriv_le_one` and `C3B5.A2.radial_pos_of_ge_eight` as *abstract
consumers*: both took the logarithmic-derivative ceiling `ρ ≤ 1` and the relation
`K′ = −(ρ + 1/(2A))K` as hypotheses.  This file removes both hypotheses by supplying the
actual object.

With `K = kix 0 x`, `K′ = kix 1 x`, `K″ = kix 2 x` (block A2) and the Liouville gauge
`z(A) = √A·K(A)`:

* `hasDerivAt_zFun`, `hasDerivAt_zDer` — `z′` and `z″` as explicit functions.
* `zDD_eq` — **`z″ = q·z` with `q(A) = 1 − (x²+¼)/A²`**, by feeding the compiled
  `kix_bessel_ode` into `C3B5.A3.liouville_normal_form` at `r = √A`.
* `tendsto_zSum` — `z + z′ → 0` at `+∞`, from the block-A1 decay bound `|kix j x A| ≤
  e^{−(A−1)}·C_j`.
* `logDeriv_kix_le_one` — **the ceiling `−z′/z ≤ 1`, concluded**, via
  `C3B5.A3.logDeriv_le_one`.
* `radial_kix_pos` — **the deliverable**:
  `0 < (A²+9)·K_{ix}(A) + 6A·K′_{ix}(A)` for `A ≥ a`, whenever `a ≥ 8` and `K_{ix} > 0`
  on `[a,∞)`.

The only remaining hypothesis on the final signature is the **positivity of `K_{ix}`
itself** on the ray — not a derivative bound, and not the conclusion in disguise: it is a
statement about the value of the function, attacked separately in block A4.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Bessel

/-! ### 1. The Liouville gauge and its two derivatives -/

/-- `z(A) = √A·K_{ix}(A)`. -/
def zFun (x A : ℝ) : ℝ := Real.sqrt A * kix 0 x A

/-- `z′(A) = (1/(2√A))·K + √A·K′`. -/
def zDer (x A : ℝ) : ℝ :=
  1 / (2 * Real.sqrt A) * kix 0 x A + Real.sqrt A * kix 1 x A

/-- `z″(A) = −(1/(4A√A))·K + (1/√A)·K′ + √A·K″`. -/
def zDD (x A : ℝ) : ℝ :=
  -(1 / (4 * (Real.sqrt A) ^ 3)) * kix 0 x A + 1 / Real.sqrt A * kix 1 x A
    + Real.sqrt A * kix 2 x A

/-- The Liouville potential `q(A) = 1 − (x²+¼)/A²`. -/
def qFun (x A : ℝ) : ℝ := 1 - (x ^ 2 + 1 / 4) / A ^ 2

theorem qFun_le_one (x : ℝ) (A : ℝ) : qFun x A ≤ 1 := by
  unfold qFun
  have h : (0 : ℝ) ≤ (x ^ 2 + 1 / 4) / A ^ 2 := by positivity
  linarith

theorem hasDerivAt_zFun (x : ℝ) {A : ℝ} (hA : 0 < A) :
    HasDerivAt (zFun x) (zDer x A) A := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt A)) A := Real.hasDerivAt_sqrt hA.ne'
  exact hs.mul (hasDerivAt_kix 0 x hA)

theorem hasDerivAt_invSqrt {A : ℝ} (hA : 0 < A) :
    HasDerivAt (fun t : ℝ => 1 / (2 * Real.sqrt t))
      (-(1 / (4 * (Real.sqrt A) ^ 3))) A := by
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt A)) A := Real.hasDerivAt_sqrt hA.ne'
  have hf : HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (2 * (1 / (2 * Real.sqrt A))) A :=
    hs.const_mul 2
  have hne : (2 : ℝ) * Real.sqrt A ≠ 0 := by positivity
  have hne0 : Real.sqrt A ≠ 0 := hsp.ne'
  have hinv := hf.inv hne
  have hfun : ((fun t : ℝ => 2 * Real.sqrt t)⁻¹) = fun t : ℝ => 1 / (2 * Real.sqrt t) := by
    funext t
    simp only [Pi.inv_apply, one_div]
  rw [hfun] at hinv
  refine hinv.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_zDer (x : ℝ) {A : ℝ} (hA : 0 < A) :
    HasDerivAt (zDer x) (zDD x A) A := by
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt A)) A := Real.hasDerivAt_sqrt hA.ne'
  have hpart1 := (hasDerivAt_invSqrt hA).mul (hasDerivAt_kix 0 x hA)
  have hpart2 := hs.mul (hasDerivAt_kix 1 x hA)
  have h := hpart1.add hpart2
  refine h.congr_deriv ?_
  unfold zDD
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  field_simp
  ring

/-! ### 2. The Liouville normal form, from the compiled ODE -/

/-- **`z″ = q·z`.**  The modified-Bessel ODE (block A2) becomes the Liouville normal form
through `C3B5.A3.liouville_normal_form` at `r = √A`. -/
theorem zDD_eq (x : ℝ) {A : ℝ} (hA : 0 < A) : zDD x A = qFun x A * zFun x A := by
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  have hs4 : Real.sqrt A ^ 4 = A ^ 2 := by
    have : Real.sqrt A ^ 4 = (Real.sqrt A ^ 2) ^ 2 := by ring
    rw [this, hsq]
  have hode := kix_bessel_ode x hA
  have hbessel : Real.sqrt A ^ 4 * kix 2 x A + Real.sqrt A ^ 2 * kix 1 x A
      - (Real.sqrt A ^ 4 - x ^ 2) * kix 0 x A = 0 := by
    rw [hs4, hsq]
    linarith [hode]
  have hL := C3B5.A3.liouville_normal_form (r := Real.sqrt A) (K := kix 0 x A)
    (K' := kix 1 x A) (K'' := kix 2 x A) (x := x) hsp hbessel
  unfold zDD qFun zFun
  rw [hs4] at hL
  exact hL

/-! ### 3. Decay of `z` and `z′` at `+∞` -/

private theorem sqrt_le_self {A : ℝ} (hA : 1 ≤ A) : Real.sqrt A ≤ A := by
  nlinarith [Real.sq_sqrt (le_trans zero_le_one hA), Real.sqrt_nonneg A,
    Real.one_le_sqrt.mpr hA]

private theorem invSqrt_le_one {A : ℝ} (hA : 1 ≤ A) : 1 / (2 * Real.sqrt A) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt A := Real.one_le_sqrt.mpr hA
  have h2 : (0 : ℝ) < 2 * Real.sqrt A := by linarith
  rw [div_le_one h2]
  linarith

/-- **The boundary behaviour.**  `z(A) + z′(A) → 0` at `+∞`. -/
theorem tendsto_zSum (x : ℝ) :
    Tendsto (fun A => zFun x A + zDer x A) atTop (nhds 0) := by
  set C : ℝ := kixConst 0 1 + kixConst 1 1 with hC
  have hC0 : 0 ≤ C := by
    have := kixConst_nonneg 0 (1 : ℝ)
    have := kixConst_nonneg 1 (1 : ℝ)
    simp only [hC]; linarith
  have hmaj : Tendsto (fun A : ℝ => Real.exp 1 * (3 * C) * (A * Real.exp (-A)))
      atTop (nhds 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h1 : Tendsto (fun A : ℝ => A * Real.exp (-A)) atTop (nhds 0) := by
      simpa using h
    have := h1.const_mul (Real.exp 1 * (3 * C))
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA0
  have hs1 : (1 : ℝ) ≤ Real.sqrt A := Real.one_le_sqrt.mpr hA
  have hb0 : |kix 0 x A| ≤ Real.exp (-(A - 1)) * kixConst 0 1 :=
    kix_abs_le 0 x one_pos hA
  have hb1 : |kix 1 x A| ≤ Real.exp (-(A - 1)) * kixConst 1 1 :=
    kix_abs_le 1 x one_pos hA
  have hE : (0 : ℝ) < Real.exp (-(A - 1)) := Real.exp_pos _
  have hEeq : Real.exp (-(A - 1)) = Real.exp 1 * Real.exp (-A) := by
    rw [← Real.exp_add]; congr 1; ring
  have hzf : |zFun x A| ≤ Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 0 1) := by
    unfold zFun
    rw [abs_mul, abs_of_nonneg hsp.le]
    exact mul_le_mul_of_nonneg_left hb0 hsp.le
  have hzd : |zDer x A|
      ≤ 1 * (Real.exp (-(A - 1)) * kixConst 0 1)
        + Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 1 1) := by
    unfold zDer
    refine (abs_add_le _ _).trans ?_
    have h1 : |1 / (2 * Real.sqrt A) * kix 0 x A|
        ≤ 1 * (Real.exp (-(A - 1)) * kixConst 0 1) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.sqrt A))]
      refine mul_le_mul (invSqrt_le_one hA) hb0 (abs_nonneg _) zero_le_one
    have h2 : |Real.sqrt A * kix 1 x A|
        ≤ Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 1 1) := by
      rw [abs_mul, abs_of_nonneg hsp.le]
      exact mul_le_mul_of_nonneg_left hb1 hsp.le
    linarith
  have hsa : Real.sqrt A ≤ A := sqrt_le_self hA
  have hk0 : 0 ≤ kixConst 0 1 := kixConst_nonneg 0 1
  have hk1 : 0 ≤ kixConst 1 1 := kixConst_nonneg 1 1
  rw [Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  have hstep : |zFun x A| + |zDer x A|
      ≤ (2 * Real.sqrt A + 1) * (Real.exp (-(A - 1)) * (kixConst 0 1 + kixConst 1 1)) := by
    have e1 : (0 : ℝ) ≤ Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 0 1) :=
      mul_nonneg hsp.le (mul_nonneg hE.le hk0)
    have e2 : (0 : ℝ) ≤ Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 1 1) :=
      mul_nonneg hsp.le (mul_nonneg hE.le hk1)
    have e3 : (0 : ℝ) ≤ Real.exp (-(A - 1)) * kixConst 1 1 := mul_nonneg hE.le hk1
    have expand : (2 * Real.sqrt A + 1) *
          (Real.exp (-(A - 1)) * (kixConst 0 1 + kixConst 1 1))
        = Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 0 1)
          + (1 * (Real.exp (-(A - 1)) * kixConst 0 1)
             + Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 1 1))
          + (Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 0 1)
             + Real.sqrt A * (Real.exp (-(A - 1)) * kixConst 1 1)
             + Real.exp (-(A - 1)) * kixConst 1 1) := by ring
    rw [expand]
    linarith
  refine hstep.trans ?_
  rw [hEeq, hC]
  have hAA : 2 * Real.sqrt A + 1 ≤ 3 * A := by nlinarith [hsa, hA]
  have hpos : (0 : ℝ) < Real.exp 1 * Real.exp (-A) := by positivity
  calc (2 * Real.sqrt A + 1) *
        (Real.exp 1 * Real.exp (-A) * (kixConst 0 1 + kixConst 1 1))
      ≤ (3 * A) * (Real.exp 1 * Real.exp (-A) * (kixConst 0 1 + kixConst 1 1)) := by
        refine mul_le_mul_of_nonneg_right hAA ?_
        have : 0 ≤ kixConst 0 1 + kixConst 1 1 := by linarith
        positivity
    _ = Real.exp 1 * (3 * (kixConst 0 1 + kixConst 1 1)) * (A * Real.exp (-A)) := by ring

/-! ### 4. The ceiling, concluded -/

/-- **THE LOGARITHMIC-DERIVATIVE CEILING FOR `K_{ix}`, CONCLUDED.**
On any ray `[a,∞)` with `a > 0` on which `K_{ix}` is positive, `−z′/z ≤ 1` for
`z = √A·K_{ix}`.  The hypothesis of `C3B5.A3.logDeriv_le_one` is discharged, not assumed:
the ODE comes from `kix_bessel_ode`, the potential bound from `qFun_le_one`, and the
boundary behaviour from `tendsto_zSum`. -/
theorem logDeriv_kix_le_one {x a : ℝ} (ha : 0 < a)
    (hKpos : ∀ A ∈ Ici a, 0 < kix 0 x A) :
    ∀ A ∈ Ici a, -zDer x A / zFun x A ≤ 1 := by
  refine C3B5.A3.logDeriv_le_one (z := zFun x) (zd := zDer x) (zdd := zDD x)
    (q := qFun x) (a := a) ?_ ?_ ?_ ?_ ?_ (tendsto_zSum x)
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht
    have hsp : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    exact mul_pos hsp (hKpos t ht)
  · intro t ht
    exact hasDerivAt_zFun x (lt_of_lt_of_le ha ht)
  · intro t ht
    exact hasDerivAt_zDer x (lt_of_lt_of_le ha ht)
  · intro t ht
    exact zDD_eq x (lt_of_lt_of_le ha ht)
  · intro t _
    exact qFun_le_one x t

/-! ### 5. The radial combination -/

/-- The `hlog` relation of `C3B5.A2`, produced rather than assumed. -/
theorem kix_logDeriv_transfer {x A : ℝ} (hA : 0 < A) (hK : kix 0 x A ≠ 0) :
    kix 1 x A = -((-zDer x A / zFun x A) + 1 / (2 * A)) * kix 0 x A := by
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hz : zFun x A ≠ 0 := by
    unfold zFun
    exact mul_ne_zero hsp.ne' hK
  refine C3B5.A3.logDeriv_transfer (A := A) (K := kix 0 x A) (K' := kix 1 x A)
    (zd := zDer x A) (z := zFun x A) hA hK hz rfl ?_
  unfold zDer
  have hsq : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  field_simp
  linear_combination (-(kix 0 x A)) * hsq

/-- **OBLIGATION A, DISCHARGED.**  For every `a ≥ 8` on whose ray `K_{ix}` is positive,
the radial combination of adjudication point 4 is strictly positive:

  `0 < (A² + 9)·K_{ix}(A) + 6A·K′_{ix}(A)`   for all `A ≥ a`.

Every hypothesis of `C3B5.A2.radial_pos_of_ge_eight` is now discharged from the integral
representation: `K′` is a genuine derivative (`hasDerivAt_kix`), the ceiling `ρ ≤ 1` is a
theorem (`logDeriv_kix_le_one`), and the logarithmic relation is produced
(`kix_logDeriv_transfer`).  **No derivative inequality appears as a hypothesis.** -/
theorem radial_kix_pos {x a : ℝ} (ha : 8 ≤ a)
    (hKpos : ∀ A ∈ Ici a, 0 < kix 0 x A) :
    ∀ A ∈ Ici a, 0 < (A ^ 2 + 9) * kix 0 x A + 6 * A * kix 1 x A := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hceil := logDeriv_kix_le_one ha0 hKpos
  intro A hA
  have hA8 : 8 ≤ A := le_trans ha hA
  have hA0 : 0 < A := by linarith
  have hK : 0 < kix 0 x A := hKpos A hA
  have hlog := kix_logDeriv_transfer hA0 hK.ne'
  have hρ : -zDer x A / zFun x A ≤ 1 := hceil A hA
  have := C3B5.A2.radial_pos_of_ge_eight (A := A) (K := kix 0 x A) (K' := kix 1 x A)
    (ρ := -zDer x A / zFun x A) hA8 hK hρ hlog
  simpa [C3B5.A2.radial] using this

end C3B6.Bessel

section AxiomAudit
#print axioms C3B6.Bessel.qFun_le_one
#print axioms C3B6.Bessel.hasDerivAt_zFun
#print axioms C3B6.Bessel.hasDerivAt_invSqrt
#print axioms C3B6.Bessel.hasDerivAt_zDer
#print axioms C3B6.Bessel.zDD_eq
#print axioms C3B6.Bessel.tendsto_zSum
#print axioms C3B6.Bessel.logDeriv_kix_le_one
#print axioms C3B6.Bessel.kix_logDeriv_transfer
#print axioms C3B6.Bessel.radial_kix_pos
end AxiomAudit
