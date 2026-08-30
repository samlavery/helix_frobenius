import c3b6_A10

/-!
# C3 batch 7, block B1 — the mode-specific `L¹` majorant (attack family 1)

Batch 6 bounded every mode by `kix_abs_le` at the **common** parameter `δ = A₁` (the head's
radial variable).  That majorant carries the rate `e^{−δ/2}` rather than `e^{−δ}`, because
`coshMaj` was built from `cosh w ≥ (1+w+w²/2)/2` — the `/2` costs a whole factor `e^{A/2}`.
Numerically (`tmp/c3b7_falsify_out.txt`) that slack is what makes the batch-6 candidate
`modeBound_tail_lt_head` **false** at `x = 0`, `A₁ = 8`: `tail/head = 1.2265`.

This file replaces it with the **mode-specific** majorant: each mode is bounded at its own
`A`, using

    `1 + w²/2 ≤ cosh w`               (`one_add_sq_half_le_cosh`)
    `cosh^j w ≤ e^{jw}`               (`C3B6.Bessel.cosh_le_exp`)
    `jw ≤ j²/A + (A/4)w²`             (`lin_le_quad`, AM–GM)
    `∫_{w>0} e^{−(A/4)w²} ≤ 1 + 4/A`  (`C3B6.Theta.exp_quarter_sq_integral_le`)

giving

    `coshMoment j A ≤ e^{−A}·e^{j²/A}·(1 + 4/A)`        (`coshMoment_sharp_le`)

— rate `e^{−A}`, the true rate of `K_{ix}(A)`.  Packaged:

    `|radial A (kix 0 x A) (kix 1 x A)| ≤ 2(A+3)²·e^{−A}`   for `A ≥ 8`
                                                        (`radial_abs_le_sharp`)

using `(A²+9) + 6A = (A+3)²` exactly and `e^{1/A} ≤ 1/(1−1/A) ≤ 1 + 2/A`.

PATCH LOG (adjudicator run 1, `env LEAN_PATH=tmp lake env lean tmp/c3b7_B1.lean`, exit 1):
* `Real.cosh_two_mul` in this Mathlib is `cosh (2z) = cosh z ^ 2 + sinh z ^ 2`, not
  `2 cosh z ^ 2 − 1`.  `hhalf` now derives `cosh w = 1 + 2 sinh(w/2)^2` from that form
  together with `Real.cosh_sq_sub_sinh_sq`.
* `exp_inv_le`: the extra `rw [div_le_iff₀ …]` after `field_simp` was invalid; the goal
  there is already `A^2 ≤ (A+2)*(A−1)`, closed by `nlinarith [hA]`.
* `radial_abs_le_sharp`/`hkey`: the `div_add'` rewrite pattern was absent.  Denominators are
  now cleared by an explicit `heq` (`field_simp; ring`) followed by `div_le_iff₀`.

SCOPE: nothing here mentions `Ξ`, zeros, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B7

open C3B6.Bessel
open C3B6.Theta

/-! ### 1. `t ≤ sinh t` and `1 + w²/2 ≤ cosh w` -/

/-- `t ≤ sinh t` for `t ≥ 0`, by monotonicity of `sinh t − t` (`cosh t ≥ 1`). -/
theorem self_le_sinh {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.sinh t := by
  have hF : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Real.sinh r - r) (Real.cosh s - 1) s := by
    intro s
    have h1 := Real.hasDerivAt_sinh s
    have h2 : HasDerivAt (fun r : ℝ => r) (1 : ℝ) s := hasDerivAt_id' (x := s)
    exact h1.sub h2
  have hmono : MonotoneOn (fun r : ℝ => Real.sinh r - r) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun s _ => ((hF s).continuousAt).continuousWithinAt
    · exact fun s _ => ((hF s).differentiableAt).differentiableWithinAt
    · intro s _
      rw [(hF s).deriv]
      have := Real.one_le_cosh s
      linarith
  have hstep := hmono (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  simp only [Real.sinh_zero, sub_zero, sub_self] at hstep
  linarith

/-- `cosh w = 1 + 2 sinh(w/2)²`, from `cosh (2z) = cosh z ² + sinh z ²` and
`cosh z ² − sinh z ² = 1`. -/
theorem cosh_eq_one_add_two_sinh_half_sq (w : ℝ) :
    Real.cosh w = 1 + 2 * Real.sinh (w / 2) ^ 2 := by
  have h2 : Real.cosh (2 * (w / 2))
      = Real.cosh (w / 2) ^ 2 + Real.sinh (w / 2) ^ 2 := Real.cosh_two_mul (w / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (w / 2)
  rw [show 2 * (w / 2) = w by ring] at h2
  linarith

/-- **`1 + w²/2 ≤ cosh w`** for every real `w`. -/
theorem one_add_sq_half_le_cosh (w : ℝ) : 1 + w ^ 2 / 2 ≤ Real.cosh w := by
  have hhalf := cosh_eq_one_add_two_sinh_half_sq w
  have hsq : w ^ 2 / 4 ≤ Real.sinh (w / 2) ^ 2 := by
    rcases le_total 0 w with hw | hw
    · have hnn : (0 : ℝ) ≤ w / 2 := by linarith
      have h := self_le_sinh (t := w / 2) hnn
      have hprod := mul_self_le_mul_self hnn h
      nlinarith [hprod]
    · have hnn : (0 : ℝ) ≤ -w / 2 := by linarith
      have h := self_le_sinh (t := -w / 2) hnn
      have hprod := mul_self_le_mul_self hnn h
      have hs : Real.sinh (w / 2) ^ 2 = Real.sinh (-w / 2) ^ 2 := by
        rw [show -w / 2 = -(w / 2) by ring, Real.sinh_neg]
        ring
      rw [hs]
      nlinarith [hprod]
  linarith [hsq, hhalf]

/-! ### 2. The AM–GM step -/

/-- `j·w ≤ j²/A + (A/4)·w²` for `A > 0` — the square `(2j − Aw)² ≥ 0`. -/
theorem lin_le_quad {A j w : ℝ} (hA : 0 < A) : j * w ≤ j ^ 2 / A + A / 4 * w ^ 2 := by
  have hne : A ≠ 0 := hA.ne'
  have heq : j ^ 2 / A + A / 4 * w ^ 2 - j * w
      = (2 * j - A * w) ^ 2 / (4 * A) := by
    field_simp
    ring
  nlinarith [heq, sq_nonneg (2 * j - A * w), hA,
    div_nonneg (sq_nonneg (2 * j - A * w)) (by linarith : (0:ℝ) ≤ 4 * A)]

/-! ### 3. The sharp `cosh`-moment bound -/

/-- **THE SHARP MAJORANT.**  `∫_{w>0} cosh^j w·e^{−A cosh w} dw ≤ e^{−A}·e^{j²/A}·(1+4/A)`.
The rate is `e^{−A}`, matching the true decay of `K_{ix}(A)`; the batch-6 majorant only
gave `e^{−A/2}`. -/
theorem coshMoment_sharp_le (j : ℕ) {A : ℝ} (hA : 0 < A) :
    coshMoment j A ≤ Real.exp (-A) * Real.exp ((j : ℝ) ^ 2 / A) * (1 + 4 / A) := by
  have hgint : IntegrableOn (fun w : ℝ =>
      Real.exp (-A) * Real.exp ((j : ℝ) ^ 2 / A) * Real.exp (-(A / 4) * w ^ 2))
      (Ioi (0 : ℝ)) := by
    have hq : (0 : ℝ) < A / 4 := by linarith
    exact ((integrable_exp_neg_mul_sq hq).integrableOn).const_mul _
  have hpt : ∀ w ∈ Ioi (0 : ℝ),
      Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))
        ≤ Real.exp (-A) * Real.exp ((j : ℝ) ^ 2 / A) * Real.exp (-(A / 4) * w ^ 2) := by
    intro w hw
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    have hcosh := one_add_sq_half_le_cosh w
    have hpow : Real.cosh w ^ j ≤ Real.exp ((j : ℝ) * w) := by
      have hc0 : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos (one_le_cosh w)
      calc Real.cosh w ^ j ≤ Real.exp w ^ j := pow_le_pow_left₀ hc0.le (cosh_le_exp hw0) j
        _ = Real.exp ((j : ℝ) * w) := by rw [← Real.exp_nat_mul]
    have hexp : Real.exp (-(A * Real.cosh w)) ≤ Real.exp (-A - A / 2 * w ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hcosh, hA]
    have hamgm := lin_le_quad (A := A) (j := (j : ℝ)) (w := w) hA
    calc Real.cosh w ^ j * Real.exp (-(A * Real.cosh w))
        ≤ Real.exp ((j : ℝ) * w) * Real.exp (-A - A / 2 * w ^ 2) :=
          mul_le_mul hpow hexp (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp ((j : ℝ) * w + (-A - A / 2 * w ^ 2)) := by rw [← Real.exp_add]
      _ ≤ Real.exp ((j : ℝ) ^ 2 / A + A / 4 * w ^ 2 + (-A - A / 2 * w ^ 2)) := by
          refine Real.exp_le_exp.mpr ?_
          linarith
      _ = Real.exp (-A) * Real.exp ((j : ℝ) ^ 2 / A) * Real.exp (-(A / 4) * w ^ 2) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  calc coshMoment j A
      ≤ ∫ w in Ioi (0 : ℝ),
          Real.exp (-A) * Real.exp ((j : ℝ) ^ 2 / A) * Real.exp (-(A / 4) * w ^ 2) :=
        setIntegral_mono_on (coshMomentFun_integrableOn j hA) hgint measurableSet_Ioi hpt
    _ = Real.exp (-A) * Real.exp ((j : ℝ) ^ 2 / A)
          * ∫ w in Ioi (0 : ℝ), Real.exp (-(A / 4) * w ^ 2) := by
        rw [integral_const_mul]
    _ ≤ Real.exp (-A) * Real.exp ((j : ℝ) ^ 2 / A) * (1 + 4 / A) := by
        refine mul_le_mul_of_nonneg_left (exp_quarter_sq_integral_le hA) ?_
        positivity

/-! ### 4. `|kix j x A| ≤ coshMoment j A` -/

theorem kix_abs_le_coshMoment (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    |kix j x A| ≤ coshMoment j A := by
  have hb := coshMomentFun_integrableOn j hA
  calc |kix j x A| = ‖∫ w in Ioi (0 : ℝ), kixTerm j x A w‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∫ w in Ioi (0 : ℝ), Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by
        refine norm_integral_le_of_norm_le hb ?_
        filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with w _
        rw [Real.norm_eq_abs]
        exact kixTerm_abs_le_cosh j x A w
    _ = coshMoment j A := rfl

/-! ### 5. The packaged radial bound -/

/-- `e^{1/A} ≤ 1 + 2/A` for `A ≥ 2`, from `1 − t ≤ e^{−t}` only. -/
theorem exp_inv_le {A : ℝ} (hA : 2 ≤ A) : Real.exp (1 / A) ≤ 1 + 2 / A := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hne : A ≠ 0 := hA0.ne'
  have h1 : (1 : ℝ) - 1 / A ≤ Real.exp (-(1 / A)) := by
    have := Real.add_one_le_exp (-(1 / A))
    linarith
  have hpos : (0 : ℝ) < 1 - 1 / A := by
    rw [sub_pos, div_lt_one hA0]
    linarith
  have hstep : Real.exp (1 / A) ≤ 1 / (1 - 1 / A) := by
    rw [le_div_iff₀ hpos]
    have hmul : Real.exp (1 / A) * Real.exp (-(1 / A)) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [h1, Real.exp_pos (1 / A)]
  refine hstep.trans ?_
  rw [div_le_iff₀ hpos]
  field_simp
  nlinarith [hA]

/-- **THE SHARP RADIAL BOUND.**  `|(A²+9)K_{ix}(A) + 6A K′_{ix}(A)| ≤ 2(A+3)²e^{−A}` for
`A ≥ 8`.  The exact identity `(A²+9) + 6A = (A+3)²` is what makes the constant clean. -/
theorem radial_abs_le_sharp (x : ℝ) {A : ℝ} (hA : 8 ≤ A) :
    |C3B5.A2.radial A (kix 0 x A) (kix 1 x A)| ≤ 2 * (A + 3) ^ 2 * Real.exp (-A) := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hE : (0 : ℝ) < Real.exp (-A) := Real.exp_pos _
  have hinv : Real.exp (1 / A) ≤ 1 + 2 / A := exp_inv_le (by linarith)
  have h0' : |kix 0 x A| ≤ Real.exp (-A) * (1 + 4 / A) := by
    have h := (kix_abs_le_coshMoment 0 x hA0).trans (coshMoment_sharp_le 0 hA0)
    simpa using h
  have h1' : |kix 1 x A| ≤ Real.exp (-A) * Real.exp (1 / A) * (1 + 4 / A) := by
    have h := (kix_abs_le_coshMoment 1 x hA0).trans (coshMoment_sharp_le 1 hA0)
    simpa using h
  have h1'' : |kix 1 x A| ≤ Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A)) := by
    refine h1'.trans ?_
    have hpos4 : (0 : ℝ) ≤ 1 + 4 / A := by positivity
    calc Real.exp (-A) * Real.exp (1 / A) * (1 + 4 / A)
        = Real.exp (-A) * (Real.exp (1 / A) * (1 + 4 / A)) := by ring
      _ ≤ Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A)) := by
          refine mul_le_mul_of_nonneg_left ?_ hE.le
          exact mul_le_mul_of_nonneg_right hinv hpos4
  have hstep : |C3B5.A2.radial A (kix 0 x A) (kix 1 x A)|
      ≤ (A ^ 2 + 9) * |kix 0 x A| + 6 * A * |kix 1 x A| := by
    unfold C3B5.A2.radial
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ A ^ 2 + 9),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 6 * A)]
  have hkey : (A ^ 2 + 9) * (1 + 4 / A) + 6 * A * ((1 + 2 / A) * (1 + 4 / A))
      ≤ 2 * (A + 3) ^ 2 := by
    have hne : A ≠ 0 := hA0.ne'
    have heq : (A ^ 2 + 9) * (1 + 4 / A) + 6 * A * ((1 + 2 / A) * (1 + 4 / A))
        = (A ^ 3 + 10 * A ^ 2 + 45 * A + 84) / A := by
      field_simp
      ring
    rw [heq, div_le_iff₀ hA0]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ A - 8) (sq_nonneg A),
      mul_nonneg (by linarith : (0:ℝ) ≤ A - 8) (by linarith : (0:ℝ) ≤ A), hA]
  have e0 : (A ^ 2 + 9) * |kix 0 x A| ≤ (A ^ 2 + 9) * (Real.exp (-A) * (1 + 4 / A)) :=
    mul_le_mul_of_nonneg_left h0' (by positivity)
  have e1 : 6 * A * |kix 1 x A|
      ≤ 6 * A * (Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A))) :=
    mul_le_mul_of_nonneg_left h1'' (by positivity)
  refine hstep.trans ?_
  calc (A ^ 2 + 9) * |kix 0 x A| + 6 * A * |kix 1 x A|
      ≤ (A ^ 2 + 9) * (Real.exp (-A) * (1 + 4 / A))
        + 6 * A * (Real.exp (-A) * ((1 + 2 / A) * (1 + 4 / A))) := by linarith
    _ = ((A ^ 2 + 9) * (1 + 4 / A) + 6 * A * ((1 + 2 / A) * (1 + 4 / A))) * Real.exp (-A) := by
        ring
    _ ≤ 2 * (A + 3) ^ 2 * Real.exp (-A) := mul_le_mul_of_nonneg_right hkey hE.le

end C3B7

section AxiomAudit
#print axioms C3B7.self_le_sinh
#print axioms C3B7.cosh_eq_one_add_two_sinh_half_sq
#print axioms C3B7.one_add_sq_half_le_cosh
#print axioms C3B7.lin_le_quad
#print axioms C3B7.coshMoment_sharp_le
#print axioms C3B7.kix_abs_le_coshMoment
#print axioms C3B7.exp_inv_le
#print axioms C3B7.radial_abs_le_sharp
end AxiomAudit
