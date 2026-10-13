import RequestProject.DilationEigenfunctional

/-!
# The same-height transverse partner (ledger 1225)

`ρ* := 1 − conj ρ` has the SAME height as `ρ` and the mirrored transverse coordinate. This is the pairing
that any symmetric realization of the native generator forces (`SymPair.inner_eq_zero_unless_reflect`),
and that the area measure's duality implements (`AreaReflection.mellin_areaDual`). It is NOT the
functional-equation reflection `ρ ↦ 1 − ρ`, which also flips the height.

* `partner_im`, `partner_re`, `partner_partner`, `partner_eq_self_iff`: same height, `σ ↦ 1 − σ`, an
  involution, fixed exactly on `Re ρ = ½`.
* `fe_reflection_eq_conj_partner`: `1 − ρ = conj(ρ*)`. The FE reflection is J (conjugation, the two feet)
  composed with the same-height partner. J alone keeps the transverse coordinate.
* `bank_partner_inversion`: per site, the partner bank is inversion in the circle whose radius is the
  drift-free amplitude: `n^{−ρ*} = n^{−1} / conj(n^{−ρ})`, and `|n^{−ρ}|·|n^{−ρ*}| = n^{−1}`.
* `covariant_functional_re_of_growth`: a nonzero continuous covariant functional on a space whose
  dilations grow at most like `C·e^{δ|t|}` has `|Re s − ½| ≤ δ`. A zero at transverse displacement `δ` is
  representable only in a completion whose dilation growth exponent is at least `|δ|`. The D-flow
  parameter is exactly this growth exponent.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SameHeight

/-- The same-height transverse partner. -/
def partner (ρ : ℂ) : ℂ := 1 - (starRingEnd ℂ) ρ

@[simp] theorem partner_im (ρ : ℂ) : (partner ρ).im = ρ.im := by simp [partner]

@[simp] theorem partner_re (ρ : ℂ) : (partner ρ).re = 1 - ρ.re := by simp [partner]

theorem partner_partner (ρ : ℂ) : partner (partner ρ) = ρ := by
  simp [partner, map_sub, map_one]

theorem partner_eq_self_iff (ρ : ℂ) : partner ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    apply Complex.ext <;> simp [h]
    norm_num

/-- **The FE reflection is J composed with the same-height partner.** -/
theorem fe_reflection_eq_conj_partner (ρ : ℂ) : 1 - ρ = (starRingEnd ℂ) (partner ρ) := by
  simp [partner, map_sub, map_one]

/-- **Per site, the partner bank is inversion in the drift-free circle.** -/
theorem bank_partner_inversion {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) :
    (n : ℂ) ^ (-(partner ρ)) = (n : ℂ) ^ (-1 : ℂ) / (starRingEnd ℂ) ((n : ℂ) ^ (-ρ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_pos.ne
  have hconj : (starRingEnd ℂ) ((n : ℂ) ^ (-ρ)) = (n : ℂ) ^ (-(starRingEnd ℂ) ρ) := by
    rw [show -(starRingEnd ℂ) ρ = (starRingEnd ℂ) (-ρ) by simp, Complex.cpow_conj _ _ harg]
    simp
  rw [hconj, div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hn0]
  congr 1
  simp [partner]
  ring

theorem bank_partner_norm {n : ℕ} (hn : 1 ≤ n) (ρ : ℂ) :
    ‖(n : ℂ) ^ (-ρ)‖ * ‖(n : ℂ) ^ (-(partner ρ))‖ = (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
    ← Real.rpow_add hn0]
  simp only [Complex.neg_re, partner_re]
  rw [show -ρ.re + -(1 - ρ.re) = -1 by ring, Real.rpow_neg_one]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- **The transverse displacement of a representable zero is bounded by the dilation growth.** -/
theorem covariant_functional_re_of_growth (V : ℝ → X →L[ℂ] X) (C δ : ℝ) (_hδ : 0 ≤ δ)
    (hV : ∀ t x, ‖V t x‖ ≤ C * Real.exp (δ * |t|) * ‖x‖)
    (φ : X →L[ℂ] ℂ) (hφ : φ ≠ 0) (s : ℂ)
    (hcov : ∀ t x, φ (V t x) = Complex.exp ((t : ℂ) * (1 / 2 - s)) * φ x) :
    |s.re - 1 / 2| ≤ δ := by
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    exact hφ (ContinuousLinearMap.ext fun y => by simpa using (not_exists.mp h y))
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hx
  have hbound : ∀ t : ℝ, Real.exp (t * (1 / 2 - s.re)) * ‖φ x‖ ≤
      ‖φ‖ * (C * Real.exp (δ * |t|) * ‖x‖) := by
    intro t
    have h1 : ‖φ (V t x)‖ ≤ ‖φ‖ * ‖V t x‖ := φ.le_opNorm _
    rw [hcov, norm_mul, Complex.norm_exp] at h1
    have hre : ((t : ℂ) * (1 / 2 - s)).re = t * (1 / 2 - s.re) := by simp
    rw [hre] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hV t x) (norm_nonneg _))
  by_contra hgt'
  have hgt : δ < |s.re - 1 / 2| := not_le.mp hgt'
  set c := |s.re - 1 / 2| - δ with hc
  have hcpos : 0 < c := by linarith
  -- along the right direction, e^{u|σ−½|}·‖φx‖ ≤ K e^{δu} for all u ≥ 0
  have hdir : ∀ u : ℝ, 0 ≤ u →
      Real.exp (u * |s.re - 1 / 2|) * ‖φ x‖ ≤ ‖φ‖ * (C * Real.exp (δ * u) * ‖x‖) := by
    intro u hu
    rcases le_or_gt (s.re - 1 / 2) 0 with h | h
    · have := hbound u
      rwa [abs_of_nonneg hu, show u * (1 / 2 - s.re) = u * |s.re - 1 / 2| by
        rw [abs_of_nonpos h]; ring] at this
    · have := hbound (-u)
      rwa [abs_neg, abs_of_nonneg hu, show -u * (1 / 2 - s.re) = u * |s.re - 1 / 2| by
        rw [abs_of_pos h]; ring] at this
  -- divide by e^{δu}: e^{cu}‖φx‖ ≤ ‖φ‖ C ‖x‖, impossible as u → ∞
  have hlim : Tendsto (fun u : ℝ => Real.exp (c * u) * ‖φ x‖) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hcpos)).atTop_mul_const hpos
  obtain ⟨u, hu1, hu0⟩ :=
    ((hlim.eventually (eventually_gt_atTop (‖φ‖ * C * ‖x‖))).and (eventually_ge_atTop 0)).exists
  have h2 := hdir u hu0
  have hsplit : Real.exp (u * |s.re - 1 / 2|) = Real.exp (c * u) * Real.exp (δ * u) := by
    rw [← Real.exp_add]
    congr 1
    rw [hc]
    ring
  rw [hsplit] at h2
  have hE : 0 < Real.exp (δ * u) := Real.exp_pos _
  have : Real.exp (c * u) * ‖φ x‖ ≤ ‖φ‖ * C * ‖x‖ := by
    have h3 : Real.exp (δ * u) * (Real.exp (c * u) * ‖φ x‖) ≤ Real.exp (δ * u) * (‖φ‖ * C * ‖x‖) := by
      nlinarith [h2]
    exact le_of_mul_le_mul_left h3 hE
  linarith

end CriticalLinePhasor.SameHeight

end

#print axioms CriticalLinePhasor.SameHeight.partner_eq_self_iff
#print axioms CriticalLinePhasor.SameHeight.fe_reflection_eq_conj_partner
#print axioms CriticalLinePhasor.SameHeight.bank_partner_inversion
#print axioms CriticalLinePhasor.SameHeight.bank_partner_norm
#print axioms CriticalLinePhasor.SameHeight.covariant_functional_re_of_growth
