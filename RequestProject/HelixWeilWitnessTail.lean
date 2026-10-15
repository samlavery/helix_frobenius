import RequestProject.HelixWeilWitnessProfile

/-!
# The Weil witness, brick W2a: the far-zero tail of the pair-profile zero side (ledger 1337)

For the pair profile at `ρ₀ = β + iγ` (1336), the zero side is `−|N|²·Σ_ρ m_ρ D(ρ)²`. Zeros at height distance
`≥ 2` from `γ` contribute a tail that vanishes as `λ → ∞`, uniformly from the geometry alone:

* `pairDiff_norm_le`: for `z, ρ₀` in the strip, `‖D(z)‖ ≤ 2·exp(λ(1 − (Im z − γ)²))` — the real part of
  `λ(z − ρ)²` is `λ[(Re z − Re ρ)² − (Im z − Im ρ)²]` and the abscissa difference is at most `1`.
* `farWeight_summable`: `Σ_ρ m_ρ exp(−2((Im ρ − γ)² − 1))` converges — dominated by the compiled
  `Σ m_ρ/‖ρ‖²` (`summable_xiOrderNat_div_norm_sq_nontrivialZeros`), since `(1 + 2γ²+2u²)e^{−2u²}` is bounded.
* `farTail_le`: for `λ ≥ 1`, `Σ_{|Im ρ − γ| ≥ 2} m_ρ ‖D(ρ)‖² ≤ 4·exp(−6(λ−1))·T₀`, `T₀` the weight sum.

So the far tail is `O(e^{−6λ})` while the pair term grows like `e^{8λ(β−½)²}` (1336). What remains (W2b) is the
finite set of zeros within height distance `2` of `γ`. No `sorry`, no `axiom`, no window.
-/

open Complex
open scoped Real ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixWeilWitness

open CriticalLinePhasor.ContourArgument

/-- The real part of `λ(z − ρ)²`. -/
theorem re_lam_mul_sq (lam : ℝ) (z ρ : ℂ) :
    ((lam : ℂ) * (z - ρ) ^ 2).re = lam * ((z.re - ρ.re) ^ 2 - (z.im - ρ.im) ^ 2) := by
  rw [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im]
  ring

/-- `‖exp(λ(z−ρ)²)‖ ≤ exp(λ(1 − (Im z − Im ρ)²))` when both abscissae lie in `[0, 1]`. -/
theorem norm_exp_lam_sq_le {lam : ℝ} (hlam : 0 ≤ lam) {z ρ : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1) :
    ‖Complex.exp ((lam : ℂ) * (z - ρ) ^ 2)‖ ≤ Real.exp (lam * (1 - (z.im - ρ.im) ^ 2)) := by
  rw [Complex.norm_exp, re_lam_mul_sq]
  apply Real.exp_le_exp.mpr
  have hsq : (z.re - ρ.re) ^ 2 ≤ 1 := by
    have h1 : -1 ≤ z.re - ρ.re := by linarith
    have h2 : z.re - ρ.re ≤ 1 := by linarith
    nlinarith
  nlinarith

/-- **The pair difference is bounded by twice a height-Gaussian** on the strip. -/
theorem pairDiff_norm_le {lam : ℝ} (hlam : 0 ≤ lam) {ρ₀ z : ℂ}
    (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖pairDiff lam ρ₀ z‖ ≤ 2 * Real.exp (lam * (1 - (z.im - ρ₀.im) ^ 2)) := by
  unfold pairDiff
  have hm0 : 0 ≤ (1 - conj ρ₀).re := by simp [Complex.conj_re]; linarith
  have hm1 : (1 - conj ρ₀).re ≤ 1 := by simp [Complex.conj_re]; linarith
  have hmim : (1 - conj ρ₀).im = ρ₀.im := by simp [Complex.conj_im]
  have h1 := norm_exp_lam_sq_le hlam hz0 hz1 hρ0 hρ1 (z := z) (ρ := ρ₀)
  have h2 := norm_exp_lam_sq_le hlam hz0 hz1 hm0 hm1 (z := z) (ρ := 1 - conj ρ₀)
  rw [hmim] at h2
  calc ‖Complex.exp ((lam : ℂ) * (z - ρ₀) ^ 2) - Complex.exp ((lam : ℂ) * (z - (1 - conj ρ₀)) ^ 2)‖
      ≤ ‖Complex.exp ((lam : ℂ) * (z - ρ₀) ^ 2)‖ + ‖Complex.exp ((lam : ℂ) * (z - (1 - conj ρ₀)) ^ 2)‖ :=
        norm_sub_le _ _
    _ ≤ Real.exp (lam * (1 - (z.im - ρ₀.im) ^ 2)) + Real.exp (lam * (1 - (z.im - ρ₀.im) ^ 2)) :=
        add_le_add h1 h2
    _ = 2 * Real.exp (lam * (1 - (z.im - ρ₀.im) ^ 2)) := by ring

/-! ## The far weight and its summability -/

/-- The far weight of a zero at height distance `u` from `γ`: `exp(−2(u² − 1))`. -/
def farWeight (γ : ℝ) (ρ : Zero) : ℝ := Real.exp (-2 * ((ρ.val.im - γ) ^ 2 - 1))

theorem farWeight_nonneg (γ : ℝ) (ρ : Zero) : 0 ≤ farWeight γ ρ := Real.exp_nonneg _

/-- `(1 + 2γ² + 2u²)·e^{−2u²} ≤ 2 + 2γ²`. -/
theorem weight_poly_bound (γ u : ℝ) : (1 + 2 * γ ^ 2 + 2 * u ^ 2) * Real.exp (-2 * u ^ 2) ≤ 2 + 2 * γ ^ 2 := by
  have he : Real.exp (-2 * u ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
  have he0 : 0 ≤ Real.exp (-2 * u ^ 2) := Real.exp_nonneg _
  -- `2u² e^{−2u²} ≤ 1`: with `v = 2u² ≥ 0`, `v e^{−v} ≤ 1` since `e^{v} ≥ 1 + v ≥ v`
  have hv : 2 * u ^ 2 * Real.exp (-2 * u ^ 2) ≤ 1 := by
    have hv0 : 0 ≤ 2 * u ^ 2 := by positivity
    have hexp : 2 * u ^ 2 ≤ Real.exp (2 * u ^ 2) := by
      have := Real.add_one_le_exp (2 * u ^ 2); linarith
    have hpos : 0 < Real.exp (2 * u ^ 2) := Real.exp_pos _
    rw [show -2 * u ^ 2 = -(2 * u ^ 2) by ring, Real.exp_neg]
    rw [mul_inv_le_iff₀ hpos]
    linarith
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + 2 * γ ^ 2) he0]

/-- The far weight is dominated by `(2 + 2γ²)e²/‖ρ‖²`. -/
theorem farWeight_le (γ : ℝ) (ρ : Zero) :
    farWeight γ ρ ≤ ((2 + 2 * γ ^ 2) * Real.exp 2) * (1 / ‖ρ.val‖ ^ 2) := by
  have hρ : 0 < ‖ρ.val‖ := by
    rw [norm_pos_iff]; intro h; have := ρ.2.1; rw [h] at this; simp at this
  have hn : ‖ρ.val‖ ^ 2 ≤ 1 + 2 * γ ^ 2 + 2 * (ρ.val.im - γ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : ρ.val.re ^ 2 ≤ 1 := by
      have := ρ.2.1; have := ρ.2.2.1; nlinarith
    nlinarith [sq_nonneg (ρ.val.im - 2 * γ), sq_nonneg γ, sq_nonneg (ρ.val.im - γ)]
  unfold farWeight
  rw [show -2 * ((ρ.val.im - γ) ^ 2 - 1) = -2 * (ρ.val.im - γ) ^ 2 + 2 by ring, Real.exp_add]
  have hw := weight_poly_bound γ (ρ.val.im - γ)
  have hpos2 : 0 < ‖ρ.val‖ ^ 2 := by positivity
  rw [mul_one_div, le_div_iff₀ hpos2]
  have he0 : 0 ≤ Real.exp (-2 * (ρ.val.im - γ) ^ 2) := Real.exp_nonneg _
  have he2 : 0 < Real.exp 2 := Real.exp_pos _
  calc Real.exp (-2 * (ρ.val.im - γ) ^ 2) * Real.exp 2 * ‖ρ.val‖ ^ 2
      ≤ Real.exp (-2 * (ρ.val.im - γ) ^ 2) * Real.exp 2 * (1 + 2 * γ ^ 2 + 2 * (ρ.val.im - γ) ^ 2) := by
        gcongr
    _ = ((1 + 2 * γ ^ 2 + 2 * (ρ.val.im - γ) ^ 2) * Real.exp (-2 * (ρ.val.im - γ) ^ 2)) * Real.exp 2 := by ring
    _ ≤ (2 + 2 * γ ^ 2) * Real.exp 2 := by gcongr

/-- **The weighted far weight is summable over the zeros.** -/
theorem farWeight_summable (γ : ℝ) :
    Summable (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℝ) * farWeight γ ρ) := by
  have hdom := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.mul_left ((2 + 2 * γ ^ 2) * Real.exp 2)
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (farWeight_nonneg γ ρ))
    (fun ρ => ?_) hdom
  have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  calc (ZD.xiOrderNat ρ.val : ℝ) * farWeight γ ρ
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * (((2 + 2 * γ ^ 2) * Real.exp 2) * (1 / ‖ρ.val‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (farWeight_le γ ρ) hm
    _ = ((2 + 2 * γ ^ 2) * Real.exp 2) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring

/-! ## The far tail -/

/-- The far part of the zero side's modulus: zeros at height distance `≥ 2`. -/
def farTerm (lam : ℝ) (ρ₀ : ℂ) (ρ : Zero) : ℝ :=
  if 2 ≤ |ρ.val.im - ρ₀.im| then (ZD.xiOrderNat ρ.val : ℝ) * ‖pairDiff lam ρ₀ ρ.val‖ ^ 2 else 0

/-- Pointwise: for `λ ≥ 1` and height distance `≥ 2`, `m‖D‖² ≤ 4e^{−6(λ−1)}·m·farWeight`. -/
theorem farTerm_le {lam : ℝ} (hlam : 1 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1) (ρ : Zero) :
    farTerm lam ρ₀ ρ ≤ (4 * Real.exp (-6 * (lam - 1))) * ((ZD.xiOrderNat ρ.val : ℝ) * farWeight ρ₀.im ρ) := by
  unfold farTerm
  split_ifs with hfar
  · have hz0 : 0 ≤ ρ.val.re := ρ.2.1.le
    have hz1 : ρ.val.re ≤ 1 := ρ.2.2.1.le
    have hD := pairDiff_norm_le (by linarith) hρ0 hρ1 hz0 hz1 (lam := lam) (z := ρ.val)
    set u : ℝ := ρ.val.im - ρ₀.im with hu
    have hu2 : 4 ≤ u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u, hfar]
    have hD2 : ‖pairDiff lam ρ₀ ρ.val‖ ^ 2 ≤ (2 * Real.exp (lam * (1 - u ^ 2))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hD 2
    have hexp : (2 * Real.exp (lam * (1 - u ^ 2))) ^ 2
        ≤ 4 * Real.exp (-6 * (lam - 1)) * farWeight ρ₀.im ρ := by
      unfold farWeight
      rw [← hu]
      have hl : (2 * Real.exp (lam * (1 - u ^ 2))) ^ 2 = 4 * Real.exp (2 * (lam * (1 - u ^ 2))) := by
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
        have : lam * (1 - u ^ 2) + lam * (1 - u ^ 2) = 2 * (lam * (1 - u ^ 2)) := by ring
        rw [this]; norm_num
      have hr : 4 * Real.exp (-6 * (lam - 1)) * Real.exp (-2 * (u ^ 2 - 1))
          = 4 * Real.exp (-6 * (lam - 1) + -2 * (u ^ 2 - 1)) := by
        rw [mul_assoc, ← Real.exp_add]
      rw [hl, hr]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (by linarith : (0 : ℝ) ≤ 2 * u ^ 2 - 8)]
    have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
    calc (ZD.xiOrderNat ρ.val : ℝ) * ‖pairDiff lam ρ₀ ρ.val‖ ^ 2
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (4 * Real.exp (-6 * (lam - 1)) * farWeight ρ₀.im ρ) :=
          mul_le_mul_of_nonneg_left (hD2.trans hexp) hm
      _ = (4 * Real.exp (-6 * (lam - 1))) * ((ZD.xiOrderNat ρ.val : ℝ) * farWeight ρ₀.im ρ) := by ring
  · exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (farWeight_nonneg _ _))

theorem farTerm_nonneg (lam : ℝ) (ρ₀ : ℂ) (ρ : Zero) : 0 ≤ farTerm lam ρ₀ ρ := by
  unfold farTerm
  split_ifs
  · positivity
  · exact le_refl _

/-- The far terms are summable. -/
theorem farTerm_summable {lam : ℝ} (hlam : 1 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1) :
    Summable (farTerm lam ρ₀) :=
  Summable.of_nonneg_of_le (farTerm_nonneg lam ρ₀) (farTerm_le hlam hρ0 hρ1)
    ((farWeight_summable ρ₀.im).mul_left _)

/-- **The far tail is `O(e^{−6λ})`**: `Σ_{|Im ρ − γ| ≥ 2} m_ρ ‖D(ρ)‖² ≤ 4e^{−6(λ−1)}·T₀`. -/
theorem farTail_le {lam : ℝ} (hlam : 1 ≤ lam) {ρ₀ : ℂ} (hρ0 : 0 ≤ ρ₀.re) (hρ1 : ρ₀.re ≤ 1) :
    ∑' ρ : Zero, farTerm lam ρ₀ ρ
      ≤ (4 * Real.exp (-6 * (lam - 1))) * ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * farWeight ρ₀.im ρ := by
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (farTerm_le hlam hρ0 hρ1) (farTerm_summable hlam hρ0 hρ1)
    ((farWeight_summable ρ₀.im).mul_left _)

end CriticalLinePhasor.HelixWeilWitness

end

#print axioms CriticalLinePhasor.HelixWeilWitness.pairDiff_norm_le
#print axioms CriticalLinePhasor.HelixWeilWitness.farWeight_summable
#print axioms CriticalLinePhasor.HelixWeilWitness.farTail_le
