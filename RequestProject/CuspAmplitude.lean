import RequestProject.Lambda0Split

/-!
# Polynomial control of the cusp amplitude on the fundamental domain

Continuation, part three.  The amplitude `Kz` and rate `cz` of the compiled tail bound are
polynomially controlled: the rate is globally at most `1/2` and at least `3/(8·im z)` on `𝒟`
(`cz_le_half`, `cz_ge_on_fd`), and the bank value at height one is at most
`1 + 4·(π·cz)^{-2}·Z` for the absolute lattice constant `Z` (`theta_one_le`) — proven with no
Gaussian-sum machinery via `e^{-x} ≤ 4/x²` and the Eisenstein-type summability.  Hence
`Kz z ≤ e^{π/2}·(1 + 4(π·cz z)^{-2}·Z)` (`Kz_le`): combined with `truncMellin_norm_le` and
`lambda0_split`, this bounds `‖Λ₀_z(s)‖` by an explicit polynomial in `im z` on `𝒟`, locally
uniformly in `s` — the dominant for differentiating the master equation under the integral.
No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane Set
open scoped Real Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta

/-- Exponential decay beats the inverse square, crudely. -/
lemma exp_neg_le_four_div_sq {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 4 / x ^ 2 := by
  have h1 : 1 + x / 2 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2)
    linarith
  have h2 : (1 + x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : x ^ 2 / 4 ≤ Real.exp x := by
    rw [← h3]
    nlinarith [h2, hx.le]
  rw [Real.exp_neg]
  rw [show (4 : ℝ) / x ^ 2 = (x ^ 2 / 4)⁻¹ by field_simp]
  exact inv_anti₀ (by positivity) h4

/-- The absolute lattice constant: the inverse-fourth-power sum over the nonzero lattice. -/
noncomputable def latticeZ : ℝ :=
  ∑' p : NZ, (((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2) ^ 2)⁻¹

/-- The inverse-fourth-power lattice sum converges. -/
lemma summable_latticeZ :
    Summable fun p : NZ => (((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2) ^ 2)⁻¹ := by
  have h1 : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(4 : ℝ)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by norm_num)
  have h2 : Summable fun p : ℤ × ℤ => ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-(4 : ℝ)) :=
    ((finTwoArrowEquiv ℤ).symm.summable_iff
      (f := fun x : Fin 2 → ℤ => ‖x‖ ^ (-(4 : ℝ)))).mpr h1
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (h2.subtype _)
  obtain ⟨⟨m, n⟩, hp⟩ := p
  set x : Fin 2 → ℤ := (finTwoArrowEquiv ℤ).symm (m, n) with hx
  have hxnz : x ≠ 0 := by
    intro h
    apply hp
    have h4 := congrArg (finTwoArrowEquiv ℤ) h
    rw [hx, Equiv.apply_symm_apply] at h4
    exact h4
  have hxpos : (0 : ℝ) < ‖x‖ := by
    rw [norm_pos_iff]
    exact hxnz
  have hx0 : x 0 = m := by
    rw [hx, finTwoArrowEquiv_symm_apply]
    rfl
  have hx1 : x 1 = n := by
    rw [hx, finTwoArrowEquiv_symm_apply]
    rfl
  have hbound : ‖x‖ ^ 2 ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    have hnormle : ‖x‖ ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      fin_cases i
      · rw [show x ⟨0, by norm_num⟩ = x 0 from rfl, hx0, Int.norm_eq_abs]
        push_cast
        apply Real.abs_le_sqrt
        nlinarith [sq_nonneg (n : ℝ)]
      · rw [show x ⟨1, by norm_num⟩ = x 1 from rfl, hx1, Int.norm_eq_abs]
        push_cast
        apply Real.abs_le_sqrt
        nlinarith [sq_nonneg (m : ℝ)]
    calc ‖x‖ ^ 2 ≤ Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnormle 2
      _ = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  calc (((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ^ 2)⁻¹ ≤ ((‖x‖ ^ 2) ^ 2)⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hbound 2
    _ = ‖x‖ ^ (-(4 : ℝ)) := by
        rw [← pow_mul, Real.rpow_neg (norm_nonneg _),
          show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma latticeZ_nonneg : 0 ≤ latticeZ :=
  tsum_nonneg fun p => by positivity

/-- Nonzero pairs have positive square-norm. -/
lemma pair_sq_pos {p : ℤ × ℤ} (hp : p ≠ 0) :
    (0 : ℝ) < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  have h : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (Prod.ext h.1 h.2)
  rcases h with h | h
  · have h1 : ((p.1 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr h
    nlinarith [pow_two_pos_of_ne_zero h1, sq_nonneg ((p.2 : ℝ))]
  · have h1 : ((p.2 : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr h
    nlinarith [pow_two_pos_of_ne_zero h1, sq_nonneg ((p.1 : ℝ))]

/-- **The bank at height one is polynomially controlled by the rate.** -/
lemma theta_one_le (z : ℍ) :
    latticeTheta z 1 ≤ 1 + 4 / (π * cz z) ^ 2 * latticeZ := by
  have hc := cz_pos z
  have hsplit := (hasSum_nz_theta z one_pos).tsum_eq
  have hterm : ∀ p : NZ, Real.exp (-(π * 1) * gram z p.1) ≤
      4 / (π * cz z) ^ 2 * (((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2) ^ 2)⁻¹ := by
    intro p
    have hg := gram_pos z p.2
    have hmn := pair_sq_pos p.2
    have hcg : cz z * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2) ≤ gram z p.1 := by
      have hge := gram_ge z p.1
      rw [cz]
      calc z.im / (z.re ^ 2 + z.im ^ 2 + 1) * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)
          = ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2) * z.im /
              (z.re ^ 2 + z.im ^ 2 + 1) := by ring
        _ ≤ gram z p.1 := hge
    calc Real.exp (-(π * 1) * gram z p.1)
        = Real.exp (-(π * gram z p.1)) := by
          congr 1
          ring
      _ ≤ 4 / (π * gram z p.1) ^ 2 := exp_neg_le_four_div_sq (by positivity)
      _ ≤ 4 / (π * (cz z * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2))) ^ 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left hcg Real.pi_pos.le
      _ = 4 / (π * cz z) ^ 2 * (((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2) ^ 2)⁻¹ := by
          field_simp
  have h1 : latticeTheta z 1 - 1 ≤ 4 / (π * cz z) ^ 2 * latticeZ := by
    calc latticeTheta z 1 - 1
        = ∑' p : NZ, Real.exp (-(π * 1) * gram z p.1) := hsplit.symm
      _ ≤ ∑' p : NZ, 4 / (π * cz z) ^ 2 *
            (((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2) ^ 2)⁻¹ :=
          Summable.tsum_le_tsum hterm (hasSum_nz_theta z one_pos).summable
            (summable_latticeZ.mul_left _)
      _ = 4 / (π * cz z) ^ 2 * latticeZ := by
          rw [tsum_mul_left, latticeZ]
  linarith

/-- The rate is globally at most one half. -/
lemma cz_le_half (z : ℍ) : cz z ≤ 1 / 2 := by
  have hy := z.im_pos
  rw [cz, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (z.im - 1), sq_nonneg z.re]

/-- **The amplitude bound**: polynomial in the reciprocal rate. -/
lemma Kz_le (z : ℍ) :
    Kz z ≤ Real.exp (π / 2) * (1 + 4 / (π * cz z) ^ 2 * latticeZ) := by
  rw [Kz]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have := cz_le_half z
    nlinarith [Real.pi_pos]
  · exact theta_one_le z
  · exact le_trans zero_le_one (one_le_latticeTheta z one_pos)
  · positivity

/-- **The rate is bounded below on the fundamental domain.** -/
lemma cz_ge_on_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    3 / (8 * z.im) ≤ cz z := by
  have hy := z.im_pos
  have hy32 := CriticalLinePhasor.HeckeSupBound.fd_im_ge hz
  have hy34 : (3 : ℝ) / 4 ≤ z.im ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hx : z.re ^ 2 ≤ 1 / 4 := by
    have h2 := hz.2
    nlinarith [sq_abs z.re, pow_le_pow_left₀ (abs_nonneg z.re) h2 2]
  rw [cz, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.theta_one_le
#print axioms CriticalLinePhasor.Unfolding.Kz_le
#print axioms CriticalLinePhasor.Unfolding.cz_ge_on_fd
