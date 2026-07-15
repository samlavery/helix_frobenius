import RequestProject.CuspAmplitude

/-!
# The dominant: the Petersson density beats the completion polynomially

Continuation, part four.  Assembling the compiled bounds on the fundamental domain: the
entire completion obeys a polynomial height bound uniformly on vertical strips
(`lambda0_bound_on_fd`), and the Petersson density decays exponentially on `𝒟`
(`P_exp_decay_on_fd` — the cusp decay of the form, with the polynomial from the weight
absorbed via `x^n ≤ n!·e^x`).  Their product is the integrable dominant for differentiating
the master equation under the `𝒟`-integral.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane Set
open scoped Real Topology MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- Powers are beaten by the exponential, with factorial constant. -/
lemma pow_le_factorial_mul_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n ≤ n.factorial * Real.exp x := by
  have h1 : x ^ n / n.factorial ≤ Real.exp x := by
    calc x ^ n / n.factorial
        ≤ ∑ i ∈ Finset.range (n + 1), x ^ i / i.factorial := by
          refine Finset.single_le_sum (f := fun i => x ^ i / (i.factorial : ℝ))
            (fun i _ => by positivity) ?_
          exact Finset.self_mem_range_succ n
      _ ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx _
  have hfac : (0 : ℝ) < n.factorial := by
    exact_mod_cast n.factorial_pos
  calc x ^ n = n.factorial * (x ^ n / n.factorial) := by field_simp
    _ ≤ n.factorial * Real.exp x := by
        exact mul_le_mul_of_nonneg_left h1 hfac.le

/-- **The Petersson density decays exponentially on the fundamental domain.** -/
lemma P_exp_decay_on_fd (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ModularGroup.fd,
      P k f z ≤ C * Real.exp (-(2 * π) * z.im) := by
  -- the eventual decay of the form
  have hdecay := CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos
    one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hdecay
  obtain ⟨C₀, hC₀⟩ := hdecay
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem] at hC₀
  obtain ⟨A, hA⟩ := hC₀
  obtain ⟨M, hM0, hM⟩ := P_bounded f
  set D : ℝ := (k.toNat.factorial : ℝ) * C₀ ^ 2 with hD
  refine ⟨max (M * Real.exp (2 * π * max A 1)) D, le_max_of_le_right (by
    rw [hD]; positivity), fun z hz => ?_⟩
  have hy := z.im_pos
  by_cases hcase : max A 1 ≤ z.im
  · -- high in the cusp: the decay bound with the weight absorbed
    have hAz : A ≤ z.im := le_trans (le_max_left _ _) hcase
    have h1z : (1 : ℝ) ≤ z.im := le_trans (le_max_right _ _) hcase
    have hf := hA z hAz
    rw [Set.mem_setOf_eq, Real.norm_of_nonneg (Real.exp_pos _).le] at hf
    have hfsq : ‖f z‖ ^ 2 ≤ C₀ ^ 2 * Real.exp (-2 * π * z.im / 1) ^ 2 := by
      have h0 : (0 : ℝ) ≤ C₀ * Real.exp (-2 * π * z.im / 1) := by
        calc (0:ℝ) ≤ ‖f z‖ := norm_nonneg _
          _ ≤ _ := hf
      calc ‖f z‖ ^ 2 ≤ (C₀ * Real.exp (-2 * π * z.im / 1)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hf 2
        _ = C₀ ^ 2 * Real.exp (-2 * π * z.im / 1) ^ 2 := by ring
    have hexp2 : Real.exp (-2 * π * z.im / 1) ^ 2 = Real.exp (-(4 * π) * z.im) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hyk : z.im ^ k ≤ (k.toNat.factorial : ℝ) * Real.exp (2 * π * z.im) := by
      have hzk : z.im ^ k = z.im ^ k.toNat := by
        conv_lhs => rw [← Int.toNat_of_nonneg hk]
        rw [zpow_natCast]
      rw [hzk]
      calc z.im ^ k.toNat ≤ (k.toNat.factorial : ℝ) * Real.exp z.im :=
            pow_le_factorial_mul_exp hy.le k.toNat
        _ ≤ (k.toNat.factorial : ℝ) * Real.exp (2 * π * z.im) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply Real.exp_le_exp.mpr
            nlinarith [Real.pi_gt_three]
    calc P k f z = z.im ^ k * Complex.normSq (f z) := by rw [P]
      _ = z.im ^ k * ‖f z‖ ^ 2 := by rw [Complex.normSq_eq_norm_sq]
      _ ≤ ((k.toNat.factorial : ℝ) * Real.exp (2 * π * z.im)) *
            (C₀ ^ 2 * Real.exp (-(4 * π) * z.im)) := by
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · exact hyk
          · rw [← hexp2]
            exact hfsq
      _ = D * Real.exp (-(2 * π) * z.im) := by
          have hexp3 : Real.exp (2 * π * z.im) * Real.exp (-(4 * π) * z.im) =
              Real.exp (-(2 * π) * z.im) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hD, show (k.toNat.factorial : ℝ) * Real.exp (2 * π * z.im) *
              (C₀ ^ 2 * Real.exp (-(4 * π) * z.im)) =
              (k.toNat.factorial * C₀ ^ 2) *
                (Real.exp (2 * π * z.im) * Real.exp (-(4 * π) * z.im)) by ring, hexp3]
      _ ≤ max (M * Real.exp (2 * π * max A 1)) D * Real.exp (-(2 * π) * z.im) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · -- low: the global bound, exponentially padded
    push Not at hcase
    have h2 : (1 : ℝ) ≤ Real.exp (2 * π * max A 1) * Real.exp (-(2 * π) * z.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have heq : 2 * π * max A 1 + -(2 * π) * z.im = 2 * π * (max A 1 - z.im) := by ring
      rw [heq]
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hcase.le)
    calc P k f z ≤ M := hM z
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * (Real.exp (2 * π * max A 1) * Real.exp (-(2 * π) * z.im)) :=
          mul_le_mul_of_nonneg_left h2 hM0
      _ = M * Real.exp (2 * π * max A 1) * Real.exp (-(2 * π) * z.im) := by ring
      _ ≤ max (M * Real.exp (2 * π * max A 1)) D * Real.exp (-(2 * π) * z.im) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- The explicit strip constant for the completion bound. -/
noncomputable def lambdaC (N : ℝ) : ℝ :=
  2 * Real.exp (π / 2) * (1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ) *
    ((8 / (3 * π)) ^ N * Real.Gamma N)

lemma lambdaC_nonneg {N : ℝ} (hN : 0 < N) : 0 ≤ lambdaC N := by
  rw [lambdaC]
  have h1 := latticeZ_nonneg
  have h2 := (Real.Gamma_pos_of_pos hN).le
  have h3 : (0 : ℝ) ≤ (8 / (3 * π)) ^ N := Real.rpow_nonneg (by positivity) N
  have h4 : (0 : ℝ) ≤ 1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ :=
    add_nonneg zero_le_one (mul_nonneg (by positivity) h1)
  exact mul_nonneg (mul_nonneg (by positivity) h4) (mul_nonneg h3 h2)

/-- **The polynomial bound for the entire completion on the fundamental domain**, uniform on
vertical strips: for `Re s ≤ N` and `Re (1-s) ≤ N`,
`‖Λ₀_z(s)‖ ≤ lambdaC N · (1 + im z²) · im z ^ N`. -/
theorem lambda0_bound_on_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) {s : ℂ} {N : ℝ}
    (hN : 0 < N) (hs1 : s.re ≤ N) (hs2 : (1 - s).re ≤ N) :
    ‖(generalFEPair z).Λ₀ s‖ ≤ lambdaC N * ((1 + z.im ^ 2) * z.im ^ N) := by
  have hy := z.im_pos
  have hc := cz_pos z
  have hcfd := cz_ge_on_fd hz
  -- the reciprocal-rate bound on the domain
  have hrate : 1 / (π * cz z) ≤ 8 / (3 * π) * z.im := by
    rw [div_le_iff₀ (by positivity)]
    have h5 : 3 / (8 * z.im) * (π * (8 / (3 * π) * z.im)) = 1 := by
      field_simp
    calc (1 : ℝ) = 3 / (8 * z.im) * (π * (8 / (3 * π) * z.im)) := h5.symm
      _ ≤ cz z * (π * (8 / (3 * π) * z.im)) := by
          apply mul_le_mul_of_nonneg_right hcfd (by positivity)
      _ = 8 / (3 * π) * z.im * (π * cz z) := by ring
  have hrate_pos : (0 : ℝ) < 1 / (π * cz z) := by positivity
  -- the amplitude bound in height form
  have hK : Kz z ≤ Real.exp (π / 2) * (1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ) *
      (1 + z.im ^ 2) := by
    calc Kz z ≤ Real.exp (π / 2) * (1 + 4 / (π * cz z) ^ 2 * latticeZ) := Kz_le z
      _ ≤ Real.exp (π / 2) * (1 + 4 * ((8 / (3 * π)) ^ 2 * z.im ^ 2) * latticeZ) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          have h6 : 4 / (π * cz z) ^ 2 ≤ 4 * ((8 / (3 * π)) ^ 2 * z.im ^ 2) := by
            rw [div_le_iff₀ (by positivity)]
            have h7 : (1 / (π * cz z)) ^ 2 ≤ (8 / (3 * π) * z.im) ^ 2 :=
              pow_le_pow_left₀ hrate_pos.le hrate 2
            have h8 : (1 / (π * cz z)) ^ 2 * (π * cz z) ^ 2 = 1 := by
              field_simp
            nlinarith [sq_nonneg (π * cz z), h7,
              mul_le_mul_of_nonneg_right h7 (sq_nonneg (π * cz z))]
          nlinarith [latticeZ_nonneg, h6]
      _ ≤ Real.exp (π / 2) * (1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ) *
            (1 + z.im ^ 2) := by
          have h9 : (0 : ℝ) ≤ 4 * (8 / (3 * π)) ^ 2 * latticeZ := by
            have := latticeZ_nonneg
            positivity
          have h10 : 1 + 4 * ((8 / (3 * π)) ^ 2 * z.im ^ 2) * latticeZ ≤
              (1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ) * (1 + z.im ^ 2) := by
            have h11 : (0 : ℝ) ≤ z.im ^ 2 := sq_nonneg _
            nlinarith [h9, h11]
          calc Real.exp (π / 2) * (1 + 4 * ((8 / (3 * π)) ^ 2 * z.im ^ 2) * latticeZ)
              ≤ Real.exp (π / 2) *
                ((1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ) * (1 + z.im ^ 2)) :=
                mul_le_mul_of_nonneg_left h10 (Real.exp_pos _).le
            _ = _ := by ring
  -- the reciprocal-rate power bound
  have hrpow : (1 / (π * cz z)) ^ N ≤ (8 / (3 * π)) ^ N * z.im ^ N := by
    rw [← Real.mul_rpow (by positivity) hy.le]
    exact Real.rpow_le_rpow hrate_pos.le hrate hN.le
  -- assemble through the splitting
  rw [lambda0_split z s]
  have hM1 := truncMellin_norm_le z hN hs1
  have hM2 := truncMellin_norm_le z hN hs2
  have hKnn : (0 : ℝ) ≤ Kz z := (Kz_pos z).le
  have hGnn : (0 : ℝ) ≤ Real.Gamma N := (Real.Gamma_pos_of_pos hN).le
  calc ‖mellin (truncTheta z) s + mellin (truncTheta z) (1 - s)‖
      ≤ ‖mellin (truncTheta z) s‖ + ‖mellin (truncTheta z) (1 - s)‖ := norm_add_le _ _
    _ ≤ 2 * (Kz z * ((1 / (π * cz z)) ^ N * Real.Gamma N)) := by
        have := hM1
        have := hM2
        linarith
    _ ≤ 2 * ((Real.exp (π / 2) * (1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ) *
          (1 + z.im ^ 2)) * (((8 / (3 * π)) ^ N * z.im ^ N) * Real.Gamma N)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul hK
        · exact mul_le_mul_of_nonneg_right hrpow hGnn
        · exact mul_nonneg (Real.rpow_nonneg hrate_pos.le N) hGnn
        · have h12 := latticeZ_nonneg
          have h13 : (0 : ℝ) ≤ 1 + 4 * (8 / (3 * π)) ^ 2 * latticeZ :=
            add_nonneg zero_le_one (mul_nonneg (by positivity) h12)
          positivity
    _ = lambdaC N * ((1 + z.im ^ 2) * z.im ^ N) := by
        rw [lambdaC]
        ring

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.P_exp_decay_on_fd
#print axioms CriticalLinePhasor.Unfolding.lambda0_bound_on_fd
