import RequestProject.GlobalHelixBilateralTensorCompletion
import RequestProject.LogThetaStrongFE

/-!
# Bounds for the Gaussian helix kernel

The Gaussian lattice series is summable at every positive height and decreases as the height
increases.  Consequently every finite 3D indexed Gaussian bank is bounded on `x ≥ 1`; multiplying
by the fixed inversion-symmetric carrier envelope makes it rapidly decreasing.
-/

open Real Complex Filter Asymptotics MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

set_option maxHeartbeats 800000 in
/-- Absolute summability of the one-dimensional Gaussian lattice at positive height. -/
theorem summable_gaussianLatticeTerm {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * a * (n : ℝ) ^ 2)) := by
  have hdec : (fun x : ℝ => Real.exp ((-Real.pi * a) * x ^ 2 + 0 * x))
      =O[atTop] (fun x : ℝ => x ^ (-2 : ℝ)) :=
    (rexp_neg_quadratic_isLittleO_rpow_atTop
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) ha) 0 (-2)).isBigO
  have hnat : Summable (fun n : ℕ => Real.exp (-Real.pi * a * (n : ℝ) ^ 2)) := by
    rw [isBigO_iff] at hdec
    rcases hdec with ⟨C, hC⟩
    apply Summable.of_norm_bounded_eventually_nat
      ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).abs.mul_left C)
    have hCnat := tendsto_natCast_atTop_atTop.eventually hC
    filter_upwards [hCnat] with n hn
    simpa only [zero_mul, add_zero, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _), abs_mul] using hn
  apply Summable.of_nat_of_neg hnat
  simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat

/-- The Gaussian lattice theta is nonnegative. -/
theorem gaussianLatticeTheta_nonneg (x : ℝ) : 0 ≤ gaussianLatticeTheta x := by
  unfold gaussianLatticeTheta
  exact tsum_nonneg fun _ => Real.exp_nonneg _

/-- Increasing a positive Gaussian height decreases its theta readout. -/
theorem gaussianLatticeTheta_antitoneOn {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    gaussianLatticeTheta b ≤ gaussianLatticeTheta a := by
  unfold gaussianLatticeTheta
  apply (summable_gaussianLatticeTerm (ha.trans_le hab)).tsum_le_tsum
  · intro n
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.pi * (n : ℝ) ^ 2 :=
      mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))
    nlinarith
  · exact summable_gaussianLatticeTerm ha

/-- The Gaussian lattice theta is continuous at every positive height. -/
theorem gaussianLatticeTheta_continuousOn :
    ContinuousOn gaussianLatticeTheta (Set.Ioi 0) := by
  intro x hx
  have hhalf : 0 < x / 2 := half_pos hx
  have hcont : ContinuousOn gaussianLatticeTheta (Set.Ici (x / 2)) := by
    unfold gaussianLatticeTheta
    apply continuousOn_tsum
    · intro n
      fun_prop
    · exact summable_gaussianLatticeTerm hhalf
    · intro n y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      apply Real.exp_le_exp.mpr
      have hp : 0 ≤ Real.pi * (n : ℝ) ^ 2 :=
        mul_nonneg Real.pi_pos.le (sq_nonneg (n : ℝ))
      calc
        -Real.pi * y * (n : ℝ) ^ 2 = -(y * (Real.pi * (n : ℝ) ^ 2)) := by ring
        _ ≤ -((x / 2) * (Real.pi * (n : ℝ) ^ 2)) :=
          neg_le_neg (mul_le_mul_of_nonneg_right hy hp)
        _ = -Real.pi * (x / 2) * (n : ℝ) ^ 2 := by ring
  have hlt : x / 2 < x := by linarith
  exact ((hcont x hlt.le).continuousAt (Ici_mem_nhds hlt)).continuousWithinAt

/-- A finite indexed Gaussian projection has polynomial exponent zero on the positive ray. -/
theorem indexedGaussianTheta_isBigO_const
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (hH : ∀ i, 0 < H i) :
    indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ))
      =O[atTop] (fun _ : ℝ => (1 : ℂ)) := by
  rw [isBigO_iff]
  refine ⟨∑ i, ‖a i‖ * gaussianLatticeTheta (H i), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  unfold indexedTheta
  rw [tsum_fintype]
  calc
    ‖∑ i, a i * (gaussianLatticeTheta (H i * x) : ℂ)‖
        ≤ ∑ i, ‖a i * (gaussianLatticeTheta (H i * x) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a i‖ * gaussianLatticeTheta (H i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gaussianLatticeTheta_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (gaussianLatticeTheta_antitoneOn (hH i)
          (le_mul_of_one_le_right (hH i).le hx)) (norm_nonneg _)
    _ = (∑ i, ‖a i‖ * gaussianLatticeTheta (H i)) *
        ‖(1 : ℂ)‖ := by simp

/-- Every finite indexed Gaussian projection is continuous on positive external heights. -/
theorem indexedGaussianTheta_continuousOn
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (hH : ∀ i, 0 < H i) :
    ContinuousOn
      (indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ))) (Set.Ioi 0) := by
  unfold indexedTheta
  rw [show (fun x : ℝ => ∑' i : I,
      a i * (fun t => (gaussianLatticeTheta t : ℂ)) (H i * x)) =
      (fun x : ℝ => ∑ i : I,
        a i * (fun t => (gaussianLatticeTheta t : ℂ)) (H i * x)) by
    funext x
    exact tsum_fintype (fun i : I =>
      a i * (fun t => (gaussianLatticeTheta t : ℂ)) (H i * x))]
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.mul continuousOn_const
  have htheta : ContinuousOn (fun x : ℝ => gaussianLatticeTheta (H i * x)) (Set.Ioi 0) :=
    gaussianLatticeTheta_continuousOn.comp (by fun_prop)
      (fun x hx => mul_pos (hH i) hx)
  change ContinuousOn
    (Complex.ofReal ∘ fun x : ℝ => gaussianLatticeTheta (H i * x)) (Set.Ioi 0)
  exact Complex.continuous_ofReal.continuousOn.comp htheta
    (fun _ _ => Set.mem_univ _)

/-- The fixed zero-weight self-dual envelope is continuous on positive heights. -/
theorem selfDualEnvelope_zero_continuousOn :
    ContinuousOn (CriticalLinePhasor.StrandExchange.selfDualEnvelope 0) (Set.Ioi 0) := by
  intro x hx
  unfold CriticalLinePhasor.StrandExchange.selfDualEnvelope
  simp only [neg_zero, zero_div, Real.rpow_zero, one_mul]
  have hinv : ContinuousAt (fun y : ℝ => y⁻¹) x := continuousAt_inv₀ hx.ne'
  exact (Real.continuous_exp.continuousAt.comp
    (continuousAt_id.neg.sub hinv)).continuousWithinAt

/-- The enveloped finite indexed bank is locally integrable on the positive half-line. -/
theorem indexedGaussianTheta_enveloped_locallyIntegrableOn
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (hH : ∀ i, 0 < H i) :
    LocallyIntegrableOn
      (fun x =>
        (CriticalLinePhasor.StrandExchange.selfDualEnvelope 0 x : ℂ) *
          indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x)
      (Set.Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact (Complex.continuous_ofReal.continuousOn.comp selfDualEnvelope_zero_continuousOn
    (fun _ _ => Set.mem_univ _)).mul (indexedGaussianTheta_continuousOn a H hH)

/-- The fixed inversion-symmetric exponential envelope turns a bounded readout into a rapidly
decreasing readout. -/
theorem selfDualEnvelope_zero_mul_rapid_of_isBigO_const
    (F : ℝ → ℂ) (hF : F =O[atTop] (fun _ : ℝ => (1 : ℂ))) :
    ∀ q : ℝ,
      (fun x => (CriticalLinePhasor.StrandExchange.selfDualEnvelope 0 x : ℂ) * F x)
        =O[atTop] (fun x : ℝ => x ^ q) := by
  intro q
  rw [isBigO_iff'] at hF ⊢
  obtain ⟨C, hCpos, hC⟩ := hF
  have hdec := (isLittleO_exp_neg_mul_rpow_atTop (a := 1) one_pos q).isBigO
  rw [isBigO_iff'] at hdec
  obtain ⟨D, hDpos, hD⟩ := hdec
  refine ⟨C * D, mul_pos hCpos hDpos, ?_⟩
  filter_upwards [hC, hD, eventually_gt_atTop (1 : ℝ)] with x hxC hxD hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hexp : Real.exp (-x - x⁻¹) ≤ Real.exp (-x) := by
    rw [Real.exp_le_exp]
    exact sub_le_self _ (inv_nonneg.mpr hx0.le)
  have hxD' : Real.exp (-x) ≤ D * x ^ q := by
    simpa [Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] using hxD
  have hxC' : ‖F x‖ ≤ C := by simpa using hxC
  simp only [CriticalLinePhasor.StrandExchange.selfDualEnvelope, zero_div, neg_zero,
    Real.rpow_zero, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-x - x⁻¹) * ‖F x‖ ≤ Real.exp (-x) * C := by gcongr
    _ ≤ (D * x ^ q) * C := by gcongr
    _ = (C * D) * ‖x ^ q‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
      ring

/-- Every finite 3D indexed Gaussian bank becomes rapidly decreasing after the fixed envelope. -/
theorem indexedGaussianTheta_enveloped_rapid
    {I : Type*} [Fintype I] (a : I → ℂ) (H : I → ℝ) (hH : ∀ i, 0 < H i) :
    ∀ q : ℝ,
      (fun x =>
        (CriticalLinePhasor.StrandExchange.selfDualEnvelope 0 x : ℂ) *
          indexedTheta a H (fun t => (gaussianLatticeTheta t : ℂ)) x)
        =O[atTop] (fun x : ℝ => x ^ q) :=
  selfDualEnvelope_zero_mul_rapid_of_isBigO_const _
    (indexedGaussianTheta_isBigO_const a H hH)

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.summable_gaussianLatticeTerm
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeTheta_antitoneOn
#print axioms CriticalLinePhasor.GlobalHelix.gaussianLatticeTheta_continuousOn
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussianTheta_isBigO_const
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussianTheta_continuousOn
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussianTheta_enveloped_locallyIntegrableOn
#print axioms CriticalLinePhasor.GlobalHelix.selfDualEnvelope_zero_mul_rapid_of_isBigO_const
#print axioms CriticalLinePhasor.GlobalHelix.indexedGaussianTheta_enveloped_rapid
