import RequestProject.GlobalHelixFullTensorEulerSummability

/-!
# Analytic positive-height control of the full 3D tensor-Euler bank

The primal full exponent-lattice readout is locally uniformly convergent.  Its
anti-helix dual is then controlled by the exact 3D inversion law, giving local
integrability on both sides without imposing finiteness on the lattice.
-/

open Real Complex Filter Asymptotics MeasureTheory

namespace CriticalLinePhasor.GlobalHelix

/-- On positive heights the dual theta is the primal theta read at reciprocal
height, divided by the geometric half-density. -/
theorem fullTensorEulerZeroModeDualTheta_eq_div
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    indexedZeroModeGaussianTheta
        (gaussianPoissonDualAmplitude (bilateralTensorEulerSeed S W)
          (bilateralEulerHeight S q) (negExponentEquiv S))
        (bilateralEulerHeight S q) c x =
      indexedZeroModeGaussianTheta
          (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c (1 / x) /
        (((x ^ ((2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
  let a := bilateralTensorEulerSeed S W
  let H := bilateralEulerHeight S q
  let dual := negExponentEquiv S
  have hH : ∀ k, 0 < H k := bilateralEulerHeight_pos S q
    (fun v hv => zero_lt_one.trans (hq v hv))
  have hrecip : ∀ k, H (dual.symm k) = (H k)⁻¹ := by
    intro k
    simpa [H, dual, negExponentEquiv] using
      bilateralEulerHeight_negExponentEquiv S q k
  have href := indexedZeroModeGaussianTheta_reflection a H dual hH hrecip hc
    (one_div_pos.mpr hx)
  simp only [one_div, inv_inv] at href
  have hscale : 1 / x⁻¹ ^ ((2 : ℝ)⁻¹) = x ^ ((2 : ℝ)⁻¹) := by
    rw [Real.inv_rpow hx.le]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hx _)]
  have hscaleC :
      ((((x⁻¹ ^ ((2 : ℝ)⁻¹))⁻¹ : ℝ) : ℂ)) =
        (((x ^ ((2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
    have hscale' : (x⁻¹ ^ ((2 : ℝ)⁻¹))⁻¹ = x ^ ((2 : ℝ)⁻¹) := by
      simpa only [one_div] using hscale
    simpa only [ofReal_inv] using congrArg (fun y : ℝ => (y : ℂ)) hscale'
  change indexedZeroModeGaussianTheta a H c x⁻¹ =
    ((((x⁻¹ ^ ((2 : ℝ)⁻¹))⁻¹ : ℝ) : ℂ)) *
      indexedZeroModeGaussianTheta (gaussianPoissonDualAmplitude a H dual) H c x at href
  rw [hscaleC] at href
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.rpow_pos_of_pos hx _)))).2
  simpa [a, H, dual, one_div, mul_comm] using href.symm

/-- The complete anti-helix scalar projection is continuous on the positive
height chart; this is transported from the primal bank by 3D inversion. -/
theorem fullTensorEulerZeroModeDualTheta_continuousOn
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c : ℝ} (hc : 0 < c) :
    ContinuousOn
      (indexedZeroModeGaussianTheta
        (gaussianPoissonDualAmplitude (bilateralTensorEulerSeed S W)
          (bilateralEulerHeight S q) (negExponentEquiv S))
        (bilateralEulerHeight S q) c)
      (Set.Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  simp only [Set.mem_Ioi] at hx
  have hinvx : 0 < 1 / x := one_div_pos.mpr hx
  have hP := fullTensorEulerZeroModeTheta_continuousOn S W q hq hc
  have hPAt := (hP (1 / x) hinvx).continuousAt (Ioi_mem_nhds hinvx)
  have hinvAt : ContinuousAt (fun y : ℝ => 1 / y) x :=
    continuousAt_const.div continuousAt_id hx.ne'
  have hnum := hPAt.comp hinvAt
  have hrpow := Real.continuousAt_rpow_const x ((2 : ℝ)⁻¹) (Or.inl hx.ne')
  have hden := Complex.continuous_ofReal.continuousAt.comp hrpow
  have hrhs := hnum.div hden (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.rpow_pos_of_pos hx _)))
  apply hrhs.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact fullTensorEulerZeroModeDualTheta_eq_div S W q hq hc hy

/-- The complete anti-helix projection is locally integrable on positive
multiplicative heights. -/
theorem fullTensorEulerZeroModeDualTheta_locallyIntegrableOn
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c : ℝ} (hc : 0 < c) :
    LocallyIntegrableOn
      (indexedZeroModeGaussianTheta
        (gaussianPoissonDualAmplitude (bilateralTensorEulerSeed S W)
          (bilateralEulerHeight S q) (negExponentEquiv S))
        (bilateralEulerHeight S q) c)
      (Set.Ioi 0) :=
  (fullTensorEulerZeroModeDualTheta_continuousOn S W q hq hc).locallyIntegrableOn
    measurableSet_Ioi

/-- The primal full-lattice tensor-Euler bank decays faster than every power at
the upper end of the positive height chart. -/
theorem fullTensorEulerZeroModeTheta_rapid
    {V ι : Type*} [Fintype ι]
    (S : Finset V) (W : V → FiniteWeightFiber ι) (q : V → ℝ)
    (hq : ∀ v ∈ S, 1 < q v) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    indexedZeroModeGaussianTheta
        (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c
      =O[atTop] (fun x : ℝ => x ^ r) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-r)
  let L : ℕ := N + 1
  have hL : 0 < L := by omega
  have hs := summable_fullTensorEulerCoeff_mul_height_rpow S W q hq 1 (by omega)
  obtain ⟨C, hC0, hC⟩ :=
    exists_zeroModeGaussianKernel_ray_rpow_bound hc (x := 1) zero_lt_one L
  let A : ℝ := ∑' k : (v : S) → ℤ,
    ‖bilateralTensorEulerSeed S W k‖ *
      bilateralEulerHeight S q k ^ (-1 : ℝ)
  have hA0 : 0 ≤ A := tsum_nonneg fun k =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
      (bilateralEulerHeight_pos S q
        (fun v hv => zero_lt_one.trans (hq v hv)) k).le _)
  rw [isBigO_iff]
  refine ⟨1 + C * A, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hterm : ∀ k : (v : S) → ℤ,
      ‖bilateralTensorEulerSeed S W k *
          zeroModeGaussianKernel c (bilateralEulerHeight S q k * x)‖ ≤
        (C * x ^ (-(N : ℝ))) *
          (‖bilateralTensorEulerSeed S W k‖ *
            bilateralEulerHeight S q k ^ (-1 : ℝ)) := by
    intro k
    by_cases hk0 : ∀ v, 0 ≤ k v
    swap
    · unfold bilateralTensorEulerSeed
      rw [if_neg hk0]
      simp
    let H := bilateralEulerHeight S q k
    have hHpos : 0 < H := bilateralEulerHeight_pos S q
      (fun v hv => zero_lt_one.trans (hq v hv)) k
    have hH1 : 1 ≤ H := by
      unfold H bilateralEulerHeight
      apply Finset.one_le_prod
      intro v hv
      exact one_le_zpow₀ (le_of_lt (hq v v.property)) (hk0 v)
    have hHx1 : 1 ≤ H * x := by nlinarith
    have hk := hC (H * x) hHx1
    simp only [mul_one] at hk
    have hHL : H ^ (-(L : ℝ)) ≤ H ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hH1
      dsimp [L]
      norm_num
    have hxL : x ^ (-(L : ℝ)) ≤ x ^ (-(N : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hx
      dsimp [L]
      norm_num
    rw [norm_mul]
    calc
      ‖bilateralTensorEulerSeed S W k‖ *
          ‖zeroModeGaussianKernel c (H * x)‖
          ≤ ‖bilateralTensorEulerSeed S W k‖ *
              (C * (H * x) ^ (-(L : ℝ))) := by gcongr
      _ = ‖bilateralTensorEulerSeed S W k‖ *
          (C * (H ^ (-(L : ℝ)) * x ^ (-(L : ℝ)))) := by
            rw [Real.mul_rpow hHpos.le hxpos.le]
      _ ≤ ‖bilateralTensorEulerSeed S W k‖ *
          (C * (H ^ (-1 : ℝ) * x ^ (-(N : ℝ)))) := by
            gcongr
      _ = (C * x ^ (-(N : ℝ))) *
          (‖bilateralTensorEulerSeed S W k‖ * H ^ (-1 : ℝ)) := by ring
  have hmajor : Summable (fun k : (v : S) → ℤ =>
      (C * x ^ (-(N : ℝ))) *
        (‖bilateralTensorEulerSeed S W k‖ *
          bilateralEulerHeight S q k ^ (-1 : ℝ))) := by
    simpa using hs.mul_left (C * x ^ (-(N : ℝ)))
  calc
    ‖indexedZeroModeGaussianTheta
        (bilateralTensorEulerSeed S W) (bilateralEulerHeight S q) c x‖
        ≤ ∑' k : (v : S) → ℤ,
          (C * x ^ (-(N : ℝ))) *
            (‖bilateralTensorEulerSeed S W k‖ *
              bilateralEulerHeight S q k ^ (-1 : ℝ)) := by
          unfold indexedZeroModeGaussianTheta indexedTheta
          exact tsum_of_norm_bounded hmajor.hasSum hterm
    _ = (C * A) * x ^ (-(N : ℝ)) := by
      rw [tsum_mul_left]
      dsimp [A]
      ring
    _ ≤ (1 + C * A) * x ^ r := by
      have hpow : x ^ (-(N : ℝ)) ≤ x ^ r :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      have hCA0 : 0 ≤ C * A := mul_nonneg hC0 hA0
      calc
        (C * A) * x ^ (-(N : ℝ)) ≤ (C * A) * x ^ r :=
          mul_le_mul_of_nonneg_left hpow hCA0
        _ ≤ (1 + C * A) * x ^ r :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hxpos.le r)
    _ = (1 + C * A) * ‖x ^ r‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le _)]

#print axioms fullTensorEulerZeroModeDualTheta_eq_div
#print axioms fullTensorEulerZeroModeDualTheta_continuousOn
#print axioms fullTensorEulerZeroModeDualTheta_locallyIntegrableOn
#print axioms fullTensorEulerZeroModeTheta_rapid

end CriticalLinePhasor.GlobalHelix
