import RequestProject.XiKernelThetaBridge
import RequestProject.XiStageHolomorphy
import RequestProject.MellinPathToXi

/-!
# Identification of the entire cosine integral

Unfolded target: `2 ∫₀∞ K(u) cos(zu) du = 2 ξ(1/2 + iz)`, with
`K = ψ'' - ψ/4` and `ψ(u) = (theta(exp(2u))-1) exp(u/2)`.
The factor two comes from the existing definition of `xiIntegral`.

Expectation-free decomposition A: integrate the derivative of
`ψ'(u) cos(zu) + z ψ(u) sin(zu)` on the positive half-line.
First Lean step: `apply MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`.
Decomposition B: integrate by parts twice on `[0,U]` and pass to the limit.
First Lean step: `apply intervalIntegral.integral_eq_sub_of_hasDerivAt`.
The first route collects both boundary terms in one primitive.

Searches:
`rg -n -i 'xiIntegral.*riemannXi|riemannXi.*xiIntegral|xiIntegral_eq|xi_integral|cosine.*riemannXi|riemannXi.*cosine' RequestProject .lake/packages/mathlib/Mathlib`
`rg -n 'psiD1|psiD2|psi.*(zero|decay|tendsto)|riemannXiKernel_eq_psi|integral_Ioi.*deriv' RequestProject -g '*.lean'`
`rg -n 'cosh_mul_I|cos_mul_I|hasDerivAt_ofReal|ofReal_comp|squeeze_zero_norm|tendsto_exp_atBot' .lake/packages/mathlib/Mathlib`
Semantic searches: LeanSearch "integral over positive half line of derivative
limit at infinity continuous at zero"; Loogle `"integral", "mul_deriv"`.
-/

open Real Complex MeasureTheory Filter Topology

noncomputable section

namespace CriticalLinePhasor.XiKernelBridge

open CriticalLinePhasor.ThetaWronskianSuzukiGram

theorem psi_eq_mellin : psi = ZD.ψ_mellin := rfl

theorem psiD1_zero : psiD1 0 = -1 / 2 := by
  have href := xiThetaProfile_deriv_reflection 0
  rw [(xiThetaProfile_hasDerivAt 0).deriv,
    xiThetaProfile_eq_zero_add_positive] at href
  simp only [neg_zero, Real.exp_zero, one_mul] at href
  rw [(xiThetaProfile_hasDerivAt 0).deriv] at href
  simp only [psiD1, thetaSum, zero_div, Real.exp_zero, one_mul]
  linarith

theorem kernel_eq_psiD2 (u : ℝ) :
    riemannXiKernel u = psiD2 u - psi u / 4 := by
  rw [riemannXiKernel_eq_psi_operator]
  have h : deriv psi = psiD1 := funext fun v => (hasDerivAt_psi v).deriv
  rw [h, (hasDerivAt_psiD1 u).deriv]

theorem xiKernelQ_ge_three (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    3 ≤ xiKernelQ n u := by
  have hn : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hp := mul_le_mul_of_nonneg_left hn Real.pi_pos.le
  have hq := le_mul_of_one_le_right
    (show 0 ≤ Real.pi * ((n : ℝ) + 1) ^ 2 by positivity) he
  dsimp [xiKernelQ]
  linarith [Real.pi_gt_three]

theorem kernelTerm_eq_q (n : ℕ) (u : ℝ) :
    4 * riemannXiKernelTerm n u =
      Real.exp (u / 2) * (8 * xiKernelQ n u ^ 2 - 12 * xiKernelQ n u) *
        Real.exp (-xiKernelQ n u) := by
  rw [four_mul_riemannXiKernelTerm_eq_thetaOperatorTerm]
  simp only [xiThetaSeriesDeriv1, xiThetaSeriesDeriv2]
  ring

theorem psi_abs_le_kernel {u : ℝ} (hu : 0 ≤ u) :
    |psi u| ≤ riemannXiKernel u := by
  have hp : 0 ≤ thetaSum u := tsum_nonneg fun n => by
    rw [xiThetaSeriesTerm_eq]; positivity
  rw [psi_eq, abs_of_nonneg (by positivity)]
  rw [thetaSum, ← tsum_mul_left, riemannXiKernel, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((xiThetaSeriesTerm_summable u).mul_left _) ((riemannXiKernelTerm_summable u).mul_left _)
  intro n
  rw [xiThetaSeriesTerm_eq, kernelTerm_eq_q]
  have hq := xiKernelQ_ge_three n hu
  have hpoly : (2 : ℝ) ≤ 8 * xiKernelQ n u ^ 2 - 12 * xiKernelQ n u := by
    nlinarith [sq_nonneg (xiKernelQ n u - 3)]
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos (u / 2)).le)
    (Real.exp_pos (-xiKernelQ n u)).le]

theorem psiD1_abs_le_kernel {u : ℝ} (hu : 0 ≤ u) :
    |psiD1 u| ≤ riemannXiKernel u := by
  have he := (Real.exp_pos (u / 2)).le
  have hsum : psiD1 u = ∑' n : ℕ,
      Real.exp (u / 2) * (xiThetaSeriesTerm n u + 2 * xiThetaSeriesDeriv1 n u) := by
    rw [tsum_mul_left, (xiThetaSeriesTerm_summable u).tsum_add
      ((xiThetaSeriesDeriv1_summable u).mul_left 2), tsum_mul_left]
    rfl
  rw [hsum, ← Real.norm_eq_abs]
  have hs := ((xiThetaSeriesTerm_summable u).add
    ((xiThetaSeriesDeriv1_summable u).mul_left 2)).mul_left (Real.exp (u / 2))
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [riemannXiKernel, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ hs.norm ((riemannXiKernelTerm_summable u).mul_left 4)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he,
    xiThetaSeriesTerm_eq, xiThetaSeriesDeriv1, kernelTerm_eq_q]
  have hq := xiKernelQ_ge_three n hu
  have hinner : Real.exp (-xiKernelQ n u) + 2 * (-2 * xiKernelQ n u *
      Real.exp (-xiKernelQ n u)) =
      (1 - 4 * xiKernelQ n u) * Real.exp (-xiKernelQ n u) := by ring
  rw [hinner, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonpos (by linarith)]
  have hpoly : -(1 - 4 * xiKernelQ n u) ≤
      8 * xiKernelQ n u ^ 2 - 12 * xiKernelQ n u := by
    nlinarith [sq_nonneg (xiKernelQ n u - 3)]
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpoly he) (Real.exp_pos (-xiKernelQ n u)).le]

theorem kernel_weight_tendsto (Y : ℝ) :
    Tendsto (fun u : ℝ => |riemannXiKernel u| * Real.exp (Y * u))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun u : ℝ =>
      (8 * Real.pi ^ 2 * Real.exp Real.pi) * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (8 * Real.pi ^ 2 * Real.exp Real.pi)
  apply squeeze_zero' (Eventually.of_forall fun u => by positivity) _ hlim
  filter_upwards [eventually_ge_atTop (max 4 Y)] with u hu
  have hu4 : 4 ≤ u := le_trans (le_max_left _ _) hu
  have huY : Y ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : 0 ≤ u := by linarith
  have he1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have he2 : (1 + u) ^ 2 ≤ Real.exp (2 * u) := by
    rw [show 2 * u = u + u by ring, Real.exp_add]
    nlinarith [Real.exp_pos u]
  have he3 : (9 / 2 + Y) * u - Real.pi * Real.exp (2 * u) ≤ -u := by
    nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le (sq_nonneg (1 + u)),
      mul_le_mul_of_nonneg_left he2 Real.pi_pos.le]
  calc |riemannXiKernel u| * Real.exp (Y * u)
      ≤ (8 * Real.pi ^ 2 * Real.exp Real.pi * Real.exp (9 * u / 2) *
          Real.exp (-Real.pi * Real.exp (2 * u))) * Real.exp (Y * u) :=
        mul_le_mul_of_nonneg_right (kernel_abs_bound hu0) (Real.exp_pos _).le
    _ = (8 * Real.pi ^ 2 * Real.exp Real.pi) *
        Real.exp ((9 / 2 + Y) * u - Real.pi * Real.exp (2 * u)) := by
      rw [show (9 / 2 + Y) * u - Real.pi * Real.exp (2 * u) =
        9 * u / 2 + -Real.pi * Real.exp (2 * u) + Y * u by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ (8 * Real.pi ^ 2 * Real.exp Real.pi) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he3) (by positivity)

def cosinePrimitive (z : ℂ) (u : ℝ) : ℂ :=
  (psiD1 u : ℂ) * Complex.cos (z * u) +
    z * (psi u : ℂ) * Complex.sin (z * u)

theorem cosinePrimitive_hasDerivAt (z : ℂ) (u : ℝ) :
    HasDerivAt (cosinePrimitive z)
      ((riemannXiKernel u : ℂ) * Complex.cos (z * u) +
        (z ^ 2 + 1 / 4) * ((psi u : ℂ) * Complex.cos (z * u))) u := by
  have hc := (((hasDerivAt_id (u : ℂ)).const_mul z).ccos).comp_ofReal
  have hs := (((hasDerivAt_id (u : ℂ)).const_mul z).csin).comp_ofReal
  have h := ((hasDerivAt_psiD1 u).ofReal_comp.mul hc).add
    (((hasDerivAt_psi u).ofReal_comp.const_mul z).mul hs)
  apply h.congr_deriv
  rw [kernel_eq_psiD2]
  simp only [id_eq]
  push_cast
  ring

theorem cosinePrimitive_tendsto (z : ℂ) :
    Tendsto (cosinePrimitive z) atTop (𝓝 0) := by
  have hlim := (kernel_weight_tendsto |z.im|).const_mul (1 + ‖z‖)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  have hK : 0 ≤ riemannXiKernel u := riemannXiKernel_nonneg hu
  have hd := psiD1_abs_le_kernel hu
  have hp := psi_abs_le_kernel hu
  have hc := cos_strip_bound (z := z) hu (le_refl |z.im|)
  have hs := sin_strip_bound (z := z) hu (le_refl |z.im|)
  calc ‖cosinePrimitive z u‖
      ≤ ‖(psiD1 u : ℂ) * Complex.cos (z * u)‖ +
        ‖z * (psi u : ℂ) * Complex.sin (z * u)‖ := norm_add_le _ _
    _ ≤ riemannXiKernel u * Real.exp (|z.im| * u) +
        ‖z‖ * (riemannXiKernel u * Real.exp (|z.im| * u)) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := mul_le_mul hd hc (norm_nonneg _) hK
      have h2 := mul_le_mul hp hs (norm_nonneg _) hK
      nlinarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg z)]
    _ = (1 + ‖z‖) * (|riemannXiKernel u| * Real.exp (|z.im| * u)) := by
      rw [abs_of_nonneg hK]; ring

theorem mellin_cosine_integrand (z : ℂ) (u : ℝ) :
    (2 : ℂ) * Complex.cosh (((1 / 2 + Complex.I * z) - 1 / 2) * (u : ℂ)) *
        (ZD.ψ_mellin u : ℂ) =
      2 * ((psi u : ℂ) * Complex.cos (z * u)) := by
  rw [show ((1 / 2 + Complex.I * z) - 1 / 2) * (u : ℂ) =
    (z * u) * Complex.I by ring, Complex.cosh_mul_I]
  rw [psi_eq_mellin]
  ring

theorem psi_cosine_integrable (z : ℂ) :
    IntegrableOn (fun u : ℝ => (psi u : ℂ) * Complex.cos (z * u)) (Set.Ioi 0) := by
  have h := ZD.integrable_I_theta_integrand (1 / 2 + Complex.I * z)
  simp only [mellin_cosine_integrand] at h
  have h2 := h.const_mul (1 / 2 : ℂ)
  simpa [IntegrableOn] using h2

theorem kernel_cosine_integral (z : ℂ) :
    ∫ u in Set.Ioi (0 : ℝ), (riemannXiKernel u : ℂ) * Complex.cos (z * u) =
      1 / 2 - (z ^ 2 + 1 / 4) *
        ∫ u in Set.Ioi (0 : ℝ), (psi u : ℂ) * Complex.cos (z * u) := by
  have hi := (xiIntegrand_integrableOn z).add
    ((psi_cosine_integrable z).const_mul (z ^ 2 + 1 / 4))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (cosinePrimitive_hasDerivAt z 0).continuousAt.continuousWithinAt
    (fun u _ => cosinePrimitive_hasDerivAt z u) hi (cosinePrimitive_tendsto z)
  rw [integral_add (xiIntegrand_integrableOn z)
    ((psi_cosine_integrable z).const_mul (z ^ 2 + 1 / 4)), integral_const_mul] at h
  simp only [cosinePrimitive, Complex.ofReal_zero, mul_zero, Complex.cos_zero, Complex.sin_zero,
    mul_one, add_zero, psiD1_zero] at h
  push_cast at h
  linear_combination h

theorem xiIntegral_eq_two_mul_riemannXi (z : ℂ) :
    xiIntegral z = 2 * ZD.riemannXi (1 / 2 + Complex.I * z) := by
  rw [ZD.riemannXi_eq_observable, ZD.I_theta_of]
  simp only [mellin_cosine_integrand]
  rw [integral_const_mul, xiIntegral, kernel_cosine_integral]
  have hI := Complex.I_sq
  ring_nf
  simp only [hI]
  ring

theorem xiIntegral_half_eq_riemannXi (z : ℂ) :
    xiIntegral z / 2 = ZD.riemannXi (1 / 2 + Complex.I * z) := by
  rw [xiIntegral_eq_two_mul_riemannXi]
  ring

theorem xiIntegral_zero_iff (z : ℂ) :
    xiIntegral z = 0 ↔ ZD.riemannXi (1 / 2 + Complex.I * z) = 0 := by
  rw [xiIntegral_eq_two_mul_riemannXi]
  simp

/-- The frequency chart inverse to `s = 1/2 + iz`. -/
def xiFrequency (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

theorem xiFrequency_chart (s : ℂ) : 1 / 2 + Complex.I * xiFrequency s = s := by
  unfold xiFrequency
  linear_combination -(s - 1 / 2) * Complex.I_sq

/-- The existing cosine stages in the arithmetic chart, with their normalization fixed. -/
def xiArithmeticStage (U : ℝ) (s : ℂ) : ℂ := xiStage U (xiFrequency s) / 2

theorem xiFrequency_hasDerivAt (s : ℂ) :
    HasDerivAt xiFrequency (-Complex.I) s := by
  change HasDerivAt (fun y : ℂ => -Complex.I * (y - 1 / 2)) (-Complex.I) s
  simpa only [id_eq, mul_one] using
    ((hasDerivAt_id s).sub_const (1 / 2)).const_mul (-Complex.I)

theorem xiArithmeticStage_differentiable (U : ℝ) :
    Differentiable ℂ (xiArithmeticStage U) := by
  intro s
  exact (((xiStage_differentiable U).differentiableAt.comp s
    (xiFrequency_hasDerivAt s).differentiableAt).div_const 2)

theorem xiArithmeticStage_tendsto (s : ℂ) :
    Tendsto (fun n : ℕ => xiArithmeticStage n s) atTop (𝓝 (ZD.riemannXi s)) := by
  have h := (xiStage_tendsto_xiIntegral (xiFrequency s)).div_const (2 : ℂ)
  rw [xiIntegral_half_eq_riemannXi, xiFrequency_chart] at h
  exact h

theorem deriv_xiArithmeticStage (U : ℝ) (s : ℂ) :
    deriv (xiArithmeticStage U) s =
      deriv (xiStage U) (xiFrequency s) * (-Complex.I) / 2 := by
  exact ((((xiStage_differentiable U) (xiFrequency s)).hasDerivAt.comp s
    (xiFrequency_hasDerivAt s)).div_const 2).deriv

theorem deriv_riemannXi_eq (s : ℂ) :
    deriv ZD.riemannXi s = deriv xiIntegral (xiFrequency s) * (-Complex.I) / 2 := by
  have h : (fun w => xiIntegral (xiFrequency w) / 2) = ZD.riemannXi := by
    funext w
    rw [xiIntegral_half_eq_riemannXi, xiFrequency_chart]
  rw [← h]
  exact (((xiIntegral_differentiable (xiFrequency s)).hasDerivAt.comp s
    (xiFrequency_hasDerivAt s)).div_const 2).deriv

theorem deriv_xiArithmeticStage_tendsto (s : ℂ) :
    Tendsto (fun n : ℕ => deriv (xiArithmeticStage n) s) atTop
      (𝓝 (deriv ZD.riemannXi s)) := by
  simp only [deriv_xiArithmeticStage, deriv_riemannXi_eq]
  exact ((deriv_xiStage_tendsto (xiFrequency s)).mul_const (-Complex.I)).div_const 2

/-- Both analytic approximation clauses hold for the explicit theta stages at every point. -/
theorem xiArithmeticStage_value_and_derivative (s : ℂ) :
    Tendsto (fun n : ℕ => xiArithmeticStage n s) atTop (𝓝 (ZD.riemannXi s)) ∧
      Tendsto (fun n : ℕ => deriv (xiArithmeticStage n) s) atTop
        (𝓝 (deriv ZD.riemannXi s)) :=
  ⟨xiArithmeticStage_tendsto s, deriv_xiArithmeticStage_tendsto s⟩

end CriticalLinePhasor.XiKernelBridge

#print axioms ZD.riemannXi_eq_observable
#print axioms CriticalLinePhasor.XiKernelBridge.riemannXiKernel_eq_psi_operator
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiThetaProfile_deriv_reflection
#print axioms CriticalLinePhasor.XiKernelBridge.psiD1_zero
#print axioms CriticalLinePhasor.XiKernelBridge.psi_abs_le_kernel
#print axioms CriticalLinePhasor.XiKernelBridge.psiD1_abs_le_kernel
#print axioms CriticalLinePhasor.XiKernelBridge.kernel_weight_tendsto
#print axioms CriticalLinePhasor.XiKernelBridge.xiIntegral_eq_two_mul_riemannXi
#print axioms CriticalLinePhasor.XiKernelBridge.xiIntegral_half_eq_riemannXi
#print axioms CriticalLinePhasor.XiKernelBridge.xiIntegral_zero_iff
#print axioms CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_value_and_derivative
#print axioms CriticalLinePhasor.XiKernelBridge.xiArithmeticStage_differentiable
