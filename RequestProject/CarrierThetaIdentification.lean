import RequestProject.CompletedBankStrongFE

/-!
# Mellin identification of carrier theta banks

This file proves the term-by-term readout identity used in the E5 step of the carrier construction.
Scaling the completion kernel by the `n`th carrier height contributes exactly `(n+1)⁻ˢ` to its
Mellin transform.  Finite theta banks therefore transform into the corresponding finite Dirichlet
readout times the Mellin transform of the completion kernel.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators

namespace CriticalLinePhasor.CarrierTheta

/-- The first `N` coefficient phasors smoothed by the completion kernel `g`. -/
noncomputable def finiteTheta (a : ℕ → ℂ) (g : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * g ((n + 1 : ℕ) * x)

/-- The finite Dirichlet readout attached to the first `N` coefficient phasors. -/
noncomputable def finiteDirichlet (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * ((n + 1 : ℕ) : ℂ) ^ (-s)

/-- Scaling the kernel by the `n`th positive carrier height contributes `(n+1)⁻ˢ` to the Mellin
transform, and the coefficient `a n` passes through as a scalar. -/
theorem coefficientTerm_hasMellin (a : ℕ → ℂ) (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s) (n : ℕ) :
    HasMellin (fun x : ℝ => a n * g ((n + 1 : ℕ) * x)) s
      (a n * (((n + 1 : ℕ) : ℂ) ^ (-s) * mellin g s)) := by
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hconv : MellinConvergent (fun x : ℝ => g (((n + 1 : ℕ) : ℝ) * x)) s :=
    (MellinConvergent.comp_mul_left hn).2 hg
  have h := hasMellin_const_smul hconv (a n)
  refine ⟨h.1, ?_⟩
  calc
    mellin (fun x : ℝ => a n * g ((n + 1 : ℕ) * x)) s =
        a n * mellin (fun x : ℝ => g (((n + 1 : ℕ) : ℝ) * x)) s := by
      simpa [smul_eq_mul] using h.2
    _ = a n * (((n + 1 : ℕ) : ℂ) ^ (-s) * mellin g s) := by
      rw [mellin_comp_mul_left g s hn]
      simp [smul_eq_mul]

/-- E5 for a finite carrier bank: its Mellin transform is the finite Dirichlet readout multiplied
by the Mellin transform of the completion kernel. -/
theorem finiteTheta_hasMellin (a : ℕ → ℂ) (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s) (N : ℕ) :
    HasMellin (finiteTheta a g N) s (finiteDirichlet a N s * mellin g s) := by
  induction N with
  | zero =>
      simp [finiteTheta, finiteDirichlet, HasMellin, MellinConvergent, mellin]
  | succ N ih =>
      have ht := coefficientTerm_hasMellin a g hg N
      have hadd := hasMellin_add ih.1 ht.1
      have hfun : finiteTheta a g (N + 1) =
          fun x => finiteTheta a g N x + a N * g ((N + 1 : ℕ) * x) := by
        funext x
        simp [finiteTheta, Finset.sum_range_succ]
      rw [hfun]
      refine ⟨hadd.1, ?_⟩
      rw [hadd.2, ih.2, ht.2]
      simp only [finiteDirichlet, Finset.sum_range_succ]
      ring

/-- The full coefficient theta assembled from every carrier height. -/
noncomputable def theta (a : ℕ → ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, a n * g ((n + 1 : ℕ) * x)

/-- The full Dirichlet readout of the coefficient bank. -/
noncomputable def dirichlet (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, a n * ((n + 1 : ℕ) : ℂ) ^ (-s)

/-- E5 for the full carrier theta.  Absolute summability of the Mellin-integrand norms is exactly
the dominated-convergence condition needed to interchange the coefficient bank with the integral.
The conclusion identifies the already convergent global carrier transform with the Dirichlet
readout times the completion kernel's Mellin transform. -/
theorem theta_hasMellin
    (a : ℕ → ℂ) (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s)
    (hglobal : MellinConvergent (theta a g) s)
    (hnorm : Summable fun n : ℕ =>
      ∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))‖) :
    HasMellin (theta a g) s (dirichlet a s * mellin g s) := by
  let F : ℕ → ℝ → ℂ := fun n x =>
    (x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    change IntegrableOn (F n) (Ioi 0)
    simpa [F, MellinConvergent, smul_eq_mul] using
      (coefficientTerm_hasMellin a g hg n).1
  have hFsum : Summable fun n => ∫ x, ‖F n x‖ ∂(volume.restrict (Ioi 0)) := by
    simpa [F] using hnorm
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  refine ⟨hglobal, ?_⟩
  calc
    mellin (theta a g) s = ∫ x : ℝ in Ioi 0, ∑' n : ℕ, F n x := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simpa [F, theta, smul_eq_mul] using
        (tsum_mul_left (f := fun n : ℕ => a n * g ((n + 1 : ℕ) * x))
          (a := (x : ℂ) ^ (s - 1))).symm
    _ = ∑' n : ℕ, ∫ x : ℝ in Ioi 0, F n x := hswap.symm
    _ = ∑' n : ℕ, a n * (((n + 1 : ℕ) : ℂ) ^ (-s) * mellin g s) := by
      apply tsum_congr
      intro n
      simpa [F, mellin, smul_eq_mul] using (coefficientTerm_hasMellin a g hg n).2
    _ = dirichlet a s * mellin g s := by
      rw [dirichlet, ← tsum_mul_right]
      apply tsum_congr
      intro n
      ring

/-- Exact norm-integral scaling for one coefficient term.  The change of variables
`u = (n+1)x` contributes `(n+1)⁻ᴿᵉˢ`. -/
theorem coefficientTerm_integral_norm_eq
    (a : ℕ → ℂ) (g : ℝ → ℂ) (s : ℂ) (n : ℕ) :
    (∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))‖) =
      ‖a n‖ * (((n + 1 : ℕ) : ℝ) ^ (-s.re) *
        ∫ u : ℝ in Ioi 0, u ^ (s.re - 1) * ‖g u‖) := by
  let N : ℝ := (n + 1 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hnorm : ∀ x ∈ Ioi (0 : ℝ),
      ‖(x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))‖ =
        ‖a n‖ * (x ^ (s.re - 1) * ‖g (N * x)‖) := by
    intro x hx
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [N]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hnorm, integral_const_mul]
  have hscale : ∀ x ∈ Ioi (0 : ℝ),
      x ^ (s.re - 1) * ‖g (N * x)‖ =
        N ^ (1 - s.re) * ((N * x) ^ (s.re - 1) * ‖g (N * x)‖) := by
    intro x hx
    rw [Real.mul_rpow hN.le hx.le]
    have hpow : N ^ (1 - s.re) * N ^ (s.re - 1) = 1 := by
      rw [← Real.rpow_add hN]
      simp
    calc
      x ^ (s.re - 1) * ‖g (N * x)‖ =
          1 * (x ^ (s.re - 1) * ‖g (N * x)‖) := by ring
      _ = (N ^ (1 - s.re) * N ^ (s.re - 1)) *
          (x ^ (s.re - 1) * ‖g (N * x)‖) := by rw [hpow]
      _ = N ^ (1 - s.re) *
          (N ^ (s.re - 1) * x ^ (s.re - 1) * ‖g (N * x)‖) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi hscale, integral_const_mul,
    integral_comp_mul_left_Ioi (fun u : ℝ => u ^ (s.re - 1) * ‖g u‖) 0 hN]
  simp only [mul_zero]
  have hNpow : N ^ (1 - s.re) * N⁻¹ = N ^ (-s.re) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN]
    congr 1
    ring
  simp only [smul_eq_mul]
  calc
    ‖a n‖ * (N ^ (1 - s.re) *
        (N⁻¹ * ∫ x : ℝ in Ioi 0, x ^ (s.re - 1) * ‖g x‖)) =
        ‖a n‖ * ((N ^ (1 - s.re) * N⁻¹) *
          ∫ x : ℝ in Ioi 0, x ^ (s.re - 1) * ‖g x‖) := by ring
    _ = ‖a n‖ * (N ^ (-s.re) *
          ∫ x : ℝ in Ioi 0, x ^ (s.re - 1) * ‖g x‖) := by rw [hNpow]
    _ = ‖a n‖ * (((n + 1 : ℕ) : ℝ) ^ (-s.re) *
          ∫ x : ℝ in Ioi 0, x ^ (s.re - 1) * ‖g x‖) := rfl

/-- A polynomial coefficient bound discharges the dominated-sum hypothesis in the initial
half-plane `A + 1 < re s`. -/
theorem coefficientTerm_integral_norm_summable_of_polynomial
    (a : ℕ → ℂ) (g : ℝ → ℂ) (s : ℂ) (C A : ℝ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (hs : A + 1 < s.re) :
    Summable fun n : ℕ =>
      ∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))‖ := by
  let B : ℝ := ∫ u : ℝ in Ioi 0, u ^ (s.re - 1) * ‖g u‖
  have hB : 0 ≤ B := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (Real.rpow_nonneg hu.le _) (norm_nonneg _)
  have hp : A - s.re < -1 := by linarith
  have hpow : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (A - s.re))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (A - s.re)) :=
      Real.summable_nat_rpow.mpr hp
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hbase
  have hmajor : Summable (fun n : ℕ =>
      (C * B) * (((n + 1 : ℕ) : ℝ) ^ (A - s.re))) := hpow.mul_left (C * B)
  refine hmajor.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) ?_
  intro n
  rw [coefficientTerm_integral_norm_eq a g s n]
  change ‖a n‖ * ((((n + 1 : ℕ) : ℝ) ^ (-s.re)) * B) ≤
    (C * B) * (((n + 1 : ℕ) : ℝ) ^ (A - s.re))
  have hN : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hfactor : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ (-s.re)) * B :=
    mul_nonneg (Real.rpow_nonneg hN.le _) hB
  calc
    ‖a n‖ * ((((n + 1 : ℕ) : ℝ) ^ (-s.re)) * B)
        ≤ (C * (((n + 1 : ℕ) : ℝ) ^ A)) *
          ((((n + 1 : ℕ) : ℝ) ^ (-s.re)) * B) :=
      mul_le_mul_of_nonneg_right (ha n) hfactor
    _ = (C * (((n + 1 : ℕ) : ℝ) ^ A) *
          (((n + 1 : ℕ) : ℝ) ^ (-s.re))) * B := by ring
    _ = (C * B) * (((n + 1 : ℕ) : ℝ) ^ (A - s.re)) := by
      rw [show A - s.re = A + (-s.re) by ring, Real.rpow_add hN]
      ring

/-- Absolute summability of the coefficient-term Mellin norms constructs the global theta
Mellin integral in `L¹`; no separate convergence assumption on the global theta is needed. -/
theorem theta_mellinConvergent_of_summable_integral_norm
    (a : ℕ → ℂ) (g : ℝ → ℂ) {s : ℂ}
    (hg : MellinConvergent g s)
    (hnorm : Summable fun n : ℕ =>
      ∫ x : ℝ in Ioi 0,
        ‖(x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))‖) :
    MellinConvergent (theta a g) s := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℂ := fun n x =>
    (x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))
  have hFint : ∀ n, Integrable (F n) μ := by
    intro n
    change IntegrableOn (F n) (Ioi 0)
    simpa [F, MellinConvergent, smul_eq_mul] using
      (coefficientTerm_hasMellin a g hg n).1
  let fL1 : ℕ → Lp ℂ 1 μ := fun n => (hFint n).toL1 (F n)
  have hnormL1 : Summable fun n => ‖fL1 n‖ := by
    have heq : (fun n => ‖fL1 n‖) = fun n =>
        ∫ x : ℝ in Ioi 0,
          ‖(x : ℂ) ^ (s - 1) * (a n * g ((n + 1 : ℕ) * x))‖ := by
      funext n
      change ‖(hFint n).toL1 (F n)‖ = ∫ x, ‖F n x‖ ∂μ
      exact L1.norm_of_fun_eq_integral_norm (hFint n)
    rw [heq]
    exact hnorm
  have henorm : ∑' n, ‖fL1 n‖ₑ ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hnormL1
  have hcoeEach : ∀ᵐ x ∂μ, ∀ n, fL1 n x = F n x := by
    rw [ae_all_iff]
    intro n
    exact (hFint n).coeFn_toL1
  have hcoeSum : (fun x => (∑' n, fL1 n) x) =ᵐ[μ] fun x => ∑' n, F n x := by
    filter_upwards [Lp.coeFn_tsum henorm, hcoeEach] with x hxsum hxeach
    rw [hxsum]
    apply tsum_congr
    intro n
    exact hxeach n
  have hIntSum : Integrable (fun x => ∑' n, F n x) μ :=
    (L1.integrable_coeFn (∑' n, fL1 n)).congr hcoeSum
  rw [MellinConvergent]
  change Integrable (fun x : ℝ => (x : ℂ) ^ (s - 1) * theta a g x) μ
  refine hIntSum.congr (Filter.Eventually.of_forall fun x => ?_)
  simpa [F, theta] using
    (tsum_mul_left (f := fun n : ℕ => a n * g ((n + 1 : ℕ) * x))
      (a := (x : ℂ) ^ (s - 1)))

/-- Full E5 in the initial half-plane.  A polynomial coefficient bound and convergence of the
completion kernel's Mellin transform imply convergence of the assembled carrier theta and identify
its Mellin transform with the full Dirichlet readout times the completion factor. -/
theorem theta_hasMellin_of_polynomial
    (a : ℕ → ℂ) (g : ℝ → ℂ) (s : ℂ) (C A : ℝ)
    (hg : MellinConvergent g s)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * (((n + 1 : ℕ) : ℝ) ^ A))
    (hs : A + 1 < s.re) :
    HasMellin (theta a g) s (dirichlet a s * mellin g s) := by
  have hnorm := coefficientTerm_integral_norm_summable_of_polynomial a g s C A ha hs
  exact theta_hasMellin a g hg
    (theta_mellinConvergent_of_summable_integral_norm a g hg hnorm) hnorm

end CriticalLinePhasor.CarrierTheta

#print axioms CriticalLinePhasor.CarrierTheta.coefficientTerm_hasMellin
#print axioms CriticalLinePhasor.CarrierTheta.finiteTheta_hasMellin
#print axioms CriticalLinePhasor.CarrierTheta.theta_hasMellin
#print axioms CriticalLinePhasor.CarrierTheta.coefficientTerm_integral_norm_eq
#print axioms CriticalLinePhasor.CarrierTheta.coefficientTerm_integral_norm_summable_of_polynomial
#print axioms CriticalLinePhasor.CarrierTheta.theta_mellinConvergent_of_summable_integral_norm
#print axioms CriticalLinePhasor.CarrierTheta.theta_hasMellin_of_polynomial
