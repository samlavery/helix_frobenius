import RequestProject.RankinMellin

/-!
# Exact Parseval: the horizontal energy readout equals the smoothed second moment

The holomorphy input.  The compiled Parseval bound (`rankin_smoothed_bound`) is an inequality
because it discards the negative Fourier modes; this file proves they vanish
(`fourierCoeffOn_neg_eq_zero`) — the bank is one-sided because the cusp form is holomorphic:
its `q`-expansion (`hasSum_qExpansion`) has only nonnegative frequencies, and each nonnegative
frequency is orthogonal to every negative one on the period interval
(`fourier_qPow_integral_eq_zero`, the `∫₀¹ e^{2πi(m-i)x} dx = 0` computation).  The exchange of
sum and integral is done at finite level plus a tail estimate: the partial sums integrate to
zero exactly, and the tail is controlled by the summable coefficient–`q` series
(`summable_coeff_qNorm`, from the compiled Hecke bound via `‖a‖ ≤ 1 + ‖a‖²`), whose tails tend
to zero.  Consequence (`rankin_energy_exact`): at every height,

  `∑' n, ‖a_n‖²·e^{-4πny}  =  ∫₀¹ ‖f(x+iy)‖² dx`  —  exactly,

so the smoothed second moment *is* the horizontal energy readout of the bank, not just a lower
part of it — the strip-side unfolding identity of the Rankin–Selberg integral.  No RH/GRH.
-/

open UpperHalfPlane Complex Filter MeasureTheory Function
open scoped MatrixGroups Real Topology

namespace CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- The fourier character on the unit period has unit norm. -/
lemma norm_fourier_one (i : ℤ) (x : ℝ) :
    ‖(fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ)‖ = 1 := by
  rw [fourier_coe_apply,
    show 2 * (π:ℂ) * Complex.I * ((-i : ℤ) : ℂ) * (x:ℂ) / (((1:ℝ) - 0 : ℝ) : ℂ) =
      ((2 * π * (-i : ℤ) * x / ((1:ℝ) - 0) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The fourier character is continuous as a function on the line. -/
lemma continuous_fourier_one (i : ℤ) :
    Continuous fun x : ℝ => (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) := by
  simp only [fourier_coe_apply]
  fun_prop

/-- The horizontal `q`-power is continuous. -/
lemma continuous_qPow (y : ℝ) (m : ℕ) :
    Continuous fun x : ℝ => Periodic.qParam 1 ((x : ℂ) + y * Complex.I) ^ m := by
  simp only [Periodic.qParam]
  fun_prop

/-- **Orthogonality**: each nonnegative bank frequency integrates to zero against every
distinct character over the period interval. -/
lemma fourier_qPow_integral_eq_zero (m : ℕ) {i : ℤ} (hi : i ≠ (m : ℤ)) (y : ℝ) :
    ∫ x in (0:ℝ)..1, (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) *
      Periodic.qParam 1 ((x : ℂ) + y * Complex.I) ^ m = 0 := by
  have hint : ∀ x : ℝ, (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) *
      Periodic.qParam 1 ((x : ℂ) + y * Complex.I) ^ m =
      Complex.exp (-(2 * π * m * y)) *
        Complex.exp ((2 * π * Complex.I * ((m : ℂ) - i)) * x) := by
    intro x
    rw [fourier_coe_apply, Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    simp only [sub_zero, div_one]
    linear_combination (2 * π * (m : ℂ) * (y : ℂ)) * Complex.I_sq
  have hc : (2 * π * Complex.I * ((m : ℂ) - i)) ≠ 0 := by
    have hmi : ((m : ℂ) - i) ≠ 0 := by
      rw [sub_ne_zero]
      exact_mod_cast (Ne.symm hi)
    have h2π : (2 * π * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact mul_ne_zero h2π hmi
  have hone : Complex.exp (2 * π * Complex.I * ((m : ℂ) - i) * 1) = 1 := by
    have h := Complex.exp_int_mul_two_pi_mul_I ((m : ℤ) - i)
    rw [show (((m : ℤ) - i : ℤ) : ℂ) * (2 * π * Complex.I) =
      2 * π * Complex.I * ((m : ℂ) - i) * 1 by push_cast; ring] at h
    exact h
  rw [intervalIntegral.integral_congr fun x _ => hint x,
    intervalIntegral.integral_const_mul, integral_exp_mul_complex hc,
    Complex.ofReal_one, Complex.ofReal_zero, hone, mul_zero, Complex.exp_zero,
    sub_self, zero_div, mul_zero]

/-- The coefficient–`q`-norm series is summable at every positive height, from the compiled
Hecke bound via `‖a‖ ≤ 1 + ‖a‖²`. -/
lemma summable_coeff_qNorm (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {y : ℝ} (hy : 0 < y) :
    Summable fun m : ℕ =>
      ‖(qExpansion 1 f).coeff m‖ * Real.exp (-2 * π * y) ^ m := by
  obtain ⟨M, hM0, hM⟩ := hecke_coeff_sq_bound f
  have hr : ‖Real.exp (-2 * π * y)‖ < 1 := by
    rw [Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_lt_one_iff.mpr
    have := Real.pi_pos
    nlinarith
  have hr' : Real.exp (-2 * π * y) < 1 := by
    rw [Real.norm_eq_abs, Real.abs_exp] at hr
    exact hr
  have hgeo1 : Summable fun m : ℕ => Real.exp (-2 * π * y) ^ m :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr'
  have hgeo2 : Summable fun m : ℕ =>
      (m : ℝ) ^ k.toNat * Real.exp (-2 * π * y) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one k.toNat hr
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    (hgeo1.add (hgeo2.mul_left M))
  have hself : ‖(qExpansion 1 f).coeff m‖ ≤ 1 + ‖(qExpansion 1 f).coeff m‖ ^ 2 := by
    nlinarith [sq_nonneg (‖(qExpansion 1 f).coeff m‖ - 1),
      norm_nonneg ((qExpansion 1 f).coeff m)]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [qExpansion_coeff_zero_cusp f]
    simp only [norm_zero, zero_mul]
    positivity
  · have hb := hM m hm
    have hzk : (m : ℝ) ^ k = (m : ℝ) ^ k.toNat := by
      conv_lhs => rw [← Int.toNat_of_nonneg hk]
      rw [zpow_natCast]
    calc ‖(qExpansion 1 f).coeff m‖ * Real.exp (-2 * π * y) ^ m
        ≤ (1 + M * (m : ℝ) ^ k) * Real.exp (-2 * π * y) ^ m := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans hself (by linarith)
      _ = Real.exp (-2 * π * y) ^ m +
          M * ((m : ℝ) ^ k.toNat * Real.exp (-2 * π * y) ^ m) := by
          rw [hzk]
          ring

/-- **The negative Fourier modes of a cusp form vanish**: holomorphy makes the bank
one-sided. -/
theorem fourierCoeffOn_neg_eq_zero (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {y : ℝ} (hy : 0 < y)
    {i : ℤ} (hi : i < 0) :
    fourierCoeffOn (zero_lt_one : (0:ℝ) < 1)
      (fun x : ℝ => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)) i = 0 := by
  set g : ℝ → ℂ := fun x => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) with hg
  have hgc : Continuous g := horizontal_continuous f hy
  set a : ℕ → ℂ := fun m => (qExpansion 1 f).coeff m with ha
  set q : ℝ → ℂ := fun x => Periodic.qParam 1 ((x : ℂ) + y * Complex.I) with hq
  set b : ℕ → ℝ := fun m => ‖a m‖ * Real.exp (-2 * π * y) ^ m with hb
  have hbsum : Summable b := summable_coeff_qNorm f hk hy
  have hqsum : ∀ x : ℝ, HasSum (fun m : ℕ => a m • q x ^ m) (g x) := fun x =>
    hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
      (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)
  have hqnorm : ∀ x : ℝ, ‖q x‖ = Real.exp (-2 * π * y) := by
    intro x
    rw [hq]
    rw [Periodic.norm_qParam]
    have him : ((x : ℂ) + y * Complex.I).im = y := by simp
    rw [him]
    norm_num
  have hfour := fourierCoeffOn_eq_integral g i (zero_lt_one : (0:ℝ) < 1)
  set I₀ : ℂ := ∫ x in (0:ℝ)..1,
    (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • g x with hI₀
  have key : ∀ N : ℕ, ‖I₀‖ ≤ ∑' m : ℕ, b (m + N) := by
    intro N
    set S1 : ℝ → ℂ := fun x => ∑ m ∈ Finset.range N, a m • q x ^ m with hS1
    have hS1c : Continuous S1 :=
      continuous_finsetSum _ fun m _ => (continuous_qPow y m).const_smul (a m)
    have hS2bound : ∀ x : ℝ, ‖g x - S1 x‖ ≤ ∑' m : ℕ, b (m + N) := by
      intro x
      have hsplit := (hqsum x).summable.sum_add_tsum_nat_add N
      rw [(hqsum x).tsum_eq] at hsplit
      have htermnorm : ∀ m : ℕ, ‖a (m + N) • q x ^ (m + N)‖ = b (m + N) := by
        intro m
        rw [norm_smul, norm_pow, hqnorm x, hb]
      have htails : Summable fun m : ℕ => ‖a (m + N) • q x ^ (m + N)‖ := by
        refine ((summable_nat_add_iff N).mpr hbsum).congr fun m => ?_
        rw [htermnorm m]
      have hgs : g x - S1 x = ∑' m : ℕ, a (m + N) • q x ^ (m + N) := by
        simp only [hS1]
        rw [← hsplit]
        ring
      rw [hgs]
      calc ‖∑' m : ℕ, a (m + N) • q x ^ (m + N)‖
          ≤ ∑' m : ℕ, ‖a (m + N) • q x ^ (m + N)‖ := norm_tsum_le_tsum_norm htails
        _ = ∑' m : ℕ, b (m + N) := tsum_congr htermnorm
    have hint1 : IntervalIntegrable
        (fun x => (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • S1 x) volume 0 1 :=
      ((continuous_fourier_one i).smul hS1c).intervalIntegrable 0 1
    have hint2 : IntervalIntegrable
        (fun x => (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • (g x - S1 x))
        volume 0 1 :=
      ((continuous_fourier_one i).smul (hgc.sub hS1c)).intervalIntegrable 0 1
    have hIsplit : I₀ =
        (∫ x in (0:ℝ)..1, (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • S1 x) +
        ∫ x in (0:ℝ)..1,
          (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • (g x - S1 x) := by
      rw [hI₀, ← intervalIntegral.integral_add hint1 hint2]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [smul_eq_mul]
      ring
    have hI1 : (∫ x in (0:ℝ)..1,
        (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • S1 x) = 0 := by
      have hpoint : ∀ x : ℝ, (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • S1 x =
          ∑ m ∈ Finset.range N,
            a m * ((fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) * q x ^ m) := by
        intro x
        simp only [hS1, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      rw [intervalIntegral.integral_congr fun x _ => hpoint x,
        intervalIntegral.integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro m _
        have hne : i ≠ (m : ℤ) := (lt_of_lt_of_le hi (Int.natCast_nonneg m)).ne
        have horth : ∫ x in (0:ℝ)..1,
            (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) * q x ^ m = 0 :=
          fourier_qPow_integral_eq_zero m hne y
        rw [intervalIntegral.integral_const_mul, horth, mul_zero]
      · intro m _
        exact (continuous_const.mul
          ((continuous_fourier_one i).mul (continuous_qPow y m))).intervalIntegrable 0 1
    have hI2 : ‖∫ x in (0:ℝ)..1,
        (fourier (-i) (x : AddCircle ((1:ℝ) - 0)) : ℂ) • (g x - S1 x)‖ ≤
        (∑' m : ℕ, b (m + N)) * |1 - (0:ℝ)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _
      rw [norm_smul, norm_fourier_one i x, one_mul]
      exact hS2bound x
    rw [hIsplit, hI1, zero_add]
    exact hI2.trans (le_of_eq (by norm_num))
  have htend : Tendsto (fun N : ℕ => ∑' m : ℕ, b (m + N)) atTop (𝓝 0) :=
    tendsto_sum_nat_add b
  have h0 : ‖I₀‖ ≤ 0 := ge_of_tendsto' htend key
  have hI0 : I₀ = 0 := norm_le_zero_iff.mp h0
  rw [hfour, hI0, smul_zero]

/-- **Exact Parseval — the strip-side unfolding identity**: the smoothed second moment IS the
horizontal energy readout of the bank, exactly, at every height. -/
theorem rankin_energy_exact (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {y : ℝ} (hy : 0 < y) :
    ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) =
      ∫ x in (0:ℝ)..1,
        ‖f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)‖ ^ 2 := by
  set g : ℝ → ℂ := fun x => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) with hg
  have hgc : Continuous g := horizontal_continuous f hy
  obtain ⟨M, hM⟩ := hecke_pointwise f
  have hgb : ∀ x : ℝ, ‖g x‖ ^ 2 ≤ M * y ^ (-k) := by
    intro x
    have h := hM (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)
    rw [Complex.normSq_eq_norm_sq] at h
    have himz : (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ).im = y := by
      simp [UpperHalfPlane.im]
    rwa [himz] at h
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    simp [Real.volume_Ioc]
  have hL2 : MemLp g 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    apply MemLp.of_bound hgc.aestronglyMeasurable (Real.sqrt (M * y ^ (-k)))
    apply Filter.Eventually.of_forall
    intro x
    calc ‖g x‖ = Real.sqrt (‖g x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (M * y ^ (-k)) := Real.sqrt_le_sqrt (hgb x)
  have hs := hasSum_sq_fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) hL2
  have hvanish : ∀ i : ℤ, i ∉ Set.range ((↑·) : ℕ → ℤ) →
      ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g i‖ ^ 2 = 0 := by
    intro i hir
    have hineg : i < 0 := by
      by_contra hpos
      push Not at hpos
      exact hir ⟨i.toNat, Int.toNat_of_nonneg hpos⟩
    have h0 : fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g i = 0 :=
      fourierCoeffOn_neg_eq_zero f hk hy hineg
    rw [h0, norm_zero]
    norm_num
  have hNat : HasSum (fun n : ℕ =>
      ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g (n : ℤ)‖ ^ 2)
      (((1:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..1, ‖g x‖ ^ 2) :=
    (Function.Injective.hasSum_iff Nat.cast_injective hvanish).mpr hs
  have hterm : ∀ n : ℕ, ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g (n : ℤ)‖ ^ 2 =
      ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) := by
    intro n
    rw [fourierCoeffOn_eq_qExpansion_coeff f hy n, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, sq (Real.exp _), ← Real.exp_add,
      show -(2 * π * (n:ℝ) * y) + -(2 * π * (n:ℝ) * y) = -(4 * π * (n:ℝ) * y) by ring]
    ring
  simp only [hterm] at hNat
  rw [hNat.tsum_eq]
  simp only [hg]
  norm_num

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.fourierCoeffOn_neg_eq_zero
#print axioms CriticalLinePhasor.HeckeSupBound.rankin_energy_exact
