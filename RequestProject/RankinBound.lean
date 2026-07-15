import RequestProject.ParsevalSecondMoment

/-!
# Rankin's smoothed second moment in coefficient form

The plumbing and the transfer.  The horizontal Fourier coefficients at height `y` are the
exponentially weighted `q`-coefficients (`fourierCoeffOn_eq_qExpansion_coeff`:
`c_n(y) = e^{-2πny}·a_n`, from the two integral formulas and the exponential algebra — the
`i² = -1` step is a one-line `linear_combination` against `Complex.I_sq`), so the Parseval
second moment becomes **Rankin's smoothed bound in coefficient form**
(`rankin_smoothed_bound`):

  `∑' n : ℕ, ‖a_n‖²·e^{-4πny} ≤ M·y^{-k}`,

for every level-one cusp form — from pure modularity, weight explicit.  This is the
second-moment input of the `r = 2` pair-dilation estimate, compiled end to end.  The remaining
arithmetic step to the classical `Sym²`-coefficient form is the Hecke relation
(`λ(n)² = ∑_{d|n} λ(n²/d²)`) — Hecke-operator theory, not present in Mathlib: classical,
formalizable, named.  No RH/GRH.
-/

open UpperHalfPlane Complex Filter MeasureTheory Matrix.SpecialLinearGroup Function
open scoped MatrixGroups Real

namespace CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- **The coefficient identification**: the `n`-th horizontal Fourier coefficient at height `y`
is the exponentially weighted `q`-expansion coefficient. -/
theorem fourierCoeffOn_eq_qExpansion_coeff (f : CuspForm 𝒮ℒ k) {y : ℝ} (hy : 0 < y) (n : ℕ) :
    fourierCoeffOn (zero_lt_one : (0:ℝ) < 1)
        (fun x : ℝ => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ)) (n : ℤ) =
      (Real.exp (-(2 * π * n * y)) : ℝ) * (qExpansion 1 f).coeff n := by
  set g : ℝ → ℂ := fun x => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) with hg
  have hfour := fourierCoeffOn_eq_integral g (n : ℤ) (zero_lt_one : (0:ℝ) < 1)
  have hcoeff := ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := f) one_pos
    one_mem_strictPeriods_SL n hy
  have hker : ∀ u : ℝ,
      (1 : ℂ) / Periodic.qParam 1 ((u : ℂ) + (y : ℂ) * Complex.I) ^ n * g u =
      ((Real.exp (2 * π * n * y) : ℝ) : ℂ) *
        (fourier (-(n : ℤ)) (u : AddCircle ((1:ℝ) - 0)) • g u) := by
    intro u
    rw [smul_eq_mul, ← mul_assoc]
    congr 1
    rw [fourier_coe_apply, Periodic.qParam, ← Complex.exp_nat_mul, one_div,
      ← Complex.exp_neg, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [sub_zero, div_one]
    linear_combination (-(2 * (π : ℂ) * (n : ℂ) * (y : ℂ))) * Complex.I_sq
  have hrel : (qExpansion 1 f).coeff n =
      ((Real.exp (2 * π * n * y) : ℝ) : ℂ) *
        fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g (n : ℤ) := by
    have hL : (qExpansion 1 f).coeff n =
        ∫ u in (0:ℝ)..1,
          (1:ℂ) / Periodic.qParam 1 ((u:ℂ) + (y:ℂ) * Complex.I) ^ n * g u := by
      rw [hcoeff]
      simp only [Complex.ofReal_one, div_one, one_mul]
      rfl
    have hR : fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g (n : ℤ) =
        ∫ u in (0:ℝ)..1, fourier (-(n : ℤ)) (u : AddCircle ((1:ℝ) - 0)) • g u := by
      rw [hfour]
      simp
    rw [hL, hR, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ => hker u
  rw [hrel, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    show -(2 * π * (n:ℝ) * y) + 2 * π * (n:ℝ) * y = 0 by ring,
    Real.exp_zero, Complex.ofReal_one, one_mul]

/-- **Rankin's smoothed second moment, coefficient form**: for every level-one cusp form,
`∑' n, ‖a_n‖²·e^{-4πny} ≤ M·y^{-k}` — from pure modularity, weight explicit. -/
theorem rankin_smoothed_bound (f : CuspForm 𝒮ℒ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, ∀ hy : 0 < y,
      ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) ≤
        M * y ^ (-k) := by
  obtain ⟨M, hM⟩ := hecke_pointwise f
  have hMnn : 0 ≤ M := hecke_pointwise_const_nonneg f hM
  refine ⟨M, hMnn, fun y hy => ?_⟩
  set g : ℝ → ℂ := fun x => f (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) with hg
  have hgc : Continuous g := horizontal_continuous f hy
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
  have hZsum : Summable fun i : ℤ =>
      ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g i‖ ^ 2 := hs.summable
  have hZbound : ∑' i : ℤ, ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g i‖ ^ 2 ≤
      M * y ^ (-k) := by
    rw [hs.tsum_eq]
    have hint : (∫ x in (0:ℝ)..1, ‖g x‖ ^ 2) ≤ M * y ^ (-k) := by
      calc (∫ x in (0:ℝ)..1, ‖g x‖ ^ 2) ≤ ∫ _x in (0:ℝ)..1, M * y ^ (-k) := by
            apply intervalIntegral.integral_mono_on zero_le_one
            · exact (hgc.norm.pow 2).intervalIntegrable 0 1
            · exact intervalIntegrable_const
            · intro x _
              exact hgb x
        _ = M * y ^ (-k) := by simp
    calc ((1:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..1, ‖g x‖ ^ 2
        = ∫ x in (0:ℝ)..1, ‖g x‖ ^ 2 := by norm_num
      _ ≤ M * y ^ (-k) := hint
  have hterm : ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) =
      ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g (n : ℤ)‖ ^ 2 := by
    intro n
    rw [fourierCoeffOn_eq_qExpansion_coeff f hy n, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, sq (Real.exp _), ← Real.exp_add,
      show -(2 * π * (n:ℝ) * y) + -(2 * π * (n:ℝ) * y) = -(4 * π * (n:ℝ) * y) by ring]
    ring
  calc ∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y))
      = ∑' n : ℕ, ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g (n : ℤ)‖ ^ 2 :=
        tsum_congr hterm
    _ ≤ ∑' i : ℤ, ‖fourierCoeffOn (zero_lt_one : (0:ℝ) < 1) g i‖ ^ 2 :=
        tsum_comp_le_tsum_of_inj hZsum (fun i => sq_nonneg _) Nat.cast_injective
    _ ≤ M * y ^ (-k) := hZbound

end CriticalLinePhasor.HeckeSupBound

#print axioms CriticalLinePhasor.HeckeSupBound.fourierCoeffOn_eq_qExpansion_coeff
#print axioms CriticalLinePhasor.HeckeSupBound.rankin_smoothed_bound
