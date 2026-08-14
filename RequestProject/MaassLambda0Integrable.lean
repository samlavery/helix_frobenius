import RequestProject.MaassPairingPoleSplit

/-!
# Integrability of the Maass entire part at a fixed exponent

Discharging the one named hypothesis of `maass_pairing_pole_split`.

`rs_entirePart_differentiable` dominates `‖P·Λ₀_z(s)‖` uniformly for `s` in a ball, and the
dominating function it uses is **`s`-free** — it depends only on the decay constant, the height,
and an integer `N` chosen large enough that `lambda0_bound_on_fd` applies.  So the same bound gives
integrability at any single fixed `s`, once `N` is chosen for that `s` rather than for a ball.

The dominating function's own integrability over `𝒟` never mentions the cusp form at all, so that
part is lifted verbatim; the two form-dependent inputs are `maassP_exp_decay_on_fd` and
`maassP_nonneg`, both already proved.

**Provenance.**  The `hbound_int` block is copied unchanged from `RSEntireHolo`; only the
surrounding statement and the two form inputs differ.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Set Filter Asymptotics
open scoped Real Topology MatrixGroups

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.EpsteinTheta CriticalLinePhasor.HeckeSupBound
open CriticalLinePhasor.ThreeDConverse

/-- **The Maass entire part is integrable over `𝒟` at every fixed exponent.** -/
theorem maassP_lambda0_integrableOn_fd (M : GenuineMaassCuspForm3D) (s : ℂ) :
    IntegrableOn (fun z : ℍ => ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s)
      ModularGroup.fd volume := by
  obtain ⟨C, hC0, hC⟩ := maassP_exp_decay_on_fd M
  obtain ⟨Nnat, hN1, hNa, hNb⟩ :
      ∃ n : ℕ, 1 ≤ n ∧ s.re ≤ (n : ℝ) ∧ (1 - s).re ≤ (n : ℝ) := by
    refine ⟨⌈s.re⌉₊ + ⌈(1 - s).re⌉₊ + 1, by omega, ?_, ?_⟩
    · push_cast
      linarith [Nat.le_ceil s.re, Nat.cast_nonneg (α := ℝ) ⌈(1 - s).re⌉₊]
    · push_cast
      linarith [Nat.le_ceil ((1 - s).re), Nat.cast_nonneg (α := ℝ) ⌈s.re⌉₊]
  set N : ℝ := (Nnat : ℝ) with hN
  have hNpos : (0 : ℝ) < N := by rw [hN]; exact_mod_cast Nat.lt_of_lt_of_le zero_lt_one hN1
  set bound : ℍ → ℝ := fun z =>
    (C * Real.exp (-(2 * π) * z.im)) * (lambdaC N * ((1 + z.im ^ 2) * z.im ^ N)) with hbound
  have hbound_int : IntegrableOn bound ModularGroup.fd volume := by
    have him : Continuous (fun z : ℍ => z.im) := UpperHalfPlane.continuous_im
    have hcont : Continuous bound := by
      rw [hbound]
      have hrpow : Continuous (fun z : ℍ => z.im ^ N) :=
        him.rpow_const (fun z => Or.inl z.im_ne_zero)
      have hexp : Continuous (fun z : ℍ => Real.exp (-(2 * π) * z.im)) :=
        Real.continuous_exp.comp (continuous_const.mul him)
      exact (continuous_const.mul hexp).mul
        (continuous_const.mul ((continuous_const.add (him.pow 2)).mul hrpow))
    refine integrableOn_fd_of_bounded hcont
      (C := C * lambdaC N * (3 * (Nnat.factorial : ℝ))) (fun z _ => ?_)
    have hy : 0 < z.im := z.im_pos
    have hy0 : 0 ≤ z.im := hy.le
    have hbnn : 0 ≤ bound z :=
      mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le)
        (mul_nonneg (lambdaC_nonneg hNpos)
          (mul_nonneg (by positivity) (Real.rpow_nonneg hy0 N)))
    rw [Real.norm_of_nonneg hbnn]
    show (C * Real.exp (-(2 * π) * z.im)) * (lambdaC N * ((1 + z.im ^ 2) * z.im ^ N))
        ≤ C * lambdaC N * (3 * (Nnat.factorial : ℝ))
    have hyN : z.im ^ N = z.im ^ Nnat := by rw [hN, Real.rpow_natCast]
    rw [hyN]
    set y := z.im with hy_def
    have e1 : (1 + y ^ 2) ≤ 3 * Real.exp y := by
      have h2 := pow_le_factorial_mul_exp hy0 2
      have h1 : (1 : ℝ) ≤ Real.exp y := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hy0
      have hfac2 : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [hfac2] at h2
      nlinarith [Real.exp_pos y]
    have e2 : y ^ Nnat ≤ (Nnat.factorial : ℝ) * Real.exp y := pow_le_factorial_mul_exp hy0 Nnat
    have hexp1 : Real.exp y * Real.exp y * Real.exp (-(2 * π) * y) ≤ 1 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, hy])
    have step : (1 + y ^ 2) * y ^ Nnat ≤ (3 * Real.exp y) * ((Nnat.factorial : ℝ) * Real.exp y) :=
      mul_le_mul e1 e2 (by positivity) (by positivity)
    calc (C * Real.exp (-(2 * π) * y)) * (lambdaC N * ((1 + y ^ 2) * y ^ Nnat))
        = C * lambdaC N * ((1 + y ^ 2) * y ^ Nnat * Real.exp (-(2 * π) * y)) := by ring
      _ ≤ C * lambdaC N *
            ((3 * Real.exp y) * ((Nnat.factorial : ℝ) * Real.exp y) * Real.exp (-(2 * π) * y)) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (lambdaC_nonneg hNpos))
          exact mul_le_mul_of_nonneg_right step (Real.exp_pos _).le
      _ = C * lambdaC N *
            (3 * (Nnat.factorial : ℝ) * (Real.exp y * Real.exp y * Real.exp (-(2 * π) * y))) := by
          ring
      _ ≤ C * lambdaC N * (3 * (Nnat.factorial : ℝ) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 (lambdaC_nonneg hNpos))
          exact mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = C * lambdaC N * (3 * (Nnat.factorial : ℝ)) := by ring
  refine Integrable.mono' hbound_int ?_ ?_
  · exact (Complex.continuous_ofReal.comp
      (continuous_maassP M)).aestronglyMeasurable.mul
      ((aestronglyMeasurable_Lambda0 s).restrict)
  · filter_upwards [ae_restrict_mem measurableSet_fd] with z hz
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (maassP_nonneg M z)]
    exact mul_le_mul (hC z hz) (lambda0_bound_on_fd hz hNpos hNa hNb) (norm_nonneg _)
      (mul_nonneg hC0 (Real.exp_pos _).le)

/-- **The Eisenstein pairing's pole split, unconditional.**  The named hypothesis of
`maass_pairing_pole_split` is discharged: the pairing is an entire function minus two explicit
simple poles whose residue coefficient is the Petersson norm, which `maassPetersson_pos` shows is
nonzero. -/
theorem maass_pairing_pole_split_unconditional (M : GenuineMaassCuspForm3D) (s : ℂ) :
    (∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ s ∂(volume : Measure ℍ)) =
      (∫ z in ModularGroup.fd,
        ((maassP M z : ℝ) : ℂ) * (generalFEPair z).Λ₀ s ∂(volume : Measure ℍ))
        - (1 / s + 1 / (1 - s)) * ((maassPetersson M : ℝ) : ℂ) :=
  maass_pairing_pole_split M s (maassP_lambda0_integrableOn_fd M s)

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.maassP_lambda0_integrableOn_fd
#print axioms CriticalLinePhasor.Unfolding.maass_pairing_pole_split_unconditional
