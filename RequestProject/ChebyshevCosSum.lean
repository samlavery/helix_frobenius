import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Chebyshev character as a cosine sum, and the single Sato--Tate line

The all-ranks Sato--Tate cancellation is carried by **one** harmonic.  This file compiles the
identity that shows it:

  **`U_r(cos θ) = ∑_{j=0}^{r} cos((r − 2j)·θ)`.**

Reading off the exponents, the sum pairs `+k` with `−k` and leaves a single unpaired `cos 0 = 1`
exactly when `r` is even, so

* `r` odd — `U_r(cos θ) = 2·∑_{l odd, l ≤ r} cos(lθ)`;
* `r` even — `U_r(cos θ) = 1 + 2·∑_{l even, l ≤ r} cos(lθ)`.

The Sato--Tate measure is `(1/π)(1 − cos 2θ)dθ` on `[0,π]`, whose cosine moments are `−1/2` at
`m = 2` and **zero at every other `m ≥ 1`**.  So each rank-`r` condition `avg U_r → 0` is a finite
integer combination of one nonzero line: `avg cos 2θ → −1/2`, `avg cos mθ → 0` otherwise.  That is
why `cancellation_iff_equidistribution` has no slack — there is only one mode to cancel, and every
rank sees it.

**`satoTate_moment_vanishes` below is NOT new.**  The vanishing of the Sato--Tate moment is already
compiled in this corpus as `chebyshev_U_angleMeasure_integral_zero`
(`CPSCharacterSatoTate3D.lean:89`), in measure form against `angleMeasure`.  What is kept here is a
second, independent derivation in interval-integral form: multiplying by `sin θ` turns the Chebyshev
character into `sin((r+1)θ)` (`U_real_cos`), so the statement becomes sine orthogonality on `[0,π]`
between frequencies `r+1` and `1` — distinct exactly when `r ≥ 1`.  It is retained as a cross-check
of the pre-existing theorem, not as a contribution.

The genuinely new content of this file is `chebyshevU_cos_eq_cosSum` alone.

**Scope.**  No claim is made about any arithmetic family; this is the target measure's own
harmonic content.
-/

open Polynomial.Chebyshev Finset

namespace CriticalLinePhasor.ThreeDConverse

/-- The cosine-sum expansion of the Chebyshev `U` character. -/
noncomputable def chebyshevCosSum (r : ℕ) (θ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), Real.cos (((r : ℝ) - 2 * (j : ℝ)) * θ)

private lemma two_cos_mul_cos (a θ : ℝ) :
    2 * Real.cos θ * Real.cos (a * θ)
      = Real.cos ((a + 1) * θ) + Real.cos ((a - 1) * θ) := by
  rw [add_mul, sub_mul, one_mul, Real.cos_add, Real.cos_sub]
  ring

/-- **The three-term recurrence, on the cosine side.** -/
private lemma chebyshevCosSum_rec (n : ℕ) (θ : ℝ) :
    chebyshevCosSum (n + 2) θ
      = 2 * Real.cos θ * chebyshevCosSum (n + 1) θ - chebyshevCosSum n θ := by
  have hmul : 2 * Real.cos θ * chebyshevCosSum (n + 1) θ
      = (∑ j ∈ Finset.range (n + 2),
            Real.cos ((((n : ℝ) + 1 - 2 * (j : ℝ)) + 1) * θ))
        + ∑ j ∈ Finset.range (n + 2),
            Real.cos ((((n : ℝ) + 1 - 2 * (j : ℝ)) - 1) * θ) := by
    rw [chebyshevCosSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    exact two_cos_mul_cos _ θ
  have hup : (∑ j ∈ Finset.range (n + 2),
        Real.cos ((((n : ℝ) + 1 - 2 * (j : ℝ)) + 1) * θ))
      = chebyshevCosSum (n + 2) θ
        - Real.cos (((n : ℝ) + 2 - 2 * ((n : ℝ) + 2)) * θ) := by
    have hsplit : chebyshevCosSum (n + 2) θ
        = (∑ j ∈ Finset.range (n + 2), Real.cos (((n : ℝ) + 2 - 2 * (j : ℝ)) * θ))
          + Real.cos (((n : ℝ) + 2 - 2 * ((n : ℝ) + 2)) * θ) := by
      rw [chebyshevCosSum, Finset.sum_range_succ]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by push_cast; ring_nf
      · push_cast; ring_nf
    rw [hsplit, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun j _ => by ring_nf
  have hdn : (∑ j ∈ Finset.range (n + 2),
        Real.cos ((((n : ℝ) + 1 - 2 * (j : ℝ)) - 1) * θ))
      = chebyshevCosSum n θ
        + Real.cos (((n : ℝ) - 2 * ((n : ℝ) + 1)) * θ) := by
    rw [Finset.sum_range_succ, chebyshevCosSum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by push_cast; ring_nf
    · push_cast; ring_nf
  rw [hmul, hup, hdn]
  have hsame : ((n : ℝ) + 2 - 2 * ((n : ℝ) + 2)) = ((n : ℝ) - 2 * ((n : ℝ) + 1)) := by ring
  rw [hsame]
  ring

/-- **The identity**: the Chebyshev `U` character is the balanced cosine sum. -/
theorem chebyshevU_cos_eq_cosSum (θ : ℝ) (r : ℕ) :
    (U ℝ (r : ℤ)).eval (Real.cos θ) = chebyshevCosSum r θ := by
  have key : ∀ n : ℕ,
      ((U ℝ (n : ℤ)).eval (Real.cos θ) = chebyshevCosSum n θ) ∧
      ((U ℝ ((n : ℤ) + 1)).eval (Real.cos θ) = chebyshevCosSum (n + 1) θ) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [chebyshevCosSum]
      · simp [chebyshevCosSum, Finset.sum_range_succ, U_one, two_mul]
    | succ m ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have hrec : (U ℝ ((m : ℤ) + 2)).eval (Real.cos θ)
          = 2 * Real.cos θ * (U ℝ ((m : ℤ) + 1)).eval (Real.cos θ)
            - (U ℝ (m : ℤ)).eval (Real.cos θ) := by
        rw [show ((m : ℤ) + 2) = (m : ℤ) + 1 + 1 by ring, U_add_one]
        simp
      have : (U ℝ ((m : ℤ) + 2)).eval (Real.cos θ) = chebyshevCosSum (m + 2) θ := by
        rw [hrec, ih.1, ih.2, chebyshevCosSum_rec]
      exact_mod_cast this
  exact (key r).1

/-! ## The moment: every rank-`r` character integrates to zero against Sato--Tate -/

/-- `∫_0^π cos(mθ) dθ = 0` for every nonzero integer `m`. -/
theorem integral_cos_int_mul (m : ℤ) (hm : m ≠ 0) :
    ∫ θ in (0:ℝ)..Real.pi, Real.cos ((m : ℝ) * θ) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm0]
  simp [Real.sin_int_mul_pi]

/-- Sine orthogonality on `[0,π]` at distinct integer frequencies. -/
theorem integral_sin_mul_sin_int {a b : ℤ} (hne : a ≠ b) (hsum : a + b ≠ 0) :
    ∫ θ in (0:ℝ)..Real.pi, Real.sin ((a : ℝ) * θ) * Real.sin ((b : ℝ) * θ) = 0 := by
  have hprod : ∀ θ : ℝ, Real.sin ((a : ℝ) * θ) * Real.sin ((b : ℝ) * θ)
      = (Real.cos (((a - b : ℤ) : ℝ) * θ) - Real.cos (((a + b : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  have hc : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => Real.cos (c * x))
      MeasureTheory.volume 0 Real.pi := fun c =>
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  simp only [hprod]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hc _) (hc _),
    integral_cos_int_mul _ (sub_ne_zero.mpr hne), integral_cos_int_mul _ hsum]
  norm_num

/-- **The Sato--Tate moment vanishes at every positive rank.**  The density is `sin²θ`; the
character is `U_r(cos θ)`; their product integrates to zero over `[0,π]` for every `r ≥ 1`. -/
theorem satoTate_moment_vanishes (r : ℕ) (hr : 1 ≤ r) :
    ∫ θ in (0:ℝ)..Real.pi, (U ℝ (r : ℤ)).eval (Real.cos θ) * Real.sin θ ^ 2 = 0 := by
  have hrw : ∀ θ : ℝ, (U ℝ (r : ℤ)).eval (Real.cos θ) * Real.sin θ ^ 2
      = Real.sin ((((r : ℤ) + 1 : ℤ) : ℝ) * θ) * Real.sin (((1 : ℤ) : ℝ) * θ) := by
    intro θ
    have h := U_real_cos (θ := θ) (n := (r : ℤ))
    push_cast at h ⊢
    rw [pow_two, ← mul_assoc, h]
    ring
  simp only [hrw]
  refine integral_sin_mul_sin_int ?_ ?_
  · omega
  · omega

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.chebyshevU_cos_eq_cosSum
#print axioms CriticalLinePhasor.ThreeDConverse.satoTate_moment_vanishes
