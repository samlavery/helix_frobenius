import RequestProject.MaassRadialDecay
import RequestProject.MaassTsumParseval

/-!
# Summability of the Maass Fourier--Whittaker coefficients

The brick that joins the two halves already on the shelf: `radialKernel_norm_le_exp` gives
exponential decay of the radial kernel, and any polynomial bound on the Hecke eigenvalues is then
crushed by it.  The result is exactly the hypothesis `tsum_cosine_parseval` consumes, so the
abstract Parseval identity becomes the Maass horizontal energy identity.

The polynomial growth of the eigenvalues is taken as an explicit hypothesis rather than derived:
`MaassEigenData.lam_bound` constrains the eigenvalues at *primes* only, and propagating that to all
`n` is the multiplicativity-plus-Hecke-recursion argument, a separate matter from the analysis done
here.  Stating it as a hypothesis keeps the analytic content honest and separable.
-/

open Real Filter Topology

namespace CriticalLinePhasor.ThreeDConverse

/-- Geometric decay beats polynomial growth, in the shifted indexing the Fourier--Whittaker
expansion uses. -/
theorem summable_shifted_pow_mul_geometric {r : ℝ} (hr0 : 0 < r) (hr : r < 1) (A : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
  have h1 : Summable fun m : ℕ => ((m : ℝ)) ^ A * r ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one A hnorm
  have hinj : Function.Injective (fun n : ℕ => n + 1) := add_left_injective 1
  have h2 := (h1.comp_injective hinj).mul_left r⁻¹
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply]
  push_cast
  field_simp
  ring

/-- **The Fourier--Whittaker series converges absolutely.**  Past an explicit height, exponential
decay of the radial kernel dominates any polynomial bound on the eigenvalues. -/
theorem summable_maass_coeff_kernel (M : GenuineMaassCuspForm3D) {A : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hpoly : ∀ n : ℕ, ‖M.eigenData.lam (n + 1)‖ ≤ C * ((n : ℝ) + 1) ^ A) :
    ∃ y₀ : ℝ, 1 ≤ y₀ ∧ ∀ y : ℝ, y₀ ≤ y →
      Summable fun n : ℕ =>
        ‖M.eigenData.lam (n + 1) * M.radialKernel (((n : ℝ) + 1) * y)‖ := by
  obtain ⟨y₀, hy₀, hdecay⟩ := radialKernel_norm_le_exp M
  refine ⟨y₀, hy₀, fun y hy => ?_⟩
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le one_pos (le_trans hy₀ hy)
  set r : ℝ := Real.exp (-(2 * Real.pi * y)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hrdef]
    apply Real.exp_lt_one_iff.mpr
    have : (0 : ℝ) < 2 * Real.pi * y := by positivity
    linarith
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_shifted_pow_mul_geometric hr0 hr1 A).mul_left C)
  -- pointwise bound
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hge : y₀ ≤ ((n : ℝ) + 1) * y := by
    calc y₀ ≤ y := hy
      _ = 1 * y := (one_mul y).symm
      _ ≤ ((n : ℝ) + 1) * y := by
        apply mul_le_mul_of_nonneg_right hn1 (le_of_lt hypos)
  have hk := hdecay _ hge
  have hexp : Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) * y))) = r ^ (n + 1) := by
    rw [hrdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [norm_mul]
  calc ‖M.eigenData.lam (n + 1)‖ * ‖M.radialKernel (((n : ℝ) + 1) * y)‖
      ≤ (C * ((n : ℝ) + 1) ^ A) * Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) * y))) := by
        apply mul_le_mul (hpoly n) hk (norm_nonneg _)
        positivity
    _ = (C * ((n : ℝ) + 1) ^ A) * r ^ (n + 1) := by rw [hexp]
    _ ≤ C * (((n : ℝ) + 1) ^ A * r ^ n) := by
        rw [pow_succ]
        have hrle : r ^ n * r ≤ r ^ n := by
          nlinarith [pow_nonneg (le_of_lt hr0) n, hr1, hr0]
        have hnn : (0 : ℝ) ≤ C * ((n : ℝ) + 1) ^ A := by positivity
        nlinarith [hrle, hnn]

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.summable_shifted_pow_mul_geometric
#print axioms CriticalLinePhasor.ThreeDConverse.summable_maass_coeff_kernel
