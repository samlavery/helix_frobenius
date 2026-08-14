import RequestProject.MaassStripIntegrable
import RequestProject.MaassHorizontalEnergy
import RequestProject.MaassTsumParseval
import RequestProject.MaassMellinSubstitution

/-!
# The archimedean factor of a Maass form converges on `Re s > 1`

The Rankin--Selberg series is `∑ₙ |λₙ|²n^{-s}` against a single archimedean integral
`A(s) = ∫₀^∞ ‖K(t)‖² t^{s-1} dt`, so evaluating the strip side needs `A(s)` to converge.

The cusp end is immediate from the kernel's decay.  The **boundary** end is the real question:
`GenuineMaassCuspForm3D` pins the kernel by the Bessel equation, decay, and the leading asymptotic
at infinity, and says *nothing* about `y → 0`.  Classically `K_{ir}(2πy)` is bounded there, but that
is a Frobenius analysis of the ODE, not something the structure hands over.

It is not needed.  The bound comes from the **global** geometry instead:

* `radialKernel_norm_le_exp_of_pos` removes the height gate from `summable_maass_coeff_kernel`, so
  Parseval holds at **every** height (`maass_horizontal_energy_of_pos`) with no hypothesis;
* the `n = 0` term of that identity is `‖K(y)‖²` on the nose, because `lam 1 = 1`;
* and the whole left side is at most the global bound `maassP_bounded`.

Hence `‖K(y)‖² ≤ 2C/y` — the boundary behaviour of the Bessel kernel *derived* from the modularity
of the wave rather than assumed of the special function.  Feeding `b = 1` to Mathlib's Mellin
criterion gives convergence exactly on `Re s > 1`, the same half-plane as the unfolding.

**Scope.**  This is the `r = 2` rung.  Sato--Tate needs every rank; this is not a route to it.
-/

open MeasureTheory Complex UpperHalfPlane Filter Asymptotics
open scoped Real Topology

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.Unfolding

/-- **Fourier--Whittaker summability at every positive height**, with no gate.  The gated version
`summable_maass_coeff_kernel` needed the normalization height; the compact-window kernel bound
removes it. -/
theorem summable_maass_coeff_kernel_of_pos (M : GenuineMaassCuspForm3D) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ =>
      ‖M.eigenData.lam (n + 1) * M.radialKernel (((n : ℝ) + 1) * y)‖ := by
  obtain ⟨C, hC1, hC⟩ := radialKernel_norm_le_exp_of_pos M hy
  set A : ℕ := M.eigenData.E₀ + 2 with hA
  set r : ℝ := Real.exp (-(2 * Real.pi * y)) with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hrlt : r < 1 := by
    rw [hr]
    apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.pi_pos]
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (((summable_shifted_pow_mul_geometric hrpos hrlt A).mul_left C).mul_right r)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hge : y ≤ ((n : ℝ) + 1) * y := by
    calc y = 1 * y := (one_mul y).symm
      _ ≤ ((n : ℝ) + 1) * y := mul_le_mul_of_nonneg_right hn1 hy.le
  have hexp : Real.exp (-(2 * Real.pi * (((n : ℝ) + 1) * y))) = r ^ (n + 1) := by
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hk : ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ≤ C * r ^ (n + 1) := by
    rw [← hexp]; exact hC _ hge
  have hlam : ‖M.eigenData.lam (n + 1)‖ ≤ ((n : ℝ) + 1) ^ A := by
    have h := lam_norm_le M.eigenData (n + 1) (by omega)
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rwa [hcast] at h
  rw [norm_mul]
  calc ‖M.eigenData.lam (n + 1)‖ * ‖M.radialKernel (((n : ℝ) + 1) * y)‖
      ≤ ((n : ℝ) + 1) ^ A * (C * r ^ (n + 1)) :=
        mul_le_mul hlam hk (norm_nonneg _) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ A * r ^ n) * r := by rw [pow_succ]; ring

/-- **Parseval for a Maass form at every height, unconditional.** -/
theorem maass_horizontal_energy_of_pos (M : GenuineMaassCuspForm3D) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0:ℝ)..1, ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2) =
      y / 2 * ∑' n : ℕ,
        ‖M.eigenData.lam (n + 1)‖ ^ 2 * ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 :=
  maass_horizontal_energy M hy (summable_maass_coeff_kernel_of_pos M hy)

/-- The horizontal slice of the wave is continuous — straight from `wave_smooth`, with no need to
build a continuous map into `ℍ`. -/
lemma continuous_maassWave_slice (M : GenuineMaassCuspForm3D) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2 := by
  have hc : ContinuousOn (Function.uncurry (maassWaveCoordinates M.eigenData M.radialKernel))
      (Set.univ ×ˢ Set.Ioi (0:ℝ)) := (M.wave_smooth 0).continuousOn
  have hg : Continuous fun x : ℝ => ((x, y) : ℝ × ℝ) := by fun_prop
  have hmaps : ∀ x : ℝ, ((x, y) : ℝ × ℝ) ∈ Set.univ ×ˢ Set.Ioi (0:ℝ) :=
    fun _ => ⟨Set.mem_univ _, hy⟩
  exact (hc.comp_continuous hg hmaps).norm.pow 2

/-- The global bound on the wave, read in coordinates. -/
lemma maassWaveCoordinates_sq_le (M : GenuineMaassCuspForm3D) {Cb : ℝ}
    (hCb : ∀ z : ℍ, ‖maassWave M.eigenData M.radialKernel z‖ ^ 2 ≤ Cb)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2 ≤ Cb := by
  have him : (0 : ℝ) < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  have hb := hCb ⟨(x : ℂ) + y * Complex.I, him⟩
  rwa [maassWave_eq_coords,
    show ((⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ) : ℂ).re = x by simp,
    show (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y by simp [UpperHalfPlane.im]] at hb

/-- **The boundary behaviour of the radial kernel, derived.**  The `n = 0` Fourier mode is
`‖K(y)‖²` exactly (`lam 1 = 1`), and Parseval bounds it by the global bound on the wave. -/
theorem radialKernel_sq_le_div (M : GenuineMaassCuspForm3D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → ‖M.radialKernel y‖ ^ 2 ≤ C / y := by
  obtain ⟨Cb, hCb0, hCb⟩ := maassP_bounded M
  refine ⟨2 * Cb, by linarith, fun y hy => ?_⟩
  -- upper bound: the energy sits under the global bound on a window of length one
  have hptw : ∀ x ∈ Set.Icc (0:ℝ) 1,
      ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2 ≤ Cb := fun x _ =>
    maassWaveCoordinates_sq_le M hCb x hy
  have hup : (∫ x in (0:ℝ)..1,
      ‖maassWaveCoordinates M.eigenData M.radialKernel x y‖ ^ 2) ≤ Cb := by
    have hmono := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) zero_le_one
      ((continuous_maassWave_slice M hy).intervalIntegrable 0 1)
      (intervalIntegrable_const (μ := volume) (c := Cb)) hptw
    simpa using hmono
  -- lower bound: the zeroth Fourier mode
  have hsum2 : Summable fun n : ℕ =>
      ‖M.eigenData.lam (n + 1)‖ ^ 2 * ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 := by
    have h := CriticalLinePhasor.MaassParseval.summable_sq_of_summable_norm
      (summable_maass_coeff_kernel_of_pos M hy)
    refine h.congr fun n => ?_
    rw [norm_mul, mul_pow]
  have hzero : ‖M.radialKernel y‖ ^ 2 ≤
      ∑' n : ℕ, ‖M.eigenData.lam (n + 1)‖ ^ 2 * ‖M.radialKernel (((n : ℝ) + 1) * y)‖ ^ 2 := by
    have hterm := hsum2.le_tsum 0 (fun m _ => by positivity)
    have hone : ‖M.eigenData.lam (0 + 1)‖ ^ 2 = 1 := by
      rw [show (0 + 1 : ℕ) = 1 from rfl, M.eigenData.one]
      norm_num
    rw [hone] at hterm
    simpa using hterm
  rw [maass_horizontal_energy_of_pos M hy] at hup
  have hhalf : y / 2 * ‖M.radialKernel y‖ ^ 2 ≤ Cb :=
    le_trans (mul_le_mul_of_nonneg_left hzero (by positivity)) hup
  rw [le_div_iff₀ hy]
  nlinarith

/-- **Mellin convergence of the archimedean factor on `Re s > 1`.**  The boundary exponent `b = 1`
is exactly the derived bound `‖K(t)‖² ≤ C/t`, so the half-plane matches the unfolding's. -/
theorem archimedeanFactor_mellinConvergent (M : GenuineMaassCuspForm3D) {s : ℂ}
    (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ => ((‖M.radialKernel t‖ ^ 2 : ℝ) : ℂ)) s := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := radialKernel_sq_le_div M
  obtain ⟨C₁, hC₁1, hC₁⟩ := radialKernel_norm_le_exp_of_pos M (a := 1) one_pos
  have hKcont : ContinuousOn M.radialKernel (Set.Ioi (0:ℝ)) := (M.radial_smooth 0).continuousOn
  have hpi : (0:ℝ) < 4 * Real.pi := by positivity
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := (1:ℝ)) ?_ ?_ (by linarith) ?_ hs
  · exact ((Complex.continuous_ofReal.comp_continuousOn
      (hKcont.norm.pow 2))).locallyIntegrableOn measurableSet_Ioi
  · -- cusp end: exponentially small
    have hOexp : (fun t : ℝ => ((‖M.radialKernel t‖ ^ 2 : ℝ) : ℂ)) =O[atTop]
        (fun t : ℝ => Real.exp (-(4 * Real.pi) * t)) := by
      rw [isBigO_iff]
      refine ⟨C₁ ^ 2, ?_⟩
      filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      have hb := hC₁ t ht
      have hsq : ‖M.radialKernel t‖ ^ 2 ≤ (C₁ * Real.exp (-(2 * Real.pi * t))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
      refine le_trans hsq (le_of_eq ?_)
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    exact hOexp.trans
      (CriticalLinePhasor.EpsteinTheta.exp_neg_isBigO_rpow hpi (-(s.re + 1)))
  · -- boundary end: the derived `C/t` bound
    rw [isBigO_iff]
    refine ⟨C₀, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0:ℝ) < t := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), Real.rpow_neg_one]
    rw [← div_eq_mul_inv]
    exact hC₀ t ht0

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.summable_maass_coeff_kernel_of_pos
#print axioms CriticalLinePhasor.ThreeDConverse.maass_horizontal_energy_of_pos
#print axioms CriticalLinePhasor.ThreeDConverse.radialKernel_sq_le_div
#print axioms CriticalLinePhasor.ThreeDConverse.archimedeanFactor_mellinConvergent
