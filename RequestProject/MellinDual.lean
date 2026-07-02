import Mathlib

/-!
# The readout is self-dual: Fourier-inverting the fiber recovers the carrier's sites

Answer to the "are we working in 4D?" question, as a theorem.  The fiber readout
`F(y) = ∑_{n} aₙ · exp(−i·hₙ·y)` (site `n` at log-height `hₙ = ln zₙ`, arrow `aₙ`) is itself a
Fourier/Mellin pairing between the 1-D readout line (ordinate `y`) and the carrier's
**log-height axis**.  The spectroscopy of this session Fourier-transforms the readout back;
the conjugate variable `ω` is therefore **not a new dimension — it is the carrier's height
axis in log coordinates**, and the spectral lines land exactly at the sites: the Bohr mean

    (1/T) · ∫₀ᵀ F(y) · exp(i·ω·y) dy   ⟶   (the arrow at the site with log-height ω)

as `T → ∞`, and `0` if no site sits at `ω`.  This is `readout_dual_recovers_sites` below —
the unconditional statement behind the measured Satake tables (the medium's lines at
`ω = ln p^k` ARE the arrows at the prime-power sites, recovered by inversion).  The model is
self-dual across the projection: project 3-D → 1-D by `y = log z`, un-project by the Bohr
mean, land back on the carrier.  Zeros are events in `y`; primes are lines in `ω`; the
explicit formula is this same pairing read in both directions.

(The other genuine fourth coordinate is `σ` in `s = σ + iy`, frozen at `1/2` by scale
balance — `scaleBalanced_iff` — which is why the strip machinery is a 1-D-only device.)

Mathlib-only; no `sorry`, no `axiom`; nothing about zero locations.
-/

open Complex Filter Topology intervalIntegral

namespace CriticalLinePhasor.MellinDual

/-- **Character orthogonality in the Bohr mean**: for a nonzero real frequency `c`, the mean
`(1/T)·∫₀ᵀ exp(i·c·y) dy` tends to `0`. -/
theorem char_mean_zero {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ y in (0:ℝ)..T, Complex.exp (Complex.I * c * y))
      atTop (𝓝 0) := by
  have hIc : (Complex.I * c) ≠ 0 := by
    simp [Complex.ext_iff, hc]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖(T : ℂ)⁻¹ * ∫ y in (0:ℝ)..T, Complex.exp (Complex.I * c * y)‖ ≤ 2 / (|c| * T) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hint : (∫ y in (0:ℝ)..T, Complex.exp (Complex.I * c * y))
        = (Complex.exp (Complex.I * c * T) - Complex.exp (Complex.I * c * 0)) / (Complex.I * c) := by
      simpa using integral_exp_mul_complex hIc (a := (0:ℝ)) (b := T)
    rw [hint, norm_mul, norm_div]
    have h1 : ‖Complex.exp (Complex.I * c * T) - Complex.exp (Complex.I * c * 0)‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      have hT2 : ‖Complex.exp (Complex.I * c * T)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      have h02 : ‖Complex.exp (Complex.I * c * 0)‖ = 1 := by
        simp
      rw [hT2, h02]
      norm_num
    have h2 : ‖(Complex.I * (c : ℂ))‖ = |c| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 : ‖((T : ℂ))⁻¹‖ = T⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    rw [h2, h3]
    calc T⁻¹ * (‖Complex.exp (Complex.I * c * T) - Complex.exp (Complex.I * c * 0)‖ / |c|)
        ≤ T⁻¹ * (2 / |c|) := by gcongr
      _ = 2 / (|c| * T) := by field_simp
  refine squeeze_zero_norm' (by simpa using hbound) ?_
  exact Tendsto.div_atTop tendsto_const_nhds
    (Tendsto.const_mul_atTop (by positivity) tendsto_id)

/-- The Bohr mean of the constant character (frequency `0`) is `1`. -/
theorem char_mean_one :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ y in (0:ℝ)..T, Complex.exp (Complex.I * (0:ℝ) * y))
      atTop (𝓝 1) := by
  have hev : (fun _ : ℝ => (1 : ℂ)) =ᶠ[atTop]
      fun T : ℝ => (T : ℂ)⁻¹ * ∫ y in (0:ℝ)..T, Complex.exp (Complex.I * (0:ℝ) * y) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have h0 : ∀ y : ℝ, Complex.exp (Complex.I * (0:ℝ) * y) = 1 := by
      intro y; simp
    rw [intervalIntegral.integral_congr (fun y _ => h0 y)]
    simp [inv_mul_cancel₀ (by exact_mod_cast hT.ne' : (T : ℂ) ≠ 0)]
  exact Tendsto.congr' hev tendsto_const_nhds

/-- **The readout is self-dual: Fourier inversion of the fiber recovers the carrier's
sites.**  For a finite bank with arrows `a n` at distinct log-heights `h n`, the Bohr mean of
`F(y)·exp(i·ω·y)` converges to the total arrow at log-height `ω` (the filtered sum; a single
arrow when the sites are distinct, `0` when no site sits at `ω`).  The spectral lines of the
ambient ARE the carrier's sites: the conjugate axis of the readout is the height axis. -/
theorem readout_dual_recovers_sites {ι : Type*} (s : Finset ι) (h : ι → ℝ) (a : ι → ℂ)
    (ω : ℝ) :
    Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ y in (0:ℝ)..T, (∑ n ∈ s, a n * Complex.exp (-(Complex.I * h n * y)))
          * Complex.exp (Complex.I * ω * y))
      atTop (𝓝 (∑ n ∈ s.filter (fun n => h n = ω), a n)) := by
  classical
  have hpt : ∀ (T : ℝ), (∫ y in (0:ℝ)..T,
      (∑ n ∈ s, a n * Complex.exp (-(Complex.I * h n * y))) * Complex.exp (Complex.I * ω * y))
      = ∑ n ∈ s, a n * ∫ y in (0:ℝ)..T, Complex.exp (Complex.I * (ω - h n) * y) := by
    intro T
    have hrw : ∀ y : ℝ,
        (∑ n ∈ s, a n * Complex.exp (-(Complex.I * h n * y))) * Complex.exp (Complex.I * ω * y)
        = ∑ n ∈ s, a n * Complex.exp (Complex.I * (ω - h n) * y) := by
      intro y
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    rw [intervalIntegral.integral_congr (fun y _ => hrw y)]
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun n _ => intervalIntegral.integral_const_mul _ _
    · intro n _
      exact (Continuous.const_mul (by fun_prop) (a n)).intervalIntegrable _ _
  have heq : ∀ T : ℝ, (T : ℂ)⁻¹ *
      (∫ y in (0:ℝ)..T,
        (∑ n ∈ s, a n * Complex.exp (-(Complex.I * h n * y))) * Complex.exp (Complex.I * ω * y))
      = ∑ n ∈ s, a n * ((T : ℂ)⁻¹ * ∫ y in (0:ℝ)..T, Complex.exp (Complex.I * (ω - h n) * y)) := by
    intro T
    rw [hpt T, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp only [heq]
  have hlim : ∀ n ∈ s, Tendsto
      (fun T : ℝ => a n * ((T : ℂ)⁻¹ * ∫ y in (0:ℝ)..T, Complex.exp (Complex.I * (ω - h n) * y)))
      atTop (𝓝 (if h n = ω then a n else 0)) := by
    intro n _
    by_cases hn : h n = ω
    · rw [if_pos hn, hn]
      have := (char_mean_one).const_mul (a n)
      simpa [sub_self] using this
    · rw [if_neg hn]
      have hc : ω - h n ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
      have := (char_mean_zero hc).const_mul (a n)
      simpa using this
  have := tendsto_finsetSum s hlim
  convert this using 2
  rw [Finset.sum_filter]

end CriticalLinePhasor.MellinDual
