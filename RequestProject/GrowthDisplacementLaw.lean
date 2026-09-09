import RequestProject.ClosedForm

/-!
# The growth-displacement law at an on-line zero (ledger 650–651)

The grown fiber `F_Z(s) = Σ (−1)^{n+1} w(n/Z) n^{−s}` has the DC `F_Z = η − Z^{−2} η(s−2) − …`, so its event
near a simple on-line zero `ρ` of `ζ` is displaced by `Z^{−2}·η(ρ−2)/η′(ρ)`.  This file compiles the exact
form of that direction.  The chain is the functional equation read at `3 − ρ`, the Schwarz reflection
`ζ(s̄) = ζ(s)‾`, the Gamma recurrence, and one fact about on-line zeros that needs neither Hardy's `Z`
nor the Riemann–Siegel `ϑ`:

* `deriv_zeta_online_reflect`: at an on-line zero, `ζ′(ρ) = −χ(ρ)·ζ′(ρ)‾`
  (differentiate `ζ(s) = χ(s) ζ(1−s)` at `ρ` and reflect);
* `chi_sub_two`: `χ(s−2) = −(1−s)(2−s)/(4π²) · χ(s)`;
* `growth_direction_core`: `ζ(ρ−2)·ζ′(ρ)‾ = (1−ρ)(2−ρ)/(4π²) · ζ(ρ+2)‾ · ζ′(ρ)`;
* `growth_direction_eta`: for a simple on-line zero,
  `η(ρ−2)/η′(ρ) = (1−2^{3−ρ})/(1−2^{1−ρ}) · (1−ρ)(2−ρ)/(4π²) · (ζ(ρ+2)/ζ′(ρ))‾`.

Here `χ(s) = 2(2π)^{s−1} Γ(1−s) cos(π(1−s)/2)` is Mathlib's functional-equation factor read at `1 − s`.
Numerically (att650d) the right side equals `i·A·e^{i(πS(γ⁺)+Φ)}` with `A > 0` and `|Φ| ≤ 1.086`; the
phase bound is elementary and is not compiled here.
-/

open Complex Real Filter Topology
open CriticalLinePhasor.EtaTrivial

namespace CriticalLinePhasor.GrowthDisplacement

/-- Derivative of `conj ∘ f ∘ conj`: an antiholomorphic reflection of a holomorphic function. -/
theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {f' z : ℂ} (h : HasDerivAt f f' z) :
    HasDerivAt (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) ((starRingEnd ℂ) f')
      ((starRingEnd ℂ) z) := by
  rw [hasDerivAt_iff_tendsto_slope] at h ⊢
  have hslope : slope (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) ((starRingEnd ℂ) z)
      = fun w => (starRingEnd ℂ) (slope f z ((starRingEnd ℂ) w)) := by
    funext w
    simp only [slope_def_field, map_div₀, map_sub, Complex.conj_conj]
  rw [hslope]
  have hconj : Tendsto (starRingEnd ℂ) (𝓝[≠] ((starRingEnd ℂ) z)) (𝓝[≠] z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := Complex.continuous_conj.tendsto ((starRingEnd ℂ) z)
      rw [Complex.conj_conj] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
      intro hwz
      apply hw
      rw [← hwz, Complex.conj_conj]
  exact (Complex.continuous_conj.tendsto f').comp (h.comp hconj)

/-- `ζ′(s̄) = ζ′(s)‾` away from the pole. -/
theorem deriv_zeta_conj {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    deriv riemannZeta ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (deriv riemannZeta ρ) := by
  have h := hasDerivAt_conj_conj (differentiableAt_riemannZeta hρ1).hasDerivAt
  have hfun : (fun w => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) w))) = riemannZeta := by
    funext w; rw [riemannZeta_conj, Complex.conj_conj]
  rw [hfun] at h
  exact h.deriv

/-- The functional-equation factor read at `1 − s`: `ζ s = χ s · ζ (1 − s)`. -/
noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * (π : ℂ)) ^ (s - 1) * Complex.Gamma (1 - s) * cos (π * (1 - s) / 2)

theorem two_pi_ne_zero : (2 * (π : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

theorem zeta_eq_chi_mul {s : ℂ} (hs : ∀ n : ℕ, (1 - s) ≠ -n) (hs' : s ≠ 0) :
    riemannZeta s = chi s * riemannZeta (1 - s) := by
  have h := riemannZeta_one_sub (s := 1 - s) hs (fun h1 => hs' (by linear_combination -h1))
  rw [show (1 : ℂ) - (1 - s) = s by ring, show -(1 - s) = s - 1 by ring] at h
  rw [h, chi]

/-- On the open strip, `ζ = χ · ζ(1 − ·)` holds identically. -/
theorem zeta_eventually_eq_chi {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    riemannZeta =ᶠ[𝓝 ρ] (fun s => chi s * riemannZeta (1 - s)) := by
  have hU : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hρU : ρ ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    show (0 : ℝ) < ρ.re ∧ ρ.re < 1
    rw [hρ]; norm_num
  filter_upwards [hU.mem_nhds hρU] with s hs
  refine zeta_eq_chi_mul (fun n h => ?_) (fun h => ?_)
  · have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
    linarith [hs.2, Nat.cast_nonneg (α := ℝ) n]
  · rw [h] at hs; simp at hs

theorem chi_differentiableAt {ρ : ℂ} (hρ : ρ.re = 1 / 2) : DifferentiableAt ℂ chi ρ := by
  unfold chi
  have h1 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) ρ :=
    (differentiableAt_const _).sub differentiableAt_id
  have hG : DifferentiableAt ℂ (fun s => Complex.Gamma (1 - s)) ρ := by
    refine (Complex.differentiableAt_Gamma (1 - ρ) (fun m h => ?_)).comp ρ h1
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re, hρ] at this
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hP : DifferentiableAt ℂ (fun s : ℂ => (2 * (π : ℂ)) ^ (s - 1)) ρ :=
    (differentiableAt_id.sub (differentiableAt_const _)).const_cpow (Or.inl two_pi_ne_zero)
  have hC : DifferentiableAt ℂ (fun s : ℂ => cos (π * (1 - s) / 2)) ρ := by
    apply Complex.differentiable_cos.differentiableAt.comp
    exact ((differentiableAt_const _).mul h1).div_const _
  exact (((differentiableAt_const _).mul hP).mul hG).mul hC

theorem one_sub_eq_conj {ρ : ℂ} (hρ : ρ.re = 1 / 2) : 1 - ρ = (starRingEnd ℂ) ρ := by
  apply Complex.ext <;> simp [hρ]; norm_num

theorem ne_one_of_re {ρ : ℂ} (hρ : ρ.re = 1 / 2) : ρ ≠ 1 := by
  intro h; rw [h] at hρ; norm_num at hρ

/-- Differentiating `ζ(s) = χ(s) ζ(1−s)` at an on-line zero. -/
theorem deriv_zeta_reflect {ρ : ℂ} (hρ : ρ.re = 1 / 2) (h0 : riemannZeta ρ = 0) :
    deriv riemannZeta ρ = -chi ρ * deriv riemannZeta (1 - ρ) := by
  have h1ρ : 1 - ρ ≠ 1 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, hρ] at this; norm_num at this
  have hz1 : HasDerivAt riemannZeta (deriv riemannZeta (1 - ρ)) (1 - ρ) :=
    (differentiableAt_riemannZeta h1ρ).hasDerivAt
  have hcomp : HasDerivAt (fun s => riemannZeta (1 - s)) (-(deriv riemannZeta (1 - ρ))) ρ := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) ρ := (hasDerivAt_id ρ).const_sub 1
    exact (hz1.comp ρ h1).congr_deriv (by ring)
  have hchi : HasDerivAt chi (deriv chi ρ) ρ := (chi_differentiableAt hρ).hasDerivAt
  have hζ : HasDerivAt riemannZeta
      (deriv chi ρ * riemannZeta (1 - ρ) + chi ρ * (-(deriv riemannZeta (1 - ρ)))) ρ :=
    (hchi.mul hcomp).congr_of_eventuallyEq (zeta_eventually_eq_chi hρ)
  have hz1ρ : riemannZeta (1 - ρ) = 0 := by
    rw [one_sub_eq_conj hρ, riemannZeta_conj, h0, map_zero]
  rw [hζ.deriv, hz1ρ]; ring

/-- **At an on-line zero, `ζ′(ρ) = −χ(ρ) · ζ′(ρ)‾`.**  No Hardy `Z`, no `ϑ`. -/
theorem deriv_zeta_online_reflect {ρ : ℂ} (hρ : ρ.re = 1 / 2) (h0 : riemannZeta ρ = 0) :
    deriv riemannZeta ρ = -chi ρ * (starRingEnd ℂ) (deriv riemannZeta ρ) := by
  have h := deriv_zeta_reflect hρ h0
  rw [one_sub_eq_conj hρ, deriv_zeta_conj (ne_one_of_re hρ)] at h
  exact h

/-- The Gamma-recurrence ratio: `χ(s−2) = −(1−s)(2−s)/(4π²) · χ(s)`. -/
theorem chi_sub_two {s : ℂ} (h1 : (1 : ℂ) - s ≠ 0) (h2 : (2 : ℂ) - s ≠ 0) :
    chi (s - 2) = -((1 - s) * (2 - s) / (4 * (π : ℂ) ^ 2)) * chi s := by
  unfold chi
  have hΓ : Gamma (1 - (s - 2)) = (2 - s) * (1 - s) * Gamma (1 - s) := by
    rw [show (1 : ℂ) - (s - 2) = (2 - s) + 1 by ring, Complex.Gamma_add_one _ h2,
      show (2 : ℂ) - s = (1 - s) + 1 by ring, Complex.Gamma_add_one _ h1]
    ring
  have hcos : cos ((π : ℂ) * (1 - (s - 2)) / 2) = -cos (π * (1 - s) / 2) := by
    rw [show (π : ℂ) * (1 - (s - 2)) / 2 = π * (1 - s) / 2 + π by ring, Complex.cos_add_pi]
  have hpow : (2 * (π : ℂ)) ^ (s - 2 - 1) = (2 * π) ^ (s - 1) / (2 * π) ^ (2 : ℂ) := by
    rw [← Complex.cpow_sub _ _ two_pi_ne_zero]; congr 1; ring
  rw [hΓ, hcos, hpow, Complex.cpow_two]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

theorem zeta_sub_two {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    riemannZeta (ρ - 2) = chi (ρ - 2) * riemannZeta (3 - ρ) := by
  have := zeta_eq_chi_mul (s := ρ - 2) (fun n h => ?_) (fun h => ?_)
  · rw [show (1 : ℂ) - (ρ - 2) = 3 - ρ by ring] at this; exact this
  · have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re, hρ] at this
    norm_num at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, hρ] at this
    norm_num at this

theorem three_sub_eq_conj_add_two {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    3 - ρ = (starRingEnd ℂ) (ρ + 2) := by
  apply Complex.ext <;> simp [hρ]; norm_num

/-- **The core identity.**  For an on-line zero `ρ` of `ζ`:
`ζ(ρ−2) · ζ′(ρ)‾ = (1−ρ)(2−ρ)/(4π²) · ζ(ρ+2)‾ · ζ′(ρ)`. -/
theorem growth_direction_core {ρ : ℂ} (hρ : ρ.re = 1 / 2) (h0 : riemannZeta ρ = 0) :
    riemannZeta (ρ - 2) * (starRingEnd ℂ) (deriv riemannZeta ρ)
      = ((1 - ρ) * (2 - ρ) / (4 * (π : ℂ) ^ 2)) * (starRingEnd ℂ) (riemannZeta (ρ + 2))
          * deriv riemannZeta ρ := by
  have h1 : (1 : ℂ) - ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re, hρ] at this; norm_num at this
  have h2 : (2 : ℂ) - ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, hρ] at this; norm_num at this
  have hS : riemannZeta (3 - ρ) = (starRingEnd ℂ) (riemannZeta (ρ + 2)) := by
    rw [three_sub_eq_conj_add_two hρ, riemannZeta_conj]
  rw [zeta_sub_two hρ, chi_sub_two h1 h2, hS]
  have hd := deriv_zeta_online_reflect hρ h0
  linear_combination
    (-((1 - ρ) * (2 - ρ) / (4 * (π : ℂ) ^ 2)) * (starRingEnd ℂ) (riemannZeta (ρ + 2))) * hd

/-- `η′(ρ) = (1 − 2^{1−ρ}) ζ′(ρ)` at a zero of `ζ`. -/
theorem deriv_etaTrivial_at_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (h0 : riemannZeta ρ = 0) :
    deriv etaTrivial ρ = (1 - (2 : ℂ) ^ (1 - ρ)) * deriv riemannZeta ρ := by
  have hz := (differentiableAt_riemannZeta hρ1).hasDerivAt
  have hp : HasDerivAt (fun s : ℂ => (1 : ℂ) - (2 : ℂ) ^ (1 - s))
      (-((2 : ℂ) ^ (1 - ρ) * Complex.log 2 * (-1))) ρ := by
    have := (((hasDerivAt_id ρ).const_sub (1 : ℂ)).const_cpow (c := (2 : ℂ))
      (Or.inl two_ne_zero)).const_sub (1 : ℂ)
    simpa using this
  have hη : HasDerivAt etaTrivial
      ((-((2 : ℂ) ^ (1 - ρ) * Complex.log 2 * (-1))) * riemannZeta ρ
        + (1 - (2 : ℂ) ^ (1 - ρ)) * deriv riemannZeta ρ) ρ := hp.mul hz
  rw [hη.deriv, h0]; ring

theorem one_sub_two_cpow_ne_zero {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    (1 : ℂ) - (2 : ℂ) ^ (1 - ρ) ≠ 0 := by
  intro h
  have h2 : (2 : ℂ) ^ (1 - ρ) = 1 := by linear_combination -h
  have hn := congrArg norm h2
  have : ‖((2 : ℝ) : ℂ) ^ (1 - ρ)‖ = (2 : ℝ) ^ (1 - ρ).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  simp only [Complex.ofReal_ofNat] at this
  rw [this, norm_one] at hn
  have hre : (1 - ρ).re = 1 / 2 := by simp [hρ]; norm_num
  rw [hre] at hn
  have : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.one_lt_rpow (by norm_num) (by norm_num)
  linarith

/-- **The growth-displacement direction at a simple on-line zero:**
`η(ρ−2)/η′(ρ) = (1−2^{3−ρ})/(1−2^{1−ρ}) · (1−ρ)(2−ρ)/(4π²) · (ζ(ρ+2)/ζ′(ρ))‾`. -/
theorem growth_direction_eta {ρ : ℂ} (hρ : ρ.re = 1 / 2) (h0 : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) :
    etaTrivial (ρ - 2) / deriv etaTrivial ρ
      = ((1 - (2 : ℂ) ^ (3 - ρ)) / (1 - (2 : ℂ) ^ (1 - ρ)))
          * ((1 - ρ) * (2 - ρ) / (4 * (π : ℂ) ^ 2))
          * (starRingEnd ℂ) (riemannZeta (ρ + 2) / deriv riemannZeta ρ) := by
  rw [deriv_etaTrivial_at_zero (ne_one_of_re hρ) h0]
  have hB := one_sub_two_cpow_ne_zero hρ
  have hc : (starRingEnd ℂ) (deriv riemannZeta ρ) ≠ 0 := by
    rwa [map_ne_zero]
  have hcore := growth_direction_core hρ h0
  rw [map_div₀]
  unfold etaTrivial
  rw [show (1 : ℂ) - (ρ - 2) = 3 - ρ by ring]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hζ2 : riemannZeta (ρ - 2)
      = ((1 - ρ) * (2 - ρ) / (4 * (π : ℂ) ^ 2)) * (starRingEnd ℂ) (riemannZeta (ρ + 2))
          * deriv riemannZeta ρ / (starRingEnd ℂ) (deriv riemannZeta ρ) := by
    rw [eq_div_iff hc]; exact hcore
  rw [hζ2]
  field_simp

end CriticalLinePhasor.GrowthDisplacement

#print axioms CriticalLinePhasor.GrowthDisplacement.deriv_zeta_online_reflect
#print axioms CriticalLinePhasor.GrowthDisplacement.growth_direction_core
#print axioms CriticalLinePhasor.GrowthDisplacement.growth_direction_eta
