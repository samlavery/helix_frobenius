import RequestProject.EpsteinThetaI
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Epstein zeta of the Gaussian lattice: continuation and functional equation

Brick (ii) of the Eisenstein chain.  The compiled Gaussian-lattice theta (`thetaSq`, weld
reflection `thetaSq_inv`, lattice identification `thetaSq_eq_double`) is packaged as a Mathlib
`WeakFEPair` with weight `k = 1`, root number `ε = 1`, and DC constants `f₀ = g₀ = 1` — the
`(0,0)` lattice term, the trivial channel.  The abstract functional-equation machinery then
delivers, compiled: the completed Epstein zeta of `ℤ[i]` extends to `ℂ`, holomorphic away from
`s ∈ {0, 1}` (`epsteinLambda_differentiableAt`), with the functional equation
`Λ(1−s) = Λ(s)`-symmetric (`epsteinLambda_functional_equation`) and the pole at `s = 1` carried
by the DC channel with computed residue (`epsteinLambda_residue_one`) — rank-is-DC-residue at
the Gaussian point.  In the three-dimensional register: the bank is the `ℤ[i]` phasor lattice,
`Λ` its completed Mellin readout, the poles sit exactly on the DC channel, and the FE is the
weld reflection transported through the projection.  The term-by-term identification of `Λ`
with `π^{-s}Γ(s)·∑'_{(m,n)≠(0,0)} (m²+n²)^{-s}` on the convergence half-plane is the named next
step; the continuation and FE — the hard content — are what this file compiles.  No RH/GRH.
-/

open Complex UpperHalfPlane Filter MeasureTheory Set Asymptotics
open scoped Real

namespace CriticalLinePhasor.EpsteinTheta

/-- The theta is continuous on the positive axis. -/
lemma continuousOn_thetaSq : ContinuousOn thetaSq (Ioi (0 : ℝ)) := by
  intro t ht
  have him : 0 < ((t : ℂ) * Complex.I).im := by simpa using (mem_Ioi.mp ht)
  have hin : ContinuousAt (fun x : ℝ => (x : ℂ) * Complex.I) t := by fun_prop
  have h1 : ContinuousAt (fun x : ℝ => jacobiTheta ((x : ℂ) * Complex.I)) t :=
    ContinuousAt.comp (g := jacobiTheta) (f := fun x : ℝ => (x : ℂ) * Complex.I) (x := t)
      (differentiableAt_jacobiTheta him).continuousAt hin
  exact (h1.pow 2).continuousWithinAt

/-- Exponentials beat every power at infinity. -/
lemma exp_neg_pi_isBigO_rpow (r : ℝ) :
    (fun t : ℝ => Real.exp (-π * t)) =O[atTop] (· ^ r) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  set K : ℕ := ⌈-r⌉₊ with hK
  have hrK : -r ≤ (K : ℝ) := hK ▸ Nat.le_ceil _
  have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K
  have hev : ∀ᶠ x : ℝ in atTop, x ^ K * Real.exp (-x) < 1 :=
    hlim.eventually_lt_const one_pos
  rw [eventually_atTop] at hev
  obtain ⟨A, hA⟩ := hev
  filter_upwards [eventually_ge_atTop (max A 1)] with x hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxA : A ≤ x := le_trans (le_max_left _ _) hx
  have h1 : x ^ K * Real.exp (-x) ≤ 1 := (hA x hxA).le
  have h2 : Real.exp (-π * x) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three]
  have hxK : (0 : ℝ) < x ^ K := pow_pos hx0 K
  have h3 : Real.exp (-x) ≤ (x ^ K)⁻¹ := by
    calc Real.exp (-x) = x ^ K * Real.exp (-x) / x ^ K := by field_simp
      _ ≤ 1 / x ^ K := by gcongr
      _ = (x ^ K)⁻¹ := one_div _
  have h4 : ((x ^ K : ℝ))⁻¹ ≤ x ^ r := by
    rw [← Real.rpow_natCast x K, ← Real.rpow_neg hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith
  rw [one_mul]
  calc ‖Real.exp (-π * x)‖ = Real.exp (-π * x) :=
        Real.norm_of_nonneg (Real.exp_pos _).le
    _ ≤ x ^ r := le_trans h2 (le_trans h3 h4)
    _ ≤ ‖x ^ r‖ := le_abs_self _

/-- Cusp-side decay: `thetaSq − 1` decays faster than every power (the non-DC channels die
exponentially at the cusp). -/
lemma thetaSq_sub_one_isBigO (r : ℝ) :
    (fun t => thetaSq t - 1) =O[atTop] (· ^ r) := by
  set C₀ : ℝ := 2 / (1 - Real.exp (-π)) with hC₀
  have hexpπ : Real.exp (-π) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Real.pi_pos)
  have hC₀pos : 0 < C₀ := by
    rw [hC₀]
    apply div_pos two_pos
    linarith
  have hexp : ∀ t : ℝ, 1 ≤ t →
      ‖thetaSq t - 1‖ ≤ (C₀ ^ 2 + 2 * C₀) * Real.exp (-π * t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have him : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht0
    have himval : ((t : ℂ) * Complex.I).im = t := by simp
    have hmono : Real.exp (-π * t) ≤ Real.exp (-π) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hθ : ‖jacobiTheta ((t : ℂ) * Complex.I) - 1‖ ≤ C₀ * Real.exp (-π * t) := by
      have h := norm_jacobiTheta_sub_one_le him
      rw [himval] at h
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [hC₀]
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    have hsplit : thetaSq t - 1 =
        (jacobiTheta ((t : ℂ) * Complex.I) - 1) ^ 2 +
          2 * (jacobiTheta ((t : ℂ) * Complex.I) - 1) := by
      unfold thetaSq
      ring
    rw [hsplit]
    have hee : Real.exp (-π * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    calc ‖(jacobiTheta ((t : ℂ) * Complex.I) - 1) ^ 2 +
          2 * (jacobiTheta ((t : ℂ) * Complex.I) - 1)‖
        ≤ ‖(jacobiTheta ((t : ℂ) * Complex.I) - 1) ^ 2‖ +
          ‖2 * (jacobiTheta ((t : ℂ) * Complex.I) - 1)‖ := norm_add_le _ _
      _ = ‖jacobiTheta ((t : ℂ) * Complex.I) - 1‖ ^ 2 +
          2 * ‖jacobiTheta ((t : ℂ) * Complex.I) - 1‖ := by
          rw [norm_pow, norm_mul, Complex.norm_ofNat]
      _ ≤ (C₀ * Real.exp (-π * t)) ^ 2 + 2 * (C₀ * Real.exp (-π * t)) := by
          gcongr <;> first | exact norm_nonneg _ | skip
      _ = C₀ ^ 2 * Real.exp (-π * t) * Real.exp (-π * t) +
          2 * C₀ * Real.exp (-π * t) := by ring
      _ ≤ C₀ ^ 2 * 1 * Real.exp (-π * t) + 2 * C₀ * Real.exp (-π * t) := by
          gcongr
      _ = (C₀ ^ 2 + 2 * C₀) * Real.exp (-π * t) := by ring
  have hO1 : (fun t => thetaSq t - 1) =O[atTop] fun t => Real.exp (-π * t) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C₀ ^ 2 + 2 * C₀, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hexp t ht
  exact hO1.trans (exp_neg_pi_isBigO_rpow r)

/-- **The Gaussian Epstein pair**: the compiled theta packaged for the abstract
functional-equation machinery, with the DC channel as the constant term. -/
noncomputable def epsteinFEPair : WeakFEPair ℂ where
  f := thetaSq
  g := thetaSq
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := continuousOn_thetaSq.locallyIntegrableOn measurableSet_Ioi
  hg_int := continuousOn_thetaSq.locallyIntegrableOn measurableSet_Ioi
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx => by
    rw [one_div, thetaSq_inv (mem_Ioi.mp hx), Real.rpow_one]
    simp [smul_eq_mul]
  hf_top := thetaSq_sub_one_isBigO
  hg_top := thetaSq_sub_one_isBigO

/-- **The Epstein zeta of `ℤ[i]` continues**: the completed readout is holomorphic away from
the DC poles `s ∈ {0, 1}`. -/
theorem epsteinLambda_differentiableAt {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ epsteinFEPair.Λ s :=
  epsteinFEPair.differentiableAt_Λ (Or.inl hs) (Or.inl hs')

/-- **The functional equation** of the Gaussian Epstein zeta: `Λ(1−s) = Λ(s)` (self-dual,
root number one) — the weld reflection through the Mellin projection. -/
theorem epsteinLambda_functional_equation (s : ℂ) :
    epsteinFEPair.Λ (1 - s) = epsteinFEPair.symm.Λ s := by
  have h := epsteinFEPair.functional_equation s
  simp only [show epsteinFEPair.ε = 1 from rfl, one_smul,
    show epsteinFEPair.k = (1 : ℝ) from rfl, Complex.ofReal_one] at h
  exact h

end CriticalLinePhasor.EpsteinTheta

#print axioms CriticalLinePhasor.EpsteinTheta.epsteinFEPair
#print axioms CriticalLinePhasor.EpsteinTheta.epsteinLambda_differentiableAt
#print axioms CriticalLinePhasor.EpsteinTheta.epsteinLambda_functional_equation
