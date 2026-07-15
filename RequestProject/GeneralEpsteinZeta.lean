import RequestProject.GeneralLatticeFE

/-!
# The Epstein zeta at every point: continuation and functional equation of `E(z,s)`

The payoff of brick (iii).  The general lattice bank `latticeTheta z` — with its compiled
functional equation `latticeTheta_inv` valid at every `z ∈ ℍ` — is packaged as a Mathlib
`WeakFEPair` with weight `k = 1`, root number `ε = 1`, and DC constants `f₀ = g₀ = 1`.  The
abstract Mellin machinery then delivers, for **every** `z` simultaneously: the completed
Epstein zeta of the lattice `ℤ·z + ℤ` extends to `ℂ`, holomorphic away from `s ∈ {0, 1}`
(`generalEpsteinLambda_differentiableAt`), with the self-dual functional equation
`Λ_z(1-s) = Λ_z(s)` (`generalEpsteinLambda_functional_equation`).  Up to the Mellin
identification of `Λ_z` with `π^{-s}Γ(s)·∑'_{p≠0} gram(z,p)^{-s}` this is the analytic
continuation and functional equation of the real-analytic Eisenstein series `E(z,s)` —
carrier-side, uniformly in `z`, poles exactly on the DC channel.  The new analytic inputs are
the continuity of the bank in the height (`continuousOn_latticeTheta`, locally uniform
`M`-test) and the cusp decay (`latticeThetaC_sub_one_isBigO`: all non-DC phasors die
exponentially, at rate governed by the trace bound `gram_ge`).  No RH/GRH.
-/

open Complex UpperHalfPlane Filter MeasureTheory Set Asymptotics
open scoped Real

namespace CriticalLinePhasor.EpsteinTheta

lemma gram_nonneg (z : ℍ) (p : ℤ × ℤ) : 0 ≤ gram z p := by
  rw [gram]
  exact div_nonneg (by positivity) z.im_pos.le

lemma gram_zero (z : ℍ) : gram z 0 = 0 := by
  simp [gram]

/-- Away from the DC channel the Gram form is bounded below by the trace constant. -/
lemma gram_ge_const (z : ℍ) {p : ℤ × ℤ} (hp : p ≠ 0) :
    z.im / (z.re ^ 2 + z.im ^ 2 + 1) ≤ gram z p := by
  have hz : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (Prod.ext h.1 h.2)
  have h1 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    have hint : (1 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 2 := by
      rcases hz with h | h
      · nlinarith [Int.one_le_abs h, sq_abs p.1, sq_nonneg p.2]
      · nlinarith [Int.one_le_abs h, sq_abs p.2, sq_nonneg p.1]
    exact_mod_cast hint
  refine le_trans ?_ (gram_ge z p)
  have hD : (0 : ℝ) < z.re ^ 2 + z.im ^ 2 + 1 := by positivity
  gcongr
  exact le_mul_of_one_le_left z.im_pos.le h1

/-- Exponentials of any positive rate beat every power at infinity. -/
lemma exp_neg_isBigO_rpow {a : ℝ} (ha : 0 < a) (r : ℝ) :
    (fun t : ℝ => Real.exp (-a * t)) =O[atTop] (· ^ r) := by
  rw [Asymptotics.isBigO_iff]
  set K : ℕ := ⌈-r⌉₊ with hK
  have hrK : -r ≤ (K : ℝ) := hK ▸ Nat.le_ceil _
  refine ⟨(a ^ K)⁻¹, ?_⟩
  have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K
  have hev : ∀ᶠ x : ℝ in atTop, x ^ K * Real.exp (-x) < 1 :=
    hlim.eventually_lt_const one_pos
  rw [eventually_atTop] at hev
  obtain ⟨A, hA⟩ := hev
  filter_upwards [eventually_ge_atTop (max (A / a) 1)] with t htt
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) htt
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hat : A ≤ a * t := by
    have hAa : A / a ≤ t := le_trans (le_max_left _ _) htt
    calc A = a * (A / a) := by field_simp
      _ ≤ a * t := by gcongr
  have h1 : (a * t) ^ K * Real.exp (-(a * t)) ≤ 1 := (hA _ hat).le
  have hatK : (0 : ℝ) < (a * t) ^ K := by positivity
  have h3 : Real.exp (-(a * t)) ≤ ((a * t) ^ K)⁻¹ := by
    calc Real.exp (-(a * t)) = (a * t) ^ K * Real.exp (-(a * t)) / (a * t) ^ K := by
          field_simp
      _ ≤ 1 / (a * t) ^ K := by gcongr
      _ = ((a * t) ^ K)⁻¹ := one_div _
  have h4 : ((t : ℝ) ^ K)⁻¹ ≤ t ^ r := by
    rw [← Real.rpow_natCast t K, ← Real.rpow_neg ht0.le]
    apply Real.rpow_le_rpow_of_exponent_le ht1
    linarith
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-a * t) = Real.exp (-(a * t)) := by rw [neg_mul]
    _ ≤ ((a * t) ^ K)⁻¹ := h3
    _ = (a ^ K)⁻¹ * (t ^ K)⁻¹ := by rw [mul_pow, mul_inv]
    _ ≤ (a ^ K)⁻¹ * t ^ r := by
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ (a ^ K)⁻¹ * ‖t ^ r‖ := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)

/-- The bank is continuous in the height on the positive axis (locally uniform `M`-test). -/
lemma continuousOn_latticeTheta (z : ℍ) :
    ContinuousOn (fun t : ℝ => latticeTheta z t) (Set.Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := mem_Ioi.mp ht₀
  have hcont : ContinuousOn (fun t : ℝ => latticeTheta z t) (Set.Ioi (t₀ / 2)) := by
    unfold latticeTheta
    refine continuousOn_tsum
      (fun p => Continuous.continuousOn (by fun_prop))
      (summable_latticeTheta_term z (half_pos ht₀')) (fun p x hx => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hx' : t₀ / 2 ≤ x := le_of_lt (mem_Ioi.mp hx)
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hx'))
      (gram_nonneg z p)]
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-- The complexified bank. -/
noncomputable def latticeThetaC (z : ℍ) (t : ℝ) : ℂ := (latticeTheta z t : ℂ)

lemma latticeThetaC_inv (z : ℍ) {t : ℝ} (ht : 0 < t) :
    latticeThetaC z t⁻¹ = (t : ℂ) * latticeThetaC z t := by
  rw [latticeThetaC, latticeThetaC, latticeTheta_inv z ht]
  push_cast
  ring

/-- Cusp decay: the bank minus its DC channel dies faster than every power — each non-DC
phasor decays at least at the trace-constant rate. -/
lemma latticeThetaC_sub_one_isBigO (z : ℍ) (r : ℝ) :
    (fun t : ℝ => latticeThetaC z t - 1) =O[atTop] (· ^ r) := by
  set c : ℝ := z.im / (z.re ^ 2 + z.im ^ 2 + 1) with hc
  have hcpos : 0 < c := by
    rw [hc]
    have := z.im_pos
    positivity
  have hkey : ∀ t : ℝ, 1 ≤ t → |latticeTheta z t - 1| ≤
      Real.exp (π * c) * latticeTheta z 1 * Real.exp (-(π * c) * t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hnn : ∀ p : ℤ × ℤ,
        0 ≤ ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
      intro p
      by_cases hp : p = 0
      · rw [if_pos hp]
      · rw [if_neg hp]
        positivity
    have hsplit : latticeTheta z t - 1 =
        ∑' p : ℤ × ℤ, ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
      have h := (summable_latticeTheta_term z ht0).tsum_eq_add_tsum_ite (0 : ℤ × ℤ)
      simp only [gram_zero, mul_zero, Real.exp_zero] at h
      rw [latticeTheta, h]
      ring
    have hterm : ∀ p : ℤ × ℤ,
        ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) ≤
          Real.exp (-(π * c) * (t - 1)) * Real.exp (-(π * 1) * gram z p) := by
      intro p
      by_cases hp : p = 0
      · rw [if_pos hp]
        positivity
      · rw [if_neg hp, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hgc := gram_ge_const z hp
        nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le
          (sub_nonneg.mpr ht)) (sub_nonneg.mpr hgc)]
    have hsum_ite : Summable fun p : ℤ × ℤ =>
        ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) := by
      refine Summable.of_nonneg_of_le hnn (fun p => ?_)
        (summable_latticeTheta_term z ht0)
      by_cases hp : p = 0
      · rw [if_pos hp]
        positivity
      · rw [if_neg hp]
    have hsum_rhs : Summable fun p : ℤ × ℤ =>
        Real.exp (-(π * c) * (t - 1)) * Real.exp (-(π * 1) * gram z p) :=
      (summable_latticeTheta_term z one_pos).mul_left _
    calc |latticeTheta z t - 1|
        = |∑' p : ℤ × ℤ, ite (p = 0) 0 (Real.exp (-(π * t) * gram z p))| := by
          rw [hsplit]
      _ = ∑' p : ℤ × ℤ, ite (p = 0) 0 (Real.exp (-(π * t) * gram z p)) :=
          abs_of_nonneg (tsum_nonneg hnn)
      _ ≤ ∑' p : ℤ × ℤ,
            Real.exp (-(π * c) * (t - 1)) * Real.exp (-(π * 1) * gram z p) :=
          Summable.tsum_le_tsum hterm hsum_ite hsum_rhs
      _ = Real.exp (-(π * c) * (t - 1)) * latticeTheta z 1 := by
          rw [tsum_mul_left, latticeTheta]
      _ = Real.exp (π * c) * latticeTheta z 1 * Real.exp (-(π * c) * t) := by
          rw [show -(π * c) * (t - 1) = π * c + -(π * c) * t by ring, Real.exp_add]
          ring
  have hO1 : (fun t : ℝ => latticeTheta z t - 1) =O[atTop]
      fun t => Real.exp (-(π * c) * t) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨Real.exp (π * c) * latticeTheta z 1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hkey t ht
  have hO2 := hO1.trans (exp_neg_isBigO_rpow (by positivity : (0:ℝ) < π * c) r)
  rw [← Asymptotics.isBigO_norm_left]
  have heq : ∀ t : ℝ, ‖latticeThetaC z t - 1‖ = ‖latticeTheta z t - 1‖ := by
    intro t
    rw [latticeThetaC, show ((latticeTheta z t : ℂ) - 1) =
      ((latticeTheta z t - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
  simp only [heq]
  exact hO2.norm_left

/-- **The general Epstein pair**: the bank at `z` packaged for the abstract
functional-equation machinery — weight one, root number one, DC constant one, for every
`z ∈ ℍ` at once. -/
noncomputable def generalFEPair (z : ℍ) : WeakFEPair ℂ where
  f := latticeThetaC z
  g := latticeThetaC z
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_latticeTheta z)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_latticeTheta z)).locallyIntegrableOn measurableSet_Ioi
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx => by
    rw [one_div, latticeThetaC_inv z (mem_Ioi.mp hx), Real.rpow_one]
    simp [smul_eq_mul]
  hf_top := latticeThetaC_sub_one_isBigO z
  hg_top := latticeThetaC_sub_one_isBigO z

/-- **The Epstein zeta of every lattice `ℤ·z + ℤ` continues**: the completed readout is
holomorphic away from the DC poles `s ∈ {0, 1}`, uniformly in the construction — one proof
for the whole family.  This is the continuation half of `E(z,s)`. -/
theorem generalEpsteinLambda_differentiableAt (z : ℍ) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (generalFEPair z).Λ s :=
  (generalFEPair z).differentiableAt_Λ (Or.inl hs) (Or.inl hs')

/-- **The functional equation of `E(z,s)`**: `Λ_z(1-s) = Λ_z(s)` at every point `z` — the
weld reflection of the general bank transported through the Mellin projection. -/
theorem generalEpsteinLambda_functional_equation (z : ℍ) (s : ℂ) :
    (generalFEPair z).Λ (1 - s) = (generalFEPair z).symm.Λ s := by
  have h := (generalFEPair z).functional_equation s
  simp only [show (generalFEPair z).ε = 1 from rfl, one_smul,
    show (generalFEPair z).k = (1 : ℝ) from rfl, Complex.ofReal_one] at h
  exact h

end CriticalLinePhasor.EpsteinTheta

#print axioms CriticalLinePhasor.EpsteinTheta.generalFEPair
#print axioms CriticalLinePhasor.EpsteinTheta.generalEpsteinLambda_differentiableAt
#print axioms CriticalLinePhasor.EpsteinTheta.generalEpsteinLambda_functional_equation
