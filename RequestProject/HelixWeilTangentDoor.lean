import RequestProject.HelixWeilTangentProfile
import RequestProject.HelixWeilWitnessAscent

/-!
# The tangent door: a two-parameter RH-complete family (ledger 1346, W4b)

The tangent profile's zero side is `−4λ²|N|²·Σ_ρ m_ρ (ρ−c)² e^{2λ(ρ−c)²}`, `c = ½ + iγ`. Under RH every term of
`Σ m_ρ (ρ−c)² e^{2λ(ρ−c)²}` is `−m_ρ u² e^{−2λu²} ≤ 0`, so the zero side is nonnegative. Conversely:

* at an off-axis zero `ρ₁ = ½ + s + iγ₁`, centring at its own height gives `(ρ₁ − c)² = s² > 0` real, so the pair
  contributes `+2m₁ s² e^{2λs²}`, growing exponentially — a positive term in `Σ`, negative in the zero side;
* `Eexp γ z = (Re z − ½)² − (Im z − γ)²` governs the other terms; a **tangent peak** is an off-axis zero whose near
  competitors all have `Eexp < s²`; the far zeros contribute `O(e^{−7.5λ})` (`tFar_le`);
* `tangent_ascent_step`: not a peak gives a competitor with `d' > d` and `Δ² ≤ d'² − d² ≤ 2(d' − d)` — the
  compiled `Step` of 1341, so the finite-energy ascent and the harmonic-series contradiction carry over verbatim
  (`exists_tangentPeak`);
* `tangentWitness_of_peak`: `∃ λ ≥ 1` with `Re zeroSide < 0`;
* **`riemannHypothesis_of_carrierPositiveTangent : CarrierPositiveTangent a b → RiemannHypothesis`**, with
  `CarrierPositiveTangent a b := ∀ λ ≥ 1, ∀ γ, 0 ≤ Re carrierSide(autocorr(tangentProfile λ γ))`.

The leaf has two real parameters `(λ, γ)` and no `d`. No `sorry`, no `axiom`, no window.
-/

open Complex
open scoped Real ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixWeilWitness

open CriticalLinePhasor.ContourArgument CriticalLinePhasor.HelixCarrierWeil

/-! ## The exponent -/

/-- The exponent of `‖tangentKernel‖` at height `γ`: `(Re z − ½)² − (Im z − γ)²`. -/
def Eexp (γ : ℝ) (z : ℂ) : ℝ := (z.re - 1 / 2) ^ 2 - (z.im - γ) ^ 2

theorem tangentKernel_norm_eq (lam γ : ℝ) (z : ℂ) :
    ‖tangentKernel lam γ z‖ = ‖z - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ z) := by
  unfold tangentKernel Eexp
  rw [norm_mul, norm_pow, Complex.norm_exp, re_lam_mul_sq, axisPt_re, axisPt_im]

theorem norm_sub_axisPt_sq (γ : ℝ) (z : ℂ) :
    ‖z - axisPt γ‖ ^ 2 = (z.re - 1 / 2) ^ 2 + (z.im - γ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [axisPt]
  ring

theorem norm_sub_axisPt_sq_le (γ : ℝ) {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) :
    ‖z - axisPt γ‖ ^ 2 ≤ 1 + (z.im - γ) ^ 2 := by
  rw [norm_sub_axisPt_sq]; nlinarith

theorem norm_sub_axisPt_sq_le_of_near (γ : ℝ) (ρ : Zero) (hn : |ρ.val.im - γ| < 2) :
    ‖ρ.val - axisPt γ‖ ^ 2 ≤ 5 := by
  rw [norm_sub_axisPt_sq]
  have h0 := ρ.2.1; have h1 := ρ.2.2.1
  have hu : (ρ.val.im - γ) ^ 2 < 4 := by nlinarith [abs_nonneg (ρ.val.im - γ), sq_abs (ρ.val.im - γ)]
  nlinarith

theorem Eexp_le (γ : ℝ) (ρ : Zero) : Eexp γ ρ.val ≤ 1 / 4 - (ρ.val.im - γ) ^ 2 := by
  unfold Eexp
  have := ρ.2.1; have := ρ.2.2.1
  nlinarith

/-! ## The tangent peak and the margin -/

/-- **Tangent peak**: every near zero other than `ρ₁` and its mirror has `Eexp < (Re ρ₁ − ½)²`. -/
def TangentPeak (ρ₁ : Zero) : Prop :=
  ∀ ρ : Zero, |ρ.val.im - ρ₁.val.im| < 2 → ρ.val ≠ ρ₁.val → ρ.val ≠ 1 - conj ρ₁.val →
    Eexp ρ₁.val.im ρ.val < (ρ₁.val.re - 1 / 2) ^ 2

theorem exists_tangent_margin (ρ₁ : Zero) (hpeak : TangentPeak ρ₁)
    (S' : Finset Zero) (hS' : ∀ ρ ∈ S', |ρ.val.im - ρ₁.val.im| < 2 ∧ ρ.val ≠ ρ₁.val ∧ ρ.val ≠ 1 - conj ρ₁.val) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ ∈ S', Eexp ρ₁.val.im ρ.val ≤ (ρ₁.val.re - 1 / 2) ^ 2 - δ := by
  by_cases hne : S'.Nonempty
  · obtain ⟨ρm, hρm, hmin⟩ := Finset.exists_min_image S'
      (fun ρ => (ρ₁.val.re - 1 / 2) ^ 2 - Eexp ρ₁.val.im ρ.val) hne
    obtain ⟨hn, h1, h2⟩ := hS' ρm hρm
    have hlt := hpeak ρm hn h1 h2
    refine ⟨(ρ₁.val.re - 1 / 2) ^ 2 - Eexp ρ₁.val.im ρm.val, by linarith, fun ρ hρ => ?_⟩
    have := hmin ρ hρ
    linarith
  · refine ⟨1, one_pos, fun ρ hρ => ?_⟩
    exact absurd ⟨ρ, hρ⟩ hne

/-! ## The terms of the zero side -/

/-- The complex term `m_ρ·(ρ−c)²e^{2λ(ρ−c)²}`. -/
def tTerm (lam γ : ℝ) (ρ : Zero) : ℂ := (ZD.xiOrderNat ρ.val : ℂ) * tangentKernel lam γ ρ.val

theorem tTerm_norm_eq (lam γ : ℝ) (ρ : Zero) :
    ‖tTerm lam γ ρ‖ = (ZD.xiOrderNat ρ.val : ℝ) * (‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val)) := by
  unfold tTerm
  rw [norm_mul, Complex.norm_natCast, tangentKernel_norm_eq]

/-- For `λ ≥ 2`, `‖tTerm‖ ≤ e^{λ/2 − 2}·m·farWeight`. -/
theorem tTerm_norm_le {lam : ℝ} (hlam : 2 ≤ lam) (γ : ℝ) (ρ : Zero) :
    ‖tTerm lam γ ρ‖ ≤ Real.exp (lam / 2 - 2) * ((ZD.xiOrderNat ρ.val : ℝ) * farWeight γ ρ) := by
  rw [tTerm_norm_eq]
  set u : ℝ := ρ.val.im - γ with hu
  have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  have hw : ‖ρ.val - axisPt γ‖ ^ 2 ≤ 1 + u ^ 2 := norm_sub_axisPt_sq_le γ ρ.2.1.le ρ.2.2.1.le
  have hE : Eexp γ ρ.val ≤ 1 / 4 - u ^ 2 := Eexp_le γ ρ
  have h1 : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by have := Real.add_one_le_exp (u ^ 2); linarith
  have hkey : ‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val)
      ≤ Real.exp (lam / 2 - 2) * farWeight γ ρ := by
    unfold farWeight
    rw [← hu]
    calc ‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val)
        ≤ Real.exp (u ^ 2) * Real.exp (2 * lam * (1 / 4 - u ^ 2)) := by
          apply mul_le_mul (hw.trans h1) _ (Real.exp_nonneg _) (Real.exp_nonneg _)
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ 2 * lam)]
      _ = Real.exp (u ^ 2 + 2 * lam * (1 / 4 - u ^ 2)) := by rw [← Real.exp_add]
      _ ≤ Real.exp (lam / 2 - 2 + -2 * (u ^ 2 - 1)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * lam - 3) (sq_nonneg u)]
      _ = Real.exp (lam / 2 - 2) * Real.exp (-2 * (u ^ 2 - 1)) := by rw [← Real.exp_add]
  calc (ZD.xiOrderNat ρ.val : ℝ) * (‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val))
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * (Real.exp (lam / 2 - 2) * farWeight γ ρ) :=
        mul_le_mul_of_nonneg_left hkey hm
    _ = _ := by ring

theorem tTerm_summable {lam : ℝ} (hlam : 2 ≤ lam) (γ : ℝ) : Summable (tTerm lam γ) :=
  Summable.of_norm_bounded ((farWeight_summable γ).mul_left _) (tTerm_norm_le hlam γ)

/-! ## The far tail -/

def tFar (lam γ : ℝ) (ρ : Zero) : ℝ := if 2 ≤ |ρ.val.im - γ| then ‖tTerm lam γ ρ‖ else 0

/-- For `λ ≥ 2` and height distance `≥ 2`, `‖tTerm‖ ≤ e^{−7.5λ + 10}·m·farWeight`. -/
theorem tFar_le {lam : ℝ} (hlam : 2 ≤ lam) (γ : ℝ) (ρ : Zero) :
    tFar lam γ ρ ≤ Real.exp (-(15 / 2) * lam + 10) * ((ZD.xiOrderNat ρ.val : ℝ) * farWeight γ ρ) := by
  unfold tFar
  split_ifs with hfar
  · rw [tTerm_norm_eq]
    set u : ℝ := ρ.val.im - γ with hu
    have hu2 : 4 ≤ u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u, hfar]
    have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
    have hw : ‖ρ.val - axisPt γ‖ ^ 2 ≤ 1 + u ^ 2 := norm_sub_axisPt_sq_le γ ρ.2.1.le ρ.2.2.1.le
    have hE : Eexp γ ρ.val ≤ 1 / 4 - u ^ 2 := Eexp_le γ ρ
    have h1 : 1 + u ^ 2 ≤ Real.exp (u ^ 2) := by have := Real.add_one_le_exp (u ^ 2); linarith
    have hkey : ‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val)
        ≤ Real.exp (-(15 / 2) * lam + 10) * farWeight γ ρ := by
      unfold farWeight
      rw [← hu]
      calc ‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val)
          ≤ Real.exp (u ^ 2) * Real.exp (2 * lam * (1 / 4 - u ^ 2)) := by
            apply mul_le_mul (hw.trans h1) _ (Real.exp_nonneg _) (Real.exp_nonneg _)
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ 2 * lam)]
        _ = Real.exp (u ^ 2 + 2 * lam * (1 / 4 - u ^ 2)) := by rw [← Real.exp_add]
        _ ≤ Real.exp (-(15 / 2) * lam + 10 + -2 * (u ^ 2 - 1)) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul_of_nonneg_left hu2 (by linarith : (0 : ℝ) ≤ 2 * lam - 3)]
        _ = Real.exp (-(15 / 2) * lam + 10) * Real.exp (-2 * (u ^ 2 - 1)) := by rw [← Real.exp_add]
    calc (ZD.xiOrderNat ρ.val : ℝ) * (‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val))
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (Real.exp (-(15 / 2) * lam + 10) * farWeight γ ρ) :=
          mul_le_mul_of_nonneg_left hkey hm
      _ = _ := by ring
  · exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (farWeight_nonneg _ _))

theorem tFar_nonneg (lam γ : ℝ) (ρ : Zero) : 0 ≤ tFar lam γ ρ := by
  unfold tFar
  split_ifs
  · exact norm_nonneg _
  · exact le_refl _

theorem tFar_summable {lam : ℝ} (hlam : 2 ≤ lam) (γ : ℝ) : Summable (tFar lam γ) :=
  Summable.of_nonneg_of_le (tFar_nonneg lam γ) (tFar_le hlam γ) ((farWeight_summable γ).mul_left _)

theorem tFarTail_le {lam : ℝ} (hlam : 2 ≤ lam) (γ : ℝ) :
    ∑' ρ : Zero, tFar lam γ ρ
      ≤ Real.exp (-(15 / 2) * lam + 10) * ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * farWeight γ ρ := by
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (tFar_le hlam γ) (tFar_summable hlam γ) ((farWeight_summable γ).mul_left _)

/-! ## Near and far real parts -/

def tNearRe (lam γ : ℝ) (ρ : Zero) : ℝ := if |ρ.val.im - γ| < 2 then (tTerm lam γ ρ).re else 0

def tFarRe (lam γ : ℝ) (ρ : Zero) : ℝ := if |ρ.val.im - γ| < 2 then 0 else (tTerm lam γ ρ).re

theorem re_tTerm_eq (lam γ : ℝ) (ρ : Zero) : (tTerm lam γ ρ).re = tNearRe lam γ ρ + tFarRe lam γ ρ := by
  unfold tNearRe tFarRe
  split_ifs <;> simp

theorem tFarRe_ge (lam γ : ℝ) (ρ : Zero) : -tFar lam γ ρ ≤ tFarRe lam γ ρ := by
  unfold tFarRe tFar
  by_cases h : |ρ.val.im - γ| < 2
  · rw [if_pos h, if_neg (by linarith)]; simp
  · rw [if_neg h, if_pos (by linarith)]
    have := Complex.abs_re_le_norm (tTerm lam γ ρ)
    have := neg_abs_le (tTerm lam γ ρ).re
    linarith

theorem tNearRe_eq_zero_of_not_mem (lam γ : ℝ) {ρ : Zero} (h : ρ ∉ (nearSet_finite (axisPt γ)).toFinset) :
    tNearRe lam γ ρ = 0 := by
  unfold tNearRe
  rw [if_neg]
  intro hlt
  apply h
  rw [Set.Finite.mem_toFinset]
  show |ρ.val.im - (axisPt γ).im| < 2
  rw [axisPt_im]
  exact hlt

theorem tNearRe_summable (lam γ : ℝ) : Summable (tNearRe lam γ) :=
  summable_of_ne_finset_zero (fun ρ hρ => tNearRe_eq_zero_of_not_mem lam γ hρ)

theorem tsum_tNearRe (lam γ : ℝ) :
    ∑' ρ : Zero, tNearRe lam γ ρ = ∑ ρ ∈ (nearSet_finite (axisPt γ)).toFinset, (tTerm lam γ ρ).re := by
  rw [tsum_eq_sum (fun ρ hρ => tNearRe_eq_zero_of_not_mem lam γ hρ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  have hρ' : |ρ.val.im - (axisPt γ).im| < 2 := hρ
  rw [axisPt_im] at hρ'
  unfold tNearRe
  rw [if_pos hρ']

/-! ## The pair's own values -/

theorem sub_axisPt_self (ρ₁ : Zero) : ρ₁.val - axisPt ρ₁.val.im = ((ρ₁.val.re - 1 / 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [axisPt]
  · simp [axisPt]

theorem mirror_sub_axisPt (ρ₁ : Zero) :
    (1 - conj ρ₁.val) - axisPt ρ₁.val.im = -((ρ₁.val.re - 1 / 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [axisPt, Complex.conj_re]; ring
  · simp [axisPt, Complex.conj_im]

theorem tangentKernel_at_zero (lam : ℝ) (ρ₁ : Zero) :
    tangentKernel lam ρ₁.val.im ρ₁.val
      = (((ρ₁.val.re - 1 / 2) ^ 2 * Real.exp (2 * lam * (ρ₁.val.re - 1 / 2) ^ 2) : ℝ) : ℂ) := by
  unfold tangentKernel
  rw [sub_axisPt_self]
  push_cast
  ring_nf

theorem tangentKernel_at_mirror (lam : ℝ) (ρ₁ : Zero) :
    tangentKernel lam ρ₁.val.im (1 - conj ρ₁.val)
      = (((ρ₁.val.re - 1 / 2) ^ 2 * Real.exp (2 * lam * (ρ₁.val.re - 1 / 2) ^ 2) : ℝ) : ℂ) := by
  unfold tangentKernel
  rw [mirror_sub_axisPt, neg_sq]
  push_cast
  ring_nf

/-! ## The witness at a tangent peak -/

set_option maxHeartbeats 1600000 in
/-- **The tangent zero sum is positive for large λ at a tangent peak**: `Re Σ_ρ m_ρ (ρ−c)² e^{2λ(ρ−c)²} > 0`
with `c = ½ + i·Im ρ₁`. -/
theorem tangentSum_pos_of_peak (ρ₁ : Zero) (hβ : ρ₁.val.re ≠ 1 / 2) (hpeak : TangentPeak ρ₁) :
    ∃ lam : ℝ, 2 ≤ lam ∧ 0 < (∑' ρ : Zero, tTerm lam ρ₁.val.im ρ).re := by
  set γ : ℝ := ρ₁.val.im with hγdef
  set q : ℝ := (ρ₁.val.re - 1 / 2) ^ 2 with hqdef
  have hq : 0 < q := by
    have : ρ₁.val.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr hβ
    positivity
  -- the mirror as an element of `Zero`
  let ρm : Zero := ⟨1 - conj ρ₁.val, mirror_mem ρ₁⟩
  have hρm_ne : ρm ≠ ρ₁ := by
    intro h
    have := congrArg (fun ρ : Zero => ρ.val.re) h
    simp only [ρm, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    apply hβ; linarith
  -- the near finite set and the other near zeros
  set S : Finset Zero := (nearSet_finite (axisPt γ)).toFinset with hSdef
  have hmemS : ∀ ρ : Zero, ρ ∈ S ↔ |ρ.val.im - γ| < 2 := by
    intro ρ
    rw [hSdef, Set.Finite.mem_toFinset]
    show |ρ.val.im - (axisPt γ).im| < 2 ↔ _
    rw [axisPt_im]
  have hρ₁S : ρ₁ ∈ S := by rw [hmemS]; show |ρ₁.val.im - ρ₁.val.im| < 2; simp
  have hρmS : ρm ∈ S.erase ρ₁ := by
    rw [Finset.mem_erase]
    refine ⟨hρm_ne, ?_⟩
    rw [hmemS]
    show |(1 - conj ρ₁.val).im - ρ₁.val.im| < 2
    simp [Complex.conj_im]
  set S' : Finset Zero := (S.erase ρ₁).erase ρm with hS'def
  have hS' : ∀ ρ ∈ S', |ρ.val.im - ρ₁.val.im| < 2 ∧ ρ.val ≠ ρ₁.val ∧ ρ.val ≠ 1 - conj ρ₁.val := by
    intro ρ hρ
    rw [hS'def, Finset.mem_erase, Finset.mem_erase] at hρ
    obtain ⟨h1, h2, h3⟩ := hρ
    rw [hmemS] at h3
    refine ⟨h3, fun h => h2 (Subtype.ext h), fun h => h1 (Subtype.ext h)⟩
  obtain ⟨δ, hδ, hmargin⟩ := exists_tangent_margin ρ₁ hpeak S' hS'
  -- the constants
  set K : ℝ := ∑ ρ ∈ S', (ZD.xiOrderNat ρ.val : ℝ) with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  set T₀ : ℝ := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℝ) * farWeight γ ρ with hT₀def
  have hT₀ : 0 ≤ T₀ := tsum_nonneg (fun ρ => mul_nonneg (Nat.cast_nonneg _) (farWeight_nonneg _ _))
  -- choose λ
  set lam : ℝ := max 2 (max (Real.log (10 * K / q + 1) / (2 * δ))
    (Real.log (2 * Real.exp 10 * T₀ / q + 1) / (2 * q))) with hlamdef
  have hlam2 : 2 ≤ lam := le_max_left _ _
  have hKe : 10 * K / q + 1 ≤ Real.exp (2 * δ * lam) :=
    exp_ge_of_le (by positivity) (by positivity) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hTe : 2 * Real.exp 10 * T₀ / q + 1 ≤ Real.exp (2 * q * lam) :=
    exp_ge_of_le (by positivity) (by positivity) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨lam, hlam2, ?_⟩
  -- the real part splits
  have hsum := tTerm_summable hlam2 γ
  rw [Complex.re_tsum hsum]
  have hre_sum : Summable (fun ρ : Zero => (tTerm lam γ ρ).re) := Complex.reCLM.summable hsum
  have hfar_sum : Summable (tFarRe lam γ) := by
    have := hre_sum.sub (tNearRe_summable lam γ)
    refine this.congr fun ρ => ?_
    show (tTerm lam γ ρ).re - tNearRe lam γ ρ = tFarRe lam γ ρ
    rw [re_tTerm_eq]; ring
  have hsplit : ∑' ρ : Zero, (tTerm lam γ ρ).re
      = ∑' ρ : Zero, tNearRe lam γ ρ + ∑' ρ : Zero, tFarRe lam γ ρ := by
    rw [← Summable.tsum_add (tNearRe_summable lam γ) hfar_sum]
    apply tsum_congr
    intro ρ
    exact re_tTerm_eq lam γ ρ
  rw [hsplit, tsum_tNearRe]
  -- the far part
  have hfar : -(Real.exp (-(15 / 2) * lam + 10) * T₀) ≤ ∑' ρ : Zero, tFarRe lam γ ρ := by
    have h1 : ∑' ρ : Zero, -tFar lam γ ρ ≤ ∑' ρ : Zero, tFarRe lam γ ρ :=
      Summable.tsum_le_tsum (tFarRe_ge lam γ) (tFar_summable hlam2 γ).neg hfar_sum
    rw [tsum_neg] at h1
    have h2 := tFarTail_le hlam2 γ
    linarith
  -- the near part: the pair plus the others
  rw [← Finset.add_sum_erase S _ hρ₁S, ← Finset.add_sum_erase (S.erase ρ₁) _ hρmS]
  set E : ℝ := Real.exp (2 * q * lam) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hpair0 : (tTerm lam γ ρ₁).re = (ZD.xiOrderNat ρ₁.val : ℝ) * (q * E) := by
    unfold tTerm
    rw [tangentKernel_at_zero]
    have : ((ZD.xiOrderNat ρ₁.val : ℂ) * (((ρ₁.val.re - 1 / 2) ^ 2 * Real.exp (2 * lam * (ρ₁.val.re - 1 / 2) ^ 2) : ℝ) : ℂ))
        = (((ZD.xiOrderNat ρ₁.val : ℝ) * (q * E) : ℝ) : ℂ) := by
      rw [hEdef, hqdef]; push_cast; ring_nf
    rw [this, Complex.ofReal_re]
  have hpairm : (tTerm lam γ ρm).re = (ZD.xiOrderNat ρ₁.val : ℝ) * (q * E) := by
    unfold tTerm
    show ((ZD.xiOrderNat (1 - conj ρ₁.val) : ℂ) * tangentKernel lam γ (1 - conj ρ₁.val)).re = _
    rw [tangentKernel_at_mirror, mirror_order]
    have : ((ZD.xiOrderNat ρ₁.val : ℂ) * (((ρ₁.val.re - 1 / 2) ^ 2 * Real.exp (2 * lam * (ρ₁.val.re - 1 / 2) ^ 2) : ℝ) : ℂ))
        = (((ZD.xiOrderNat ρ₁.val : ℝ) * (q * E) : ℝ) : ℂ) := by
      rw [hEdef, hqdef]; push_cast; ring_nf
    rw [this, Complex.ofReal_re]
  have hm₁ : (1 : ℝ) ≤ (ZD.xiOrderNat ρ₁.val : ℝ) :=
    Nat.one_le_cast.mpr (Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros ρ₁.2))
  -- the other near zeros: each `≥ −5 m e^{2λ(q − δ)}`
  have hothers : -(5 * K * E / Real.exp (2 * δ * lam)) ≤ ∑ ρ ∈ S', (tTerm lam γ ρ).re := by
    have hterm : ∀ ρ ∈ S', -((ZD.xiOrderNat ρ.val : ℝ) * (5 * E / Real.exp (2 * δ * lam)))
        ≤ (tTerm lam γ ρ).re := by
      intro ρ hρ
      obtain ⟨hn, -, -⟩ := hS' ρ hρ
      have hre : -‖tTerm lam γ ρ‖ ≤ (tTerm lam γ ρ).re := by
        have := Complex.abs_re_le_norm (tTerm lam γ ρ)
        have := neg_abs_le (tTerm lam γ ρ).re
        linarith
      rw [tTerm_norm_eq] at hre
      have hw : ‖ρ.val - axisPt γ‖ ^ 2 ≤ 5 := norm_sub_axisPt_sq_le_of_near γ ρ hn
      have hM : Eexp γ ρ.val ≤ q - δ := by rw [hqdef]; exact hmargin ρ hρ
      have hexpM : Real.exp (2 * lam * Eexp γ ρ.val) ≤ E / Real.exp (2 * δ * lam) := by
        rw [hEdef, ← Real.exp_sub]
        apply Real.exp_le_exp.mpr
        have hl0 : 0 ≤ lam := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hM hl0]
      have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
      have hprod : ‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val) ≤ 5 * (E / Real.exp (2 * δ * lam)) :=
        mul_le_mul hw hexpM (Real.exp_nonneg _) (by norm_num)
      calc -((ZD.xiOrderNat ρ.val : ℝ) * (5 * E / Real.exp (2 * δ * lam)))
          ≤ -((ZD.xiOrderNat ρ.val : ℝ) * (‖ρ.val - axisPt γ‖ ^ 2 * Real.exp (2 * lam * Eexp γ ρ.val))) := by
            apply neg_le_neg
            apply mul_le_mul_of_nonneg_left _ hm
            rw [mul_div_assoc]
            exact hprod
        _ ≤ (tTerm lam γ ρ).re := hre
    have hrew : ∑ ρ ∈ S', -((ZD.xiOrderNat ρ.val : ℝ) * (5 * E / Real.exp (2 * δ * lam)))
        = -(5 * (∑ ρ ∈ S', (ZD.xiOrderNat ρ.val : ℝ)) * E / Real.exp (2 * δ * lam)) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl; intro ρ _; ring
    have hle := Finset.sum_le_sum hterm
    rw [hrew] at hle
    rw [hKdef]
    exact hle
  -- combine
  rw [hpair0, hpairm]
  have hpairs : 2 * (q * E) ≤ (ZD.xiOrderNat ρ₁.val : ℝ) * (q * E) + (ZD.xiOrderNat ρ₁.val : ℝ) * (q * E) := by
    have hqE : 0 ≤ q * E := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hm₁ hqE]
  have hothers' : -(q * E / 2) ≤ ∑ ρ ∈ S', (tTerm lam γ ρ).re := by
    have hpos : 0 < Real.exp (2 * δ * lam) := Real.exp_pos _
    have : 5 * K * E / Real.exp (2 * δ * lam) ≤ q * E / 2 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      -- 10 K E ≤ q E e^{2δλ}  ⟸  10K/q + 1 ≤ e^{2δλ}
      have h10 : 10 * K ≤ q * Real.exp (2 * δ * lam) := by
        have := mul_le_mul_of_nonneg_left hKe hq.le
        have hq' : q * (10 * K / q + 1) = 10 * K + q := by field_simp
        rw [hq'] at this
        linarith
      have hE0 : 0 ≤ E := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h10 hE0]
    linarith
  have hfar' : -(q * E / 2) ≤ ∑' ρ : Zero, tFarRe lam γ ρ := by
    have hdecay : Real.exp (-(15 / 2) * lam + 10) ≤ Real.exp 10 := by
      apply Real.exp_le_exp.mpr; linarith
    have h1 : Real.exp (-(15 / 2) * lam + 10) * T₀ ≤ Real.exp 10 * T₀ :=
      mul_le_mul_of_nonneg_right hdecay hT₀
    have h2 : Real.exp 10 * T₀ ≤ q * E / 2 := by
      have := mul_le_mul_of_nonneg_left hTe hq.le
      have hq' : q * (2 * Real.exp 10 * T₀ / q + 1) = 2 * Real.exp 10 * T₀ + q := by field_simp
      rw [hq', hEdef] at this
      rw [hEdef]
      linarith
    linarith
  have hqE : 0 < q * E := by positivity
  linarith

/-- **The tangent witness**: at a tangent peak the zero side at the tangent profile is strictly negative for some
`λ ≥ 1`. -/
theorem tangentWitness_of_peak (ρ₁ : Zero) (hβ : ρ₁.val.re ≠ 1 / 2) (hpeak : TangentPeak ρ₁) :
    ∃ lam : ℝ, 1 ≤ lam ∧ (zeroSide (autocorr (tangentProfile lam ρ₁.val.im))).re < 0 := by
  obtain ⟨lam, hlam, hpos⟩ := tangentSum_pos_of_peak ρ₁ hβ hpeak
  refine ⟨lam, by linarith, ?_⟩
  have hlam0 : 0 < lam := by linarith
  unfold zeroSide
  have hrw : (fun ρ : Zero => (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest (autocorr (tangentProfile lam ρ₁.val.im)) ρ.val)
      = fun ρ : Zero => -((4 * lam ^ 2 * Complex.normSq (gaussNorm lam) : ℝ) : ℂ) * tTerm lam ρ₁.val.im ρ := by
    funext ρ
    rw [tangent_autocorr_eq hlam0]
    unfold tTerm
    ring
  rw [hrw, tsum_mul_left, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
  have hN : 0 < Complex.normSq (gaussNorm lam) := Complex.normSq_pos.mpr (gaussNorm_ne_zero hlam0)
  have hc : 0 < 4 * lam ^ 2 * Complex.normSq (gaussNorm lam) := by positivity
  simp only [neg_zero, zero_mul, sub_zero]
  nlinarith [mul_pos hc hpos]

/-! ## The ascent for the tangent exponent -/

/-- **The tangent ascent step**: not a tangent peak gives a competitor of strictly larger deviation with
`Δ² ≤ d'² − d² ≤ 2(d' − d)`. -/
theorem tangent_ascent_step {ρ₁ : Zero} (hβ : ρ₁.val.re ≠ 1 / 2) (hno : ¬ TangentPeak ρ₁) :
    ∃ ρ : Zero, dev ρ₁ < dev ρ ∧ (ρ.val.im - ρ₁.val.im) ^ 2 ≤ 2 * (dev ρ - dev ρ₁) := by
  unfold TangentPeak at hno
  push_neg at hno
  obtain ⟨ρ, _hn, h1, h2, hE⟩ := hno
  refine ⟨ρ, ?_⟩
  unfold Eexp at hE
  unfold dev
  set s : ℝ := ρ₁.val.re - 1 / 2 with hs
  set s' : ℝ := ρ.val.re - 1 / 2 with hs'
  set Δ : ℝ := ρ.val.im - ρ₁.val.im with hΔ
  have hsq : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  have hsq' : s' ^ 2 = |s'| ^ 2 := (sq_abs s').symm
  rw [hsq, hsq'] at hE
  have hs_pos : 0 < |s| := abs_pos.mpr (sub_ne_zero.mpr hβ)
  have hs'_nn : 0 ≤ |s'| := abs_nonneg _
  have hs_lt : |s| < 1 / 2 := by rw [hs]; exact dev_lt_half ρ₁
  have hs'_lt : |s'| < 1 / 2 := by rw [hs']; exact dev_lt_half ρ
  have hΔsq : 0 ≤ Δ ^ 2 := sq_nonneg _
  have hle : |s| ≤ |s'| := by
    by_contra hlt
    push_neg at hlt
    have : |s'| ^ 2 < |s| ^ 2 := by nlinarith
    linarith
  have hne : |s| ≠ |s'| := by
    intro heq
    have hΔ0 : Δ = 0 := by
      have h0 : Δ ^ 2 ≤ 0 := by rw [← heq] at hE; linarith
      exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h0 hΔsq)
    have hsq2 : s' ^ 2 = s ^ 2 := (sq_eq_sq_iff_abs_eq_abs s' s).mpr heq.symm
    have hfac : (s' - s) * (s' + s) = 0 := by
      have : (s' - s) * (s' + s) = s' ^ 2 - s ^ 2 := by ring
      rw [this, hsq2, sub_self]
    have him : ρ.val.im = ρ₁.val.im := by rw [hΔ] at hΔ0; linarith
    rcases mul_eq_zero.mp hfac with h | h
    · apply h1
      apply Complex.ext
      · rw [hs, hs'] at h; linarith
      · exact him
    · apply h2
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; rw [hs, hs'] at h; linarith
      · simp [Complex.conj_im]; exact him
  have hlt : |s| < |s'| := lt_of_le_of_ne hle hne
  refine ⟨hlt, ?_⟩
  have h3 : |s'| + |s| ≤ 1 := by linarith
  have hdiff : 0 ≤ |s'| - |s| := by linarith
  calc Δ ^ 2 ≤ |s'| ^ 2 - |s| ^ 2 := by linarith
    _ = (|s'| - |s|) * (|s'| + |s|) := by ring
    _ ≤ (|s'| - |s|) * 1 := mul_le_mul_of_nonneg_left h3 hdiff
    _ ≤ 2 * (|s'| - |s|) := by linarith

/-- **A tangent peak exists whenever an off-axis zero exists** (the finite-energy ascent of 1341). -/
theorem exists_tangentPeak (ρ₀ : Zero) (hβ : ρ₀.val.re ≠ 1 / 2) :
    ∃ ρ₁ : Zero, ρ₁.val.re ≠ 1 / 2 ∧ TangentPeak ρ₁ := by
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ ρ : OffZero, ∃ ρ' : OffZero, Step ρ ρ' := by
    intro ρ
    obtain ⟨ρ', h1, h2⟩ := tangent_ascent_step ρ.2 (hcon ρ.1 ρ.2)
    have hoff : ρ'.val.re ≠ 1 / 2 := off_of_dev_pos (lt_of_le_of_lt (dev_nonneg ρ.1) h1)
    exact ⟨⟨ρ', hoff⟩, h1, h2⟩
  set f : ℕ → OffZero := ascent hstep ⟨ρ₀, hβ⟩ with hf
  have hspec : ∀ n, Step (f n) (f (n + 1)) := fun n => ascent_spec hstep ⟨ρ₀, hβ⟩ n
  have hmono : StrictMono (fun n => dev (f n).1) := strictMono_nat_of_lt_succ (fun n => (hspec n).1)
  have hinj : Function.Injective (fun n => (f n).1) := by
    intro m n h
    apply hmono.injective
    show dev (f m).1 = dev (f n).1
    simp only at h
    rw [h]
  have henergy : ∀ n, ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im) ^ 2
      ≤ 2 * (dev (f n).1 - dev (f 0).1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := (hspec n).2
      linarith
  have henergy1 : ∀ n, ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im) ^ 2 ≤ 1 := by
    intro n
    have h1 := henergy n
    have h2 := dev_lt_half (f n).1
    have h3 := dev_nonneg (f 0).1
    linarith
  have hheight : ∀ n : ℕ, ((f n).1.val.im - (f 0).1.val.im) ^ 2 ≤ n := by
    intro n
    have htel : ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im)
        = (f n).1.val.im - (f 0).1.val.im := Finset.sum_range_sub (fun k => (f k).1.val.im) n
    rw [← htel]
    calc (∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im)) ^ 2
        ≤ ((Finset.range n).card : ℝ) * ∑ k ∈ Finset.range n, ((f (k + 1)).1.val.im - (f k).1.val.im) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ (n : ℝ) * 1 := by
          rw [Finset.card_range]
          exact mul_le_mul_of_nonneg_left (henergy1 n) (Nat.cast_nonneg _)
      _ = n := mul_one _
  set γ₀ : ℝ := (f 0).1.val.im with hγ₀
  have hnorm : ∀ n : ℕ, ‖(f n).1.val‖ ^ 2 ≤ 1 + 2 * γ₀ ^ 2 + 2 * n := by
    intro n
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hre : (f n).1.val.re * (f n).1.val.re ≤ 1 := by
      have h0 := (f n).1.2.1
      have h1 := (f n).1.2.2.1
      nlinarith
    have him : (f n).1.val.im * (f n).1.val.im ≤ 2 * γ₀ ^ 2 + 2 * n := by
      have := hheight n
      nlinarith [sq_nonneg ((f n).1.val.im - 2 * γ₀)]
    linarith
  have hsum : Summable (fun n : ℕ => (ZD.xiOrderNat (f n).1.val : ℝ) / ‖(f n).1.val‖ ^ 2) :=
    ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.comp_injective hinj
  have hC : (0 : ℝ) < 1 + 2 * γ₀ ^ 2 + 2 := by positivity
  have hlow : ∀ n : ℕ, 1 / ((1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ))
      ≤ (ZD.xiOrderNat (f n).1.val : ℝ) / ‖(f n).1.val‖ ^ 2 := by
    intro n
    have hm : (1 : ℝ) ≤ (ZD.xiOrderNat (f n).1.val : ℝ) :=
      Nat.one_le_cast.mpr (Nat.succ_le_of_lt (ZD.xiOrderNat_pos_of_mem_NontrivialZeros (f n).1.2))
    have hpos : 0 < ‖(f n).1.val‖ ^ 2 := by
      have hne : (f n).1.val ≠ 0 := by
        intro h
        have := (f n).1.2.1
        rw [h] at this
        simp at this
      positivity
    have hle : ‖(f n).1.val‖ ^ 2 ≤ (1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ) := by
      have := hnorm n
      push_cast
      nlinarith [sq_nonneg γ₀, Nat.cast_nonneg (α := ℝ) n]
    calc 1 / ((1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ)) ≤ 1 / ‖(f n).1.val‖ ^ 2 :=
          one_div_le_one_div_of_le hpos hle
      _ ≤ (ZD.xiOrderNat (f n).1.val : ℝ) / ‖(f n).1.val‖ ^ 2 := by
          rw [div_le_div_iff_of_pos_right hpos]; exact hm
  have hharm : Summable (fun n : ℕ => 1 / ((1 + 2 * γ₀ ^ 2 + 2) * ((n + 1 : ℕ) : ℝ))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hlow hsum
  have h2 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    have := hharm.mul_left (1 + 2 * γ₀ ^ 2 + 2)
    refine this.congr (fun n => ?_)
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    field_simp
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp h2)

/-! ## The tangent door -/

/-- **Carrier positivity on the tangent profiles**: the prime–Γ functional is nonnegative on the autocorrelation
of every tangent profile with `λ ≥ 1` and centre on the axis. A two-parameter family, `(λ, γ)`. -/
def CarrierPositiveTangent (a b : ℝ) : Prop :=
  ∀ lam : ℝ, 1 ≤ lam → ∀ γ : ℝ, 0 ≤ (carrierSide (autocorr (tangentProfile lam γ)) a b).re

/-- **Carrier positivity on the tangent profiles puts every zero on the axis.** -/
theorem axis_of_carrierPositiveTangent {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hpos : CarrierPositiveTangent a b) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ρ, hρ, hne⟩ := hcon
  obtain ⟨ρ₁, hβ, hpeak⟩ := exists_tangentPeak ⟨ρ, hρ⟩ hne
  obtain ⟨lam, hlam, hneg⟩ := tangentWitness_of_peak ρ₁ hβ hpeak
  have hge := hpos lam hlam ρ₁.val.im
  rw [carrierSide_tangent_eq_zeroSide hlam ρ₁.val.im ha hb] at hge
  linarith

/-- **The tangent door**: `CarrierPositiveTangent a b → RiemannHypothesis`. -/
theorem riemannHypothesis_of_carrierPositiveTangent {a b : ℝ} (ha : a < 0) (hb : 1 < b)
    (hpos : CarrierPositiveTangent a b) : RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (axis_of_carrierPositiveTangent ha hb hpos)

end CriticalLinePhasor.HelixWeilWitness

end

#print axioms CriticalLinePhasor.HelixWeilWitness.tangentSum_pos_of_peak
#print axioms CriticalLinePhasor.HelixWeilWitness.tangentWitness_of_peak
#print axioms CriticalLinePhasor.HelixWeilWitness.exists_tangentPeak
#print axioms CriticalLinePhasor.HelixWeilWitness.axis_of_carrierPositiveTangent
#print axioms CriticalLinePhasor.HelixWeilWitness.riemannHypothesis_of_carrierPositiveTangent
