import RequestProject.HarmonizedCellTelescoping
import RequestProject.FoliatedGlobalPolarization

/-!
# The S(t) warp with its unwrapped registration coordinate

Unfolded construction: the registration helix is
`u ↦ (exp(i π u), u) ∈ ℂ × ℝ`. Its third coordinate records the
unwrapped registration, not the physical height of a zeta event.
For the actual contour and native multiplicity registrations, the difference
is twice the multiplicity of zeros in the right half of the finite strip.
Consequently their circle phases agree, while the third coordinate retains
the complete difference. Multiplicity is retained throughout.

Before construction: what would I try without a prior expectation? Split
the finite strip at its midpoint and transport analytic orders by the
functional-equation reflection. Two decompositions: `apply Finset.sum_bij`
for the reflected halves, and `rw [Finset.sum_union]` for their disjoint
partition. Both are used below.

Search commands, applied before constructing the declarations:
`rg -n -i 'offLine.*(even|two|mod|pair)|even.*offLine|classicalSContour.*
(exp|phase|warp)|Smult.*(exp|phase|warp)|[Ll]ifted[Ww]arp|
[Rr]egistration[Ww]arp' RequestProject --glob '*.lean'`
`rg -n 'sum_involution|sum_bij|sum_filter.*add|sum_add_sum_compl|
even.*invol|invol.*even' .lake/packages/mathlib/Mathlib/Algebra/BigOperators
.lake/packages/mathlib/Mathlib/Data/Finset --glob '*.lean'`
Semantic searches: LeanSearch on fixed-point-free involutions and invariant
weighted sums; Loogle `Finset.sum_bij`.
-/

open Complex Set MeasureTheory Filter
open scoped BigOperators

namespace CriticalLinePhasor.ContourArgument

open CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.FoliatedPolarization
open CriticalLinePhasor.FoliatedGlobalPolarization

/-- One representative side of the reflected pairs, with analytic multiplicity. -/
noncomputable def rightHalfCountMult (T : ℝ) : ℕ :=
  ∑ ρ ∈ (stripZeroFinset T).filter (fun ρ => 1 / 2 < ρ.re), ZD.xiOrderNat ρ

theorem feReflect_mem_stripZeroFinset {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ stripZeroFinset T) : feReflect ρ ∈ stripZeroFinset T := by
  have hs := (stripZeroWindow_finite T).mem_toFinset.mp hρ
  apply (stripZeroWindow_finite T).mem_toFinset.mpr
  refine ⟨feReflect_mem hs.1, ?_, ?_⟩
  · simpa [feReflect] using hs.2.1
  · simpa [feReflect] using hs.2.2

/-- Reflection pairs both halves at the same ordinate and with the same order. -/
theorem leftHalfCountMult_eq_right (T : ℝ) :
    (∑ ρ ∈ (stripZeroFinset T).filter (fun ρ => ρ.re < 1 / 2), ZD.xiOrderNat ρ) =
      rightHalfCountMult T := by
  classical
  unfold rightHalfCountMult
  apply Finset.sum_bij (fun ρ _ => feReflect ρ)
  · intro ρ hρ
    obtain ⟨hmem, hre⟩ := Finset.mem_filter.mp hρ
    refine Finset.mem_filter.mpr ⟨feReflect_mem_stripZeroFinset hmem, ?_⟩
    simp only [feReflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · intro ρ₁ _ ρ₂ _ heq
    have h := congrArg feReflect heq
    simpa using h
  · intro ρ hρ
    obtain ⟨hmem, hre⟩ := Finset.mem_filter.mp hρ
    refine ⟨feReflect ρ, Finset.mem_filter.mpr
      ⟨feReflect_mem_stripZeroFinset hmem, ?_⟩, feReflect_involutive ρ⟩
    simp only [feReflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · intro ρ _
    exact (xiOrderNat_feReflect ρ).symm

/-- The registration defect counts complete reflected pairs, including their orders. -/
theorem offLineStripZeroCountMult_eq_two_mul_right (T : ℝ) :
    offLineStripZeroCountMult T = 2 * rightHalfCountMult T := by
  classical
  have hpartition :
      (stripZeroFinset T).filter (fun ρ => ρ.re ≠ 1 / 2) =
        (stripZeroFinset T).filter (fun ρ => ρ.re < 1 / 2) ∪
        (stripZeroFinset T).filter (fun ρ => 1 / 2 < ρ.re) := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hm, hn⟩
      rcases lt_or_gt_of_ne hn with h | h
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, h⟩
    · rintro (⟨hm, hl⟩ | ⟨hm, hr⟩)
      · exact ⟨hm, ne_of_lt hl⟩
      · exact ⟨hm, ne_of_gt hr⟩
  have hd : Disjoint
      ((stripZeroFinset T).filter (fun ρ => ρ.re < 1 / 2))
      ((stripZeroFinset T).filter (fun ρ => 1 / 2 < ρ.re)) := by
    apply Finset.disjoint_left.mpr
    intro ρ hl hr
    exact (lt_asymm (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hr).2)
  rw [offLineStripZeroCountMult, hpartition, Finset.sum_union hd,
    leftHalfCountMult_eq_right]
  change rightHalfCountMult T + rightHalfCountMult T = _
  omega

theorem offLineStripZeroCountMult_even (T : ℝ) : Even (offLineStripZeroCountMult T) := by
  rw [offLineStripZeroCountMult_eq_two_mul_right]
  exact even_two_mul _

/-- A nonzero defect costs at least one complete pair. -/
theorem two_le_offLineStripZeroCountMult {T : ℝ}
    (h : offLineStripZeroCountMult T ≠ 0) : 2 ≤ offLineStripZeroCountMult T := by
  rw [offLineStripZeroCountMult_eq_two_mul_right] at h ⊢
  omega

/-- A half-turn per unit of S-registration, with full turns still recorded in the lift. -/
noncomputable def registrationPhase (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) * (u : ℂ))

/-- Three real coordinates: circle projection and its unwrapped registration ledger. -/
noncomputable def registrationHelix (u : ℝ) : ℂ × ℝ := (registrationPhase u, u)

theorem registrationPhase_norm (u : ℝ) : ‖registrationPhase u‖ = 1 := by
  simp [registrationPhase, Complex.norm_exp]

theorem registrationPhase_add_two_mul_nat (u : ℝ) (k : ℕ) :
    registrationPhase (u + 2 * k) = registrationPhase u := by
  have hsplit : Complex.I * (Real.pi : ℂ) * ((u + 2 * k : ℝ) : ℂ) =
      Complex.I * (Real.pi : ℂ) * (u : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [registrationPhase, hsplit, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I,
    mul_one]
  rfl

theorem registrationHelix_injective : Function.Injective registrationHelix :=
  fun _ _ h => congrArg Prod.snd h

/-- The actual native and contour warps have exactly the same circle projection. -/
theorem contour_registrationPhase_eq_native {T : ℝ} (hT : GoodHeight T) :
    registrationPhase (classicalSContour hT) = registrationPhase (Smult T) := by
  rw [classicalSContour_eq_Smult_add_offLine hT,
    offLineStripZeroCountMult_eq_two_mul_right, Nat.cast_mul, Nat.cast_ofNat]
  exact registrationPhase_add_two_mul_nat _ _

/-- The third coordinate retains exactly the complete reflected-pair census. -/
theorem contour_registrationHelix_third_gap {T : ℝ} (hT : GoodHeight T) :
    (registrationHelix (classicalSContour hT)).2 - (registrationHelix (Smult T)).2 =
      2 * (rightHalfCountMult T : ℝ) := by
  change classicalSContour hT - Smult T = _
  rw [classicalSContour_eq_Smult_add_offLine hT,
    offLineStripZeroCountMult_eq_two_mul_right]
  push_cast
  ring

/-- The conjugate-pair lattice gives an exact local threshold for the lifted warp. -/
theorem registration_identification_of_gap_lt_two {T : ℝ} (hT : GoodHeight T)
    (hgap : classicalSContour hT - Smult T < 2) :
    classicalSContour hT = Smult T := by
  have hD : (offLineStripZeroCountMult T : ℝ) < 2 := by
    rw [classicalSContour_eq_Smult_add_offLine hT] at hgap
    linarith
  have hz : offLineStripZeroCountMult T = 0 := by
    by_contra hn
    have htwo : (2 : ℝ) ≤ offLineStripZeroCountMult T := by
      exact_mod_cast two_le_offLineStripZeroCountMult hn
    linarith
  rw [classicalSContour_eq_Smult_add_offLine hT, hz]
  simp

/-- Conjugacy sharpens the integrated defect lower bound by a factor of two. -/
theorem integrated_defect_pair_lower_bound {T₀ T : ℝ}
    (h : offLineStripZeroCountMult T₀ ≠ 0) (hT : T₀ ≤ T) :
    2 * (T - T₀) ≤ ∫ t in (0 : ℝ)..T, (offLineStripZeroCountMult t : ℝ) := by
  have hpos : 0 < T₀ := by
    by_contra hle
    exact h (offLineStripZeroCountMult_eq_zero_of_nonpos (not_lt.mp hle))
  have hhead : 0 ≤ ∫ t in (0 : ℝ)..T₀, (offLineStripZeroCountMult t : ℝ) :=
    intervalIntegral.integral_nonneg hpos.le (fun _ _ => Nat.cast_nonneg _)
  have htail : 2 * (T - T₀) ≤ ∫ t in T₀..T, (offLineStripZeroCountMult t : ℝ) := by
    have hc : (∫ _t in T₀..T, (2 : ℝ)) = 2 * (T - T₀) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [← hc]
    apply intervalIntegral.integral_mono_on hT intervalIntegrable_const
      (offLine_intervalIntegrable T₀ T)
    intro t ht
    exact_mod_cast (two_le_offLineStripZeroCountMult h).trans
      (offLineStripZeroCountMult_mono ht.1)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (offLine_intervalIntegrable 0 T₀) (offLine_intervalIntegrable T₀ T)]
  linarith

end CriticalLinePhasor.ContourArgument

#print axioms CriticalLinePhasor.ContourArgument.offLineStripZeroCountMult_eq_two_mul_right
#print axioms CriticalLinePhasor.ContourArgument.contour_registrationPhase_eq_native
#print axioms CriticalLinePhasor.ContourArgument.contour_registrationHelix_third_gap
#print axioms CriticalLinePhasor.ContourArgument.registration_identification_of_gap_lt_two
#print axioms CriticalLinePhasor.ContourArgument.integrated_defect_pair_lower_bound
