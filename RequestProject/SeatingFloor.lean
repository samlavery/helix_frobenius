import RequestProject.SeatingDetector
import Zeta23.Unconditional
import Zeta23.Statement.SeamClosed

/-!
# The compiled density floor under the seating leaf

The Zeta23 artifact's census vocabulary is definitionally our ledger's:
`zerosIn = stripBox`, `N0star = onLineBox.ncard`.  Translating, their
unconditional two-thirds theorem becomes a compiled floor directly beneath the
seating leaf:

  `seating_density_floor` — for every `ε > 0`, eventually in every dyadic box
  `(T, 2T]`:  `(2/3 − ε)·census ≤ on-line census`.

So the leaf (`census ≤ flips`, equivalently census = on-line census per box
with flip visibility) starts from a compiled 2/3, not from zero.

No `sorry`, no `axiom` (consumes the Apache-2.0 zeta-23-lean artifact by
import; see `ClockRateStirling.lean` for the attribution convention).
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- The ledger's strip box is Zeta23's window, definitionally. -/
theorem stripBox_eq_zerosIn (T₁ T₂ : ℝ) :
    stripBox T₁ T₂ = Zeta23.zerosIn T₁ T₂ := by
  ext ρ
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨⟨h3, h1, h2⟩, h4, h5⟩
  · rintro ⟨⟨h3, h1, h2⟩, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, h4, h5⟩

/-- The ledger's on-line box is Zeta23's `N0star` set. -/
theorem onLineBox_eq (T₁ T₂ : ℝ) :
    onLineBox T₁ T₂ = Zeta23.zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1/2} := by
  ext ρ
  constructor
  · rintro ⟨hs, hre⟩
    exact ⟨(stripBox_eq_zerosIn T₁ T₂) ▸ hs, hre⟩
  · rintro ⟨hz, hre⟩
    exact ⟨(stripBox_eq_zerosIn T₁ T₂) ▸ hz, hre⟩

/-- Distinct census ≤ multiplicity census. -/
theorem census_le_Ncount (T₁ T₂ : ℝ) :
    (stripBox T₁ T₂).ncard ≤ Zeta23.Ncount T₁ T₂ := by
  rw [stripBox_eq_zerosIn]
  unfold Zeta23.Ncount
  have hfin := Zeta23.zerosIn_finite T₁ T₂
  have hsupp : Zeta23.zerosIn T₁ T₂ ∩ Function.support Zeta23.zeroMult
      = Zeta23.zerosIn T₁ T₂ := by
    apply Set.inter_eq_left.mpr
    intro ρ hρ
    have := Zeta23.ZetaSeam.one_le_mult_holds ρ hρ.1
    simp only [Function.mem_support]
    omega
  have hfin' : (Zeta23.zerosIn T₁ T₂ ∩ Function.support Zeta23.zeroMult).Finite := by
    rw [hsupp]
    exact hfin
  rw [finsum_mem_eq_sum _ hfin']
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hsame : hfin.toFinset = hfin'.toFinset := by
    ext ρ
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hsupp]
  rw [hsame]
  calc hfin'.toFinset.card = ∑ _ρ ∈ hfin'.toFinset, 1 := by simp
    _ ≤ ∑ ρ ∈ hfin'.toFinset, Zeta23.zeroMult ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        exact Zeta23.ZetaSeam.one_le_mult_holds ρ
          ((hfin'.mem_toFinset.mp hρ).1).1

/-- **The compiled density floor** (dyadic windows): eventually,
`(2/3 − ε)·census ≤ on-line census`, in the ledger's own vocabulary. -/
theorem seating_density_floor :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2/3 - ε) * ((stripBox T (2*T)).ncard : ℝ)
        ≤ ((onLineBox T (2*T)).ncard : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.two_thirds_on_critical_line ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have h2 : (onLineBox T (2*T)).ncard = Zeta23.N0star T (2*T) := by
    rw [onLineBox_eq]
    rfl
  rw [h2]
  by_cases hc : (0:ℝ) ≤ 2/3 - ε
  · have h1 : ((stripBox T (2*T)).ncard : ℝ) ≤ (Zeta23.Ncount T (2*T) : ℝ) := by
      exact_mod_cast census_le_Ncount _ _
    calc (2/3 - ε) * ((stripBox T (2*T)).ncard : ℝ)
        ≤ (2/3 - ε) * (Zeta23.Ncount T (2*T) : ℝ) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ ≤ (Zeta23.N0star T (2*T) : ℝ) := h
  · push_neg at hc
    have hle : (2/3 - ε) * ((stripBox T (2*T)).ncard : ℝ) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hc.le, Nat.cast_nonneg _⟩)
    exact le_trans hle (Nat.cast_nonneg _)

/-- Cumulative form: `(2/3 − ε)·census(0,T] ≤ on-line census(0,T]` eventually. -/
theorem seating_density_floor_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2/3 - ε) * ((stripBox 0 T).ncard : ℝ)
        ≤ ((onLineBox 0 T).ncard : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.two_thirds_on_critical_line_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have h2 : (onLineBox 0 T).ncard = Zeta23.N0star 0 T := by
    rw [onLineBox_eq]
    rfl
  rw [h2]
  by_cases hc : (0:ℝ) ≤ 2/3 - ε
  · have h1 : ((stripBox 0 T).ncard : ℝ) ≤ (Zeta23.Ncount 0 T : ℝ) := by
      exact_mod_cast census_le_Ncount _ _
    calc (2/3 - ε) * ((stripBox 0 T).ncard : ℝ)
        ≤ (2/3 - ε) * (Zeta23.Ncount 0 T : ℝ) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ ≤ (Zeta23.N0star 0 T : ℝ) := h
  · push_neg at hc
    have hle : (2/3 - ε) * ((stripBox 0 T).ncard : ℝ) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hc.le, Nat.cast_nonneg _⟩)
    exact le_trans hle (Nat.cast_nonneg _)

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.seating_density_floor
#print axioms CriticalLinePhasor.SeatingLedger.seating_density_floor_cumulative

/-! ## The simple-on-line floor (density ½, with multiplicity 1) -/

namespace CriticalLinePhasor.SeatingLedger

/-- The simple on-line box: on-line zeros of ζ-multiplicity one — the
flip-transversal candidates. -/
def simpleOnLineBox (T₁ T₂ : ℝ) : Set ℂ :=
  {ρ ∈ onLineBox T₁ T₂ | Zeta23.zeroMult ρ = 1}

theorem simpleOnLineBox_eq (T₁ T₂ : ℝ) :
    simpleOnLineBox T₁ T₂
      = Zeta23.zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1/2} ∩ {ρ | Zeta23.zeroMult ρ = 1} := by
  ext ρ
  constructor
  · rintro ⟨hon, hm⟩
    exact ⟨(onLineBox_eq T₁ T₂) ▸ hon, hm⟩
  · rintro ⟨hon, hm⟩
    exact ⟨(onLineBox_eq T₁ T₂) ▸ hon, hm⟩

/-- **The compiled simple floor** (dyadic windows): eventually
`(1/2 − ε)·census ≤ simple on-line census` — the multiplicity half of the
leaf at density ½, in the ledger's own vocabulary. -/
theorem seating_simple_floor :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1/2 - ε) * ((stripBox T (2*T)).ncard : ℝ)
        ≤ ((simpleOnLineBox T (2*T)).ncard : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.half_simple_on_critical_line ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have h2 : (simpleOnLineBox T (2*T)).ncard = Zeta23.N0simple T (2*T) := by
    rw [simpleOnLineBox_eq]
    rfl
  rw [h2]
  by_cases hc : (0:ℝ) ≤ 1/2 - ε
  · have h1 : ((stripBox T (2*T)).ncard : ℝ) ≤ (Zeta23.Ncount T (2*T) : ℝ) := by
      exact_mod_cast census_le_Ncount _ _
    calc (1/2 - ε) * ((stripBox T (2*T)).ncard : ℝ)
        ≤ (1/2 - ε) * (Zeta23.Ncount T (2*T) : ℝ) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ ≤ (Zeta23.N0simple T (2*T) : ℝ) := h
  · push_neg at hc
    have hle : (1/2 - ε) * ((stripBox T (2*T)).ncard : ℝ) ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨hc.le, Nat.cast_nonneg _⟩)
    exact le_trans hle (Nat.cast_nonneg _)

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.seating_simple_floor

/-! ## The distinct floor (¾): multiplicity is rare -/

namespace CriticalLinePhasor.SeatingLedger

/-- **The compiled distinct floor** (dyadic): eventually
`(3/4 − ε)·(census with multiplicity) ≤ distinct census` — multiple zeros are
at most a quarter of the ledger. -/
theorem seating_distinct_floor :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3/4 - ε) * (Zeta23.Ncount T (2*T) : ℝ)
        ≤ ((stripBox T (2*T)).ncard : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.three_quarters_distinct ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have h2 : (stripBox T (2*T)).ncard = Zeta23.Ndist T (2*T) := by
    rw [stripBox_eq_zerosIn]
    rfl
  rw [h2]
  exact h

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.seating_distinct_floor
