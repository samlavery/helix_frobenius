import Mathlib
import RequestProject.HilbertPolyaCapstone

/-!
# Interface to the Zeta23 artifact: two thirds of the census registers

The trusted statement layer of `anthropics/zeta-23-lean` (Claude; Anthropic,
2026 — "More than two thirds of the zeros of the Riemann zeta function lie
on the critical line"), vendored verbatim from `comparator/ChallengeDeps.lean`
(Apache 2.0; Copyright (c) 2026 Anthropic, PBC), together with the bridge to
this repository's census vocabulary and the consumer that turns the
artifact's Theorem A into a registration-majority statement.

The definitions below are character-for-character the artifact's trusted
layer (§1), Mathlib-only, so statement equality with the artifact is
auditable by eye.  The artifact proves its headline theorems sorry-free at
`{propext, Classical.choice, Quot.sound}` on Lean v4.33.0-rc2; its import
into this v4.32.0 build is pending the next toolchain bump, so the consumer
below takes the artifact's exact ε-form statement as its single input —
the same pattern as the Wiener–Ikehara import before PrimeNumberTheoremAnd
was pulled in.  No `axiom`, no `sorry`.
-/

open Complex Set

noncomputable section

namespace CriticalLinePhasor.Zeta23

/-! ## The vendored trusted statement layer (ChallengeDeps §1, verbatim) -/

/-- ρ is a nontrivial zero of the Riemann zeta function: ζ(ρ) = 0 with
0 < Re ρ < 1 (the open critical strip).  [Vendored: ChallengeDeps.lean] -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ, the multiplicity of ρ via Mathlib's `analyticOrderAt`.
[Vendored: ChallengeDeps.lean] -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- The nontrivial zeros with ordinate in the window (T₁, T₂].
[Vendored: ChallengeDeps.lean] -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂): window zeros counted with multiplicity.
[Vendored: ChallengeDeps.lean] -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N₀*(T₁,T₂): the number of DISTINCT zeros on the critical line in the
window.  [Vendored: ChallengeDeps.lean] -/
def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-! ## Bridge: the artifact's vocabulary is this repository's -/

/-- The artifact's zero predicate is literally this repository's
`GRHSpectral`-style strip-zero set for ζ (the `ZD` divisor vocabulary):
the same conjunction, reordered. -/
theorem isNontrivialZero_iff_mem (ρ : ℂ) :
    IsNontrivialZero ρ ↔ ρ ∈ ZD.NontrivialZeros := by
  unfold IsNontrivialZero ZD.NontrivialZeros
  constructor
  · rintro ⟨hz, h0, h1⟩
    exact ⟨h0, h1, hz⟩
  · rintro ⟨h0, h1, hz⟩
    exact ⟨hz, h0, h1⟩

/-- Every zero the artifact counts is a zero this repository's registration
capstone quantifies over, and conversely. -/
theorem zerosIn_eq (T₁ T₂ : ℝ) :
    zerosIn T₁ T₂ =
      {ρ | ρ ∈ ZD.NontrivialZeros ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
  ext ρ
  simp only [zerosIn, Set.mem_setOf_eq, isNontrivialZero_iff_mem]

/-! ## The consumer: Theorem A as a registration majority -/

/-- The artifact's Theorem A (cumulative form), verbatim in its ε-form:
`liminf N₀*(T)/N(T) ≥ 2/3`.  Discharged by
`Solution.two_thirds_on_critical_line_cumulative` of the artifact on
import; stated here as the single input of the consumer. -/
def TheoremA : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ (N0star 0 T : ℝ)

/-- **The registration majority.**  Given the artifact's Theorem A, the
unregistered census mass is eventually a minority: the count of window
zeros not accounted for by distinct on-line registrations is at most
`(1/3 + ε)·N(T)`.  In the house vocabulary: at least two thirds of the
census registers — the off-carrier defect, if nonzero anywhere, is
quantitatively pinned below one third of the ledger. -/
theorem unregistered_minority (hA : TheoremA) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (Ncount 0 T : ℝ) - (N0star 0 T : ℝ) ≤ (1 / 3 + ε) * (Ncount 0 T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hA ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hN : (0 : ℝ) ≤ (Ncount 0 T : ℝ) := Nat.cast_nonneg _
  nlinarith

end CriticalLinePhasor.Zeta23

#print axioms CriticalLinePhasor.Zeta23.isNontrivialZero_iff_mem
#print axioms CriticalLinePhasor.Zeta23.zerosIn_eq
#print axioms CriticalLinePhasor.Zeta23.unregistered_minority
