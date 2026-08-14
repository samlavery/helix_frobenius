/-
Consumes results from https://github.com/anthropics/zeta-23-lean at commit
3635e74826a4c1fcece7d1cd2b6fa75e43a00510, registered as the path dependency
`Zeta23` in this repository's lake-manifest.json.
Zeta23 — a Lean 4 formalization of critical-line zero-proportion theorems,
Copyright 2026 Anthropic, PBC; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Upstream declarations consumed by this file, all from `Zeta23/Final.lean`
and its transitive statement layer `Zeta23/Statement.lean`:
  * `Zeta23.thmA₀_cumulative` — Theorem A, cumulative, unconditional
  * `Zeta23.Ncount`, `Zeta23.N0star` — the counting functions it is stated with
No upstream source is copied into this repository; §1 below restates the
statement layer so that the interface is auditable without the dependency,
and each restatement is checked against the upstream constant by `rfl`.
-/
import Mathlib
import RequestProject.HilbertPolyaCapstone
import RequestProject.ZetaContourArgument
import RequestProject.GramRegistrationCapstone
import Zeta23.Final

/-!
# Interface to the Zeta23 artifact: two thirds of the census registers

The trusted statement layer of `anthropics/zeta-23-lean` (Claude; Anthropic,
2026 — "More than two thirds of the zeros of the Riemann zeta function lie
on the critical line"), restated verbatim from `comparator/ChallengeDeps.lean`
(Apache 2.0; Copyright (c) 2026 Anthropic, PBC), together with the bridge to
this repository's census vocabulary.  What is genuinely new here is the
*plumbing* — the multiplicity and count bridges below; the consumers that
restate Theorem A in the off-line, source, and Gram vocabularies are
transports, and are labelled as such.

The definitions in §1 are character-for-character the artifact's trusted
layer (§1 of `Zeta23/Statement.lean`), Mathlib-only, so statement equality
with the artifact is auditable by eye; `Ncount_eq_upstream` and
`N0star_eq_upstream` then discharge that audit by `rfl` against the imported
constants, and `theoremA` discharges the former hypothesis outright.

## What the artifact supplies, and what it does not

The artifact's Theorem A is a **lower bound on the registered census** — the
count of zeros that *are* accounted for on the critical line.  That is the
side this repository lacked.  The other side was never in doubt: the ceiling
on the registered census is `N(T)` itself, because one cannot register more
zeros than exist.  That ceiling is proved below as
`sourcedWindow_ncard_le_census`, in two lines and with no analysis, which is
the point — there is no "two-sided census" to be had here; only the floor was
ever the question.

Every classical result in this line is floor-raising against that same
trivially-known ceiling: Selberg (a positive proportion), Levinson (1/3),
Conrey (2/5), Pratt–Robles–Zaharescu–Zeindler (5/12), and this artifact
(2/3).  Each raises the floor; none touches the ceiling.

**RH is the statement that the floor saturates the ceiling** — registered =
all.  In this repository that is `grh_iff_spectral_gram_registration`
(`RequestProject/GramRegistrationCapstone.lean`), an `iff` quantified over
*every* nontrivial zero.  Saturation is a different quantity from a
proportion, not a sharper constant on the same one: no density theorem, at
2/3 or at any constant below 1, is progress toward it, and nothing in this
file should be read as such.

## The chain landed here

New plumbing — this did not exist before and is what the file is for:

* `theoremA` — the artifact's Theorem A, discharged outright, the vendored
  statement layer being `rfl`-equal to the upstream constants;
* `zeroMult_eq_xiOrderNat` — the artifact's ζ-multiplicity is this
  repository's ξ-multiplicity, at every point of the open strip (not merely
  at line points, which is all `eventOrder_eq_xiOrderNat` gave);
* `Ncount_eq_stripZeroCountMult` — the artifact's window count is this
  repository's strip census, the two window conventions checked to agree at
  `T₁ = 0` rather than assumed to.

Transports — Theorem A restated in other vocabularies, carrying **no
mathematical content beyond it**, each labelled in place:

* `offLine_le_third` (and its `S(t)` reading) — the arithmetic complement;
* `sourced_floor` — the same count in the source vocabulary, which
  `sourcedWindow_eq_onLine` shows is the on-line set renamed, because
  `tauChi` is the identity;
* `gram_event_floor` — the same again in the Gram vocabulary, the rank-drop
  being an `iff` with the L-zero.

A note on why the source transport is *not* the first quantitative statement
about the source predicate, which an earlier draft of this file wrongly
claimed.  The predicate `∃ Z > 0, ρ = reprPoint χ Z` unfolds to `Re ρ = 1/2`;
`EveryZeroHasSource` is all-or-nothing because it quantifies over *every*
zero, not because the per-zero predicate carries content.  Counting it is
therefore counting on-line zeros, which is what the artifact already does.

`offLine_le_third` is also proved below, but it is *not* new mathematics and
is labelled accordingly: `N_off ≤ N − N₀*` is the arithmetic complement of the
artifact's `N₀* ≥ (2/3 − ε)·N`, the same content restated in the off-line
coordinate.  It is kept because the S(t) reading is convenient, not because
it is a new bound.

No `axiom`, no `sorry`.
-/

open Complex Set
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResidueJump
open CriticalLinePhasor.HarmonicCell

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
`liminf N₀*(T)/N(T) ≥ 2/3`.  Formerly the single input of the consumer;
discharged unconditionally by `theoremA` below. -/
def TheoremA : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ (N0star 0 T : ℝ)

/-! ### The statement audit, discharged by `rfl`

The restatements of §1 are not merely *equivalent* to the artifact's
counting functions — they are the same constants after δ-reduction. -/

/-- The restated window count is the artifact's. -/
theorem Ncount_eq_upstream : Ncount = _root_.Zeta23.Ncount := rfl

/-- The restated distinct on-line count is the artifact's. -/
theorem N0star_eq_upstream : N0star = _root_.Zeta23.N0star := rfl

/-- **Theorem A, discharged.**  The hypothesis is now a theorem: the
artifact's `Zeta23.thmA₀_cumulative` (unconditional — it is `thmA₁_cumulative`
applied to `Zeta23.zetaEF`, Weil's explicit formula for ζ proved from
Mathlib's functional equation by contour integration) has precisely this
statement, the counting functions being the same constants by
`Ncount_eq_upstream` and `N0star_eq_upstream`. -/
theorem theoremA : TheoremA := _root_.Zeta23.thmA₀_cumulative

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

/-- The registration majority, unconditionally: `unregistered_minority` with
its input discharged. -/
theorem unregistered_minority_uncond :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (Ncount 0 T : ℝ) - (N0star 0 T : ℝ) ≤ (1 / 3 + ε) * (Ncount 0 T : ℝ) :=
  unregistered_minority theoremA

/-! ## The multiplicity bridge: `ord_ζ = ord_ξ` on the whole open strip

`eventOrder_eq_xiOrderNat` gives this at line points only.  The same
`analyticOrderAt_mul` + `analyticOrderAt_congr` argument runs at every point
of the open strip, because `riemannXi_eq_unit_mul_zeta` was already proved
there: the non-ζ factor `u(s) = (s(s−1)/2)·Γℝ(s)` is an analytic unit
throughout `Re s > 0`, `s ≠ 1`, not just on the line. -/

/-- The non-ζ factor of ξ is analytic at every point of the right half plane. -/
theorem unitFactor_analyticAt_strip {z : ℂ} (hre : 0 < z.re) :
    AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2 * Gammaℝ s) z := by
  have hΓinv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) z :=
    (differentiable_Gammaℝ_inv).analyticAt _
  have hΓne : (Gammaℝ z)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre)
  have h2 : AnalyticAt ℂ (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) z := hΓinv.inv hΓne
  have hfun : (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) = Gammaℝ := funext fun s => inv_inv _
  rw [hfun] at h2
  have hpoly : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) z := by
    have hnum : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) z :=
      analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
    exact hnum.div analyticAt_const two_ne_zero
  exact hpoly.mul h2

/-- The non-ζ factor of ξ is nonvanishing at every point of the right half
plane off `s = 1`. -/
theorem unitFactor_ne_zero_strip {z : ℂ} (hre : 0 < z.re) (hz1 : z ≠ 1) :
    z * (z - 1) / 2 * Gammaℝ z ≠ 0 := by
  have h0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl 0 hre
  have h1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 h1) two_ne_zero)
    (Gammaℝ_ne_zero_of_re_pos hre)

/-- ζ is analytic away from its pole. -/
theorem zeta_analyticAt_of_ne_one {z : ℂ} (hz : z ≠ 1) :
    AnalyticAt ℂ riemannZeta z := by
  have hU : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hz)

/-- **The multiplicity bridge.**  At every nontrivial zero, the artifact's
ζ-multiplicity `m_ρ` and this repository's ξ-multiplicity `xiOrderNat` are the
same natural number.  This is what lets a theorem counted in `zeroMult` be
read in the `xiOrderNat` ledger. -/
theorem zeroMult_eq_xiOrderNat {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    zeroMult ρ = ZD.xiOrderNat ρ := by
  obtain ⟨hre, hre1, _⟩ := hρ
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hre1
    exact lt_irrefl 1 hre1
  have hopen : {s : ℂ | 0 < s.re ∧ s ≠ 1} ∈ nhds ρ := by
    refine IsOpen.mem_nhds ?_ ⟨hre, hρ1⟩
    exact (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hev : ZD.riemannXi =ᶠ[nhds ρ]
      fun s => s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
    filter_upwards [hopen] with s hs
    rw [CriticalLinePhasor.ResolventLimit.riemannXi_eq_unit_mul_zeta hs.1 hs.2, mul_assoc]
  have horder : analyticOrderAt ZD.riemannXi ρ = analyticOrderAt riemannZeta ρ := by
    rw [analyticOrderAt_congr hev]
    show analyticOrderAt
      ((fun s : ℂ => s * (s - 1) / 2 * Gammaℝ s) * riemannZeta) ρ = _
    rw [analyticOrderAt_mul (unitFactor_analyticAt_strip hre)
        (zeta_analyticAt_of_ne_one hρ1),
      (unitFactor_analyticAt_strip hre).analyticOrderAt_eq_zero.mpr
        (unitFactor_ne_zero_strip hre hρ1),
      zero_add]
  show (analyticOrderAt riemannZeta ρ).toNat = analyticOrderNatAt ZD.riemannXi ρ
  unfold analyticOrderNatAt
  exact congrArg ENat.toNat horder.symm

/-! ## The count bridge: the artifact's `N(T)` is this repository's census

The two window conventions agree at the cumulative endpoint: the artifact's
`zerosIn T₁ T₂` asks `T₁ < Im ρ ≤ T₂`, and this repository's
`stripZeroWindow T` asks `0 < Im ρ ≤ T`, so at `T₁ = 0` the two predicates
are literally the same conjunction — checked by `rfl` below, not assumed. -/

/-- At the cumulative endpoint the artifact's window is this repository's
upper-strip window. -/
theorem zerosIn_zero_eq_stripZeroWindow (T : ℝ) :
    zerosIn 0 T = stripZeroWindow T := by
  rw [zerosIn_eq]
  rfl

/-- **The count bridge.**  The artifact's `N(T)`, a `finsum` of ζ-multiplicities
over its window, is this repository's `stripZeroCountMult T`, a `Finset.sum`
of ξ-multiplicities over the strip census. -/
theorem Ncount_eq_stripZeroCountMult (T : ℝ) :
    Ncount 0 T = stripZeroCountMult T := by
  rw [Ncount, zerosIn_zero_eq_stripZeroWindow,
    finsum_mem_eq_finite_toFinset_sum _ (stripZeroWindow_finite T)]
  unfold stripZeroCountMult
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact zeroMult_eq_xiOrderNat ((stripZeroWindow_finite T).mem_toFinset.mp hρ).1

/-! ## The registered census as a finset -/

/-- The artifact's distinct on-line count is the cardinality of this
repository's on-line strip finset. -/
theorem N0star_eq_onLineFinset_card (T : ℝ) :
    N0star 0 T = ((stripZeroFinset T).filter (fun ρ => ρ.re = 1 / 2)).card := by
  have hset : zerosIn 0 T ∩ {ρ : ℂ | ρ.re = 1 / 2}
      = (((stripZeroFinset T).filter (fun ρ => ρ.re = 1 / 2) : Finset ℂ) : Set ℂ) := by
    rw [zerosIn_zero_eq_stripZeroWindow]
    ext ρ
    constructor
    · rintro ⟨hw, hre⟩
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨(stripZeroWindow_finite T).mem_toFinset.mpr hw, hre⟩)
    · intro h
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h)
      exact ⟨(stripZeroWindow_finite T).mem_toFinset.mp h1, h2⟩
  rw [N0star, hset, Set.ncard_coe_finset]

/-! ## The complement restatement in the off-line coordinate

Nothing below this heading is new mathematics.  `N_off ≤ N − N₀*` is the
arithmetic complement of the artifact's lower bound; it is recorded because
the `S(t)` reading is convenient downstream. -/

/-- Distinct on-line zeros are at most the on-line count with multiplicity:
each of the `N₀*` zeros contributes at least `1` to the ledger, by positivity
of the analytic order at a nontrivial zero. -/
theorem N0star_le_onLineStripZeroCountMult (T : ℝ) :
    N0star 0 T ≤ onLineStripZeroCountMult T := by
  rw [N0star_eq_onLineFinset_card]
  unfold onLineStripZeroCountMult
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum ?_
  intro ρ hρ
  have hmem := (stripZeroWindow_finite T).mem_toFinset.mp (Finset.mem_filter.mp hρ).1
  exact ZD.xiOrderNat_pos_of_mem_NontrivialZeros hmem.1

/-- **The off-line census is eventually at most a third** — the artifact's
lower bound `N₀* ≥ (2/3 − ε)·N` restated in the off-line coordinate, and no
more than that: subtracting a floor on the registered count from the exact
total is the same statement, not a new one.

The exact split `stripZeroCountMult_eq_onLine_add_offLine` carries it with no
error term; the ε touches only the on-line summand. -/
theorem offLine_le_third : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (offLineStripZeroCountMult T : ℝ) ≤ (1 / 3 + ε) * (stripZeroCountMult T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := theoremA ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hA := hT₀ T hT
  have hN : (Ncount 0 T : ℝ) = (stripZeroCountMult T : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Ncount_eq_stripZeroCountMult T)
  have hline : (N0star 0 T : ℝ) ≤ (onLineStripZeroCountMult T : ℝ) := by
    exact_mod_cast N0star_le_onLineStripZeroCountMult T
  have hsplit : (stripZeroCountMult T : ℝ)
      = (onLineStripZeroCountMult T : ℝ) + (offLineStripZeroCountMult T : ℝ) := by
    exact_mod_cast stripZeroCountMult_eq_onLine_add_offLine T
  rw [hN] at hA
  have hoff : (offLineStripZeroCountMult T : ℝ)
      = (stripZeroCountMult T : ℝ) - (onLineStripZeroCountMult T : ℝ) := by linarith
  have hrhs : (1 / 3 + ε) * (stripZeroCountMult T : ℝ)
      = (stripZeroCountMult T : ℝ) - (2 / 3 - ε) * (stripZeroCountMult T : ℝ) := by ring
  rw [hoff, hrhs]
  linarith

/-- **The same bound in the `S(t)` coordinate.**  The gap between the
independently continued classical argument and the native registration
coordinate is exactly the off-line ledger
(`classicalSContour_eq_Smult_add_offLine`), so it inherits the bound: the
registration defect is eventually at most a third of the census. -/
theorem classicalSContour_sub_Smult_le_third :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ (T : ℝ) (hT : GoodHeight T), T₀ ≤ T →
      classicalSContour hT - Smult T ≤ (1 / 3 + ε) * (stripZeroCountMult T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := offLine_le_third ε hε
  refine ⟨T₀, fun T hT hTge => ?_⟩
  have hsplit := classicalSContour_eq_Smult_add_offLine hT
  have hbound := hT₀ T hTge
  rw [hsplit]
  linarith

/-! ## Notation transport into the source / Gram vocabulary

**Nothing in this section is new mathematics either.**  It is Theorem A
rewritten in this repository's source and Gram words, and the rewriting is a
change of notation, not of content.

Why it is only notation: `tauChi` is the identity
(`def tauChi (_χ) (y : ℝ) : ℝ := y`, `HarmonicPencilCell.lean`) — it discards
the character — so `reprPoint χ Z = 1/2 + i·log Z`, and since
`log : ℝ_{>0} → ℝ` is onto, the source predicate `∃ Z > 0, ρ = reprPoint χ Z`
is *definitionally* the critical-line predicate `Re ρ = 1/2` written in
geometric-height coordinates.  `sourcedWindow_eq_onLine` below proves exactly
that equality, and it is what makes `sourced_floor` a transport rather than a
result: `(2/3 − ε)·N(T) ≤ |sourcedWindow|` and `(2/3 − ε)·N(T) ≤ |on-line set|`
are the same statement with a synonym substituted.  The same applies to
`gram_event_floor`, since the Gram rank-drop is an `iff` with the L-zero
(`gramH_rank_drop_iff_L_zero`).

So this section carries **no mathematical content beyond Theorem A**, and in
particular the 2/3 here is not a statement about sources that was previously
unavailable — `EveryZeroHasSource` is all-or-nothing only because it
quantifies over *all* zeros, not because the per-zero predicate is deep.

What the theorems are prospectively good for, and no more: any downstream
machinery that consumes `sourcedWindow` or `gramEventWindow` can now be fed
Theorem A without re-deriving the ζ-to-χ bridge.  As of this writing **nothing
consumes them** — grepping `sourcedWindow` and `gramEventWindow` across
`RequestProject/` returns only this file, and nothing in the repository imports
`RequestProject.Zeta23Interface` at all.  They are kept as plumbing against a
future consumer, not as a result.

The one piece of real wiring here is that the census is ζ's while the source
vocabulary is stated for Dirichlet `L`-functions, so the two meet at the
modulus-one character, where Mathlib's
`DirichletCharacter.LFunction_modOne_eq` makes `L(·,χ)` literally
`riemannZeta`. -/

/-- A nontrivial zero of ζ in this repository's vocabulary is a nontrivial
zero of the modulus-one Dirichlet `L`-function, which *is* `riemannZeta`. -/
theorem nontrivialZeroChi_of_mem (χ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) : NontrivialZeroChi χ ρ := by
  obtain ⟨h0, h1, hz⟩ := hρ
  refine ⟨?_, h0, h1⟩
  rw [DirichletCharacter.LFunction_modOne_eq]
  exact hz

/-- **The sourced part of the window census**: the zeros through height `T`
that arise from a real source height, in the sense of `EveryZeroHasSource`.
By `sourcedWindow_eq_onLine` this is the on-line part of the window under
another name. -/
def sourcedWindow (χ : DirichletCharacter ℂ 1) (T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ stripZeroWindow T ∧ ∃ Z : ℝ, 0 < Z ∧ ρ = reprPoint χ Z}

/-- **Sourced = on-line, as sets.**  A represented point of a real height has
`re = 1/2` (`reprPoint_re`), and conversely `Z = exp(Im ρ)` sources an on-line
zero (`zero_source_admissibility`).  Because `tauChi` is the identity and
`log` is onto `ℝ`, this is not a correspondence between two notions but the
*same* set under two names.

This equality is the honest measure of everything below it: it is why
`sourced_floor` transports Theorem A rather than adding to it. -/
theorem sourcedWindow_eq_onLine (χ : DirichletCharacter ℂ 1) (T : ℝ) :
    sourcedWindow χ T
      = (((stripZeroFinset T).filter (fun ρ => ρ.re = 1 / 2) : Finset ℂ) : Set ℂ) := by
  ext ρ
  constructor
  · rintro ⟨hw, Z, _, hZ⟩
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨(stripZeroWindow_finite T).mem_toFinset.mpr hw, ?_⟩)
    rw [hZ]
    exact reprPoint_re χ Z
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h)
    have hw := (stripZeroWindow_finite T).mem_toFinset.mp h1
    obtain ⟨Z, hZpos, _, hZ⟩ :=
      zero_source_admissibility χ ρ (nontrivialZeroChi_of_mem χ hw.1) h2
    exact ⟨hw, Z, hZpos, hZ⟩

/-- The sourced census is exactly the artifact's `N₀*`. -/
theorem sourcedWindow_ncard (χ : DirichletCharacter ℂ 1) (T : ℝ) :
    (sourcedWindow χ T).ncard = N0star 0 T := by
  rw [sourcedWindow_eq_onLine, Set.ncard_coe_finset, N0star_eq_onLineFinset_card]

/-- **The ceiling, for contrast.**  One cannot register more zeros than
exist: the sourced census never exceeds the full census, with no hypothesis
and no analysis.  This is the entire content of the "upper side" of the
registered census, and it is why only the floor was ever the question — and
why `sourced_floor` reaching this bound, rather than any larger constant below
it, is what RH would say. -/
theorem sourcedWindow_ncard_le_census (χ : DirichletCharacter ℂ 1) (T : ℝ) :
    (sourcedWindow χ T).ncard ≤ stripZeroCountMult T := by
  rw [sourcedWindow_ncard]
  refine (N0star_le_onLineStripZeroCountMult T).trans ?_
  rw [stripZeroCountMult_eq_onLine_add_offLine]
  exact Nat.le_add_right _ _

/-- **A floor on the source census.**  At least `(2/3 − ε)` of the window
census has a source: there are at least that many zeros through height `T`
that arise from a real source height `Z > 0` through `ρ = reprPoint χ Z`.

**This is Theorem A with a synonym substituted, not a new result.**  By
`sourcedWindow_eq_onLine` the set counted here *is* the on-line set, because
`tauChi` is the identity and `log` is onto; so this inequality and the
artifact's `N₀* ≥ (2/3 − ε)·N` are the same statement in different words.  It
is recorded so that a consumer written against the source vocabulary can use
Theorem A directly; see the section header for the (currently empty) list of
such consumers.

Framing, unchanged by the above: this is a *floor*.  The ceiling is
`stripZeroCountMult T` itself and is trivial
(`sourcedWindow_ncard_le_census`), and saturation of the floor at that
ceiling — not a larger constant below it — is what
`grh_iff_spectral_gram_registration` states. -/
theorem sourced_floor (χ : DirichletCharacter ℂ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (2 / 3 - ε) * (stripZeroCountMult T : ℝ) ≤ ((sourcedWindow χ T).ncard : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := theoremA ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hA := hT₀ T hT
  have hN : (Ncount 0 T : ℝ) = (stripZeroCountMult T : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Ncount_eq_stripZeroCountMult T)
  rw [hN] at hA
  rw [sourcedWindow_ncard]
  exact hA

/-- **The spectral Gram events of the window census**: the zeros through
height `T` at which the harmonic-cell Gram pencil rank-drops at a real source
height whose represented point is the zero. -/
def gramEventWindow (χ : DirichletCharacter ℂ 1) (μ lam : ℂ) (T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ stripZeroWindow T ∧ ∃ Z : ℝ, ρ = reprPoint χ Z ∧ (GramH χ Z μ lam).det = 0}

/-- The Gram-event census is finite: it sits inside the strip window. -/
theorem gramEventWindow_finite (χ : DirichletCharacter ℂ 1) (μ lam : ℂ) (T : ℝ) :
    (gramEventWindow χ μ lam T).Finite :=
  (stripZeroWindow_finite T).subset (fun _ h => h.1)

/-- Every on-line window zero is a spectral Gram event.  This is
`L_zero_imp_spectral_gram_event` verbatim — it is already per-zero and already
takes `hcrit : ρ.re = 1/2` as its hypothesis, so it applies unchanged to
whichever subset the artifact's floor hands us. -/
theorem onLine_subset_gramEventWindow (χ : DirichletCharacter ℂ 1) (μ lam : ℂ)
    (hlam : lam ≠ μ) (T : ℝ) :
    (((stripZeroFinset T).filter (fun ρ => ρ.re = 1 / 2) : Finset ℂ) : Set ℂ)
      ⊆ gramEventWindow χ μ lam T := by
  intro ρ h
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp h)
  have hw := (stripZeroWindow_finite T).mem_toFinset.mp h1
  have hL : DirichletCharacter.LFunction χ ρ = 0 :=
    (nontrivialZeroChi_of_mem χ hw.1).1
  exact ⟨hw, L_zero_imp_spectral_gram_event χ ρ μ lam hlam h2 hL⟩

/-- **A floor on the spectral Gram events.**  At least `(2/3 − ε)` of the
window census is a rank-drop of the harmonic-cell Gram pencil at a real source
height.  The diagonal calibration is required admissible (`hlam : lam ≠ μ`),
as everywhere in the cell layer.

**Also a transport, not a new result**: `gramH_rank_drop_iff_L_zero` makes the
rank-drop an `iff` with the L-zero at the represented height, so — as with
`sourced_floor` — the set counted here is again the on-line set under a third
name, and the content is still Theorem A's. -/
theorem gram_event_floor (χ : DirichletCharacter ℂ 1) (μ lam : ℂ) (hlam : lam ≠ μ) :
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (2 / 3 - ε) * (stripZeroCountMult T : ℝ)
        ≤ ((gramEventWindow χ μ lam T).ncard : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := sourced_floor χ ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  have hbound := hT₀ T hT
  have hle : (sourcedWindow χ T).ncard ≤ (gramEventWindow χ μ lam T).ncard := by
    rw [sourcedWindow_eq_onLine]
    exact Set.ncard_le_ncard (onLine_subset_gramEventWindow χ μ lam hlam T)
      (gramEventWindow_finite χ μ lam T)
  have hcast : ((sourcedWindow χ T).ncard : ℝ)
      ≤ ((gramEventWindow χ μ lam T).ncard : ℝ) := Nat.cast_le.mpr hle
  linarith

end CriticalLinePhasor.Zeta23

#print axioms CriticalLinePhasor.Zeta23.isNontrivialZero_iff_mem
#print axioms CriticalLinePhasor.Zeta23.zerosIn_eq
#print axioms CriticalLinePhasor.Zeta23.unregistered_minority
#print axioms CriticalLinePhasor.Zeta23.theoremA
#print axioms CriticalLinePhasor.Zeta23.unregistered_minority_uncond
#print axioms CriticalLinePhasor.Zeta23.zeroMult_eq_xiOrderNat
#print axioms CriticalLinePhasor.Zeta23.Ncount_eq_stripZeroCountMult
#print axioms CriticalLinePhasor.Zeta23.N0star_le_onLineStripZeroCountMult
#print axioms CriticalLinePhasor.Zeta23.offLine_le_third
#print axioms CriticalLinePhasor.Zeta23.classicalSContour_sub_Smult_le_third
#print axioms CriticalLinePhasor.Zeta23.nontrivialZeroChi_of_mem
#print axioms CriticalLinePhasor.Zeta23.sourcedWindow_eq_onLine
#print axioms CriticalLinePhasor.Zeta23.sourcedWindow_ncard_le_census
#print axioms CriticalLinePhasor.Zeta23.sourced_floor
#print axioms CriticalLinePhasor.Zeta23.gram_event_floor
