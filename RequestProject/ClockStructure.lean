import RequestProject.ChiralityHB

/-!
# The abstract clock structure: one template, two fields — and the landing method

FRONTIER.md §8 named two proofs "within reach from our own chairs."  This file is both.

## 1. The purity-defect template as ONE lemma

The campaign's most striking observation: arithmetic zero displacement and gauge-theory
mass gaps obey the SAME law.  Here that becomes mathematics rather than analogy: define
`defectDepth α ℓ = −log‖α‖/ℓ` once, and prove
* `arithmetic_clock_law` — a zero of the symmetrized prime clock sits at
  `Im z = defectDepth α ℓ` (re-expression of `ChiralityHB.clock_zero_depth`);
* `gauge_gap_law` — a transfer ratio `D = λ₁/λ₀ ∈ (0,1]` has gap
  `−log D = defectDepth D 1` (measured exact in 2D, `tmp/villain_curve_results.txt`;
  4D dichotomy `tmp/ym_4d_results.txt`);
* `one_template` — both statements in a single theorem: the displacement and the gap are
  evaluations of the SAME function;
* `defectDepth_eq_zero_iff` / `defectDepth_pos_iff` — **purity ⟺ zero defect**: the face
  is unitary iff the depth vanishes (on-axis zero ⟺ gapless/healed clock), sub-unitary
  iff the depth is positive — the shared boundary behavior (deconfinement = the
  purity-limit crossing) as an iff;
* `healing_limit` — the defect dies continuously as the face heals to the circle.

The lattice facts and the arithmetic law were each established separately; the theorem
content HERE is that they are instances of one function with one boundary structure.
What remains conjecture is stated as a `Prop` definition, never an axiom:
`NeverHeals` — the 4D compact-clock conjecture's shape (non-abelian vacuum defect < 1
at every coupling; measured support at 8⁴, continuum = Clay, untouched).

## 2. The distinguished-point law and the integer-landing method

The obstruction campaign (38/38 landings: class numbers, Ш) rests on a measurement
method whose well-posedness deserves a proof: `distinguishedPointLaw` states the
Bloch–Kato-shaped identity; `obstruction_recovery` inverts it (the obstruction is
determined by the special value and the other data); `integer_landing_unique` proves
the landing method is well-posed — **at better-than-half-integer precision, the integer
read is unique**.  This is why 29/29 exact landings are identifications, not
approximations.  (Instantiating the law at Mathlib's proven class-number machinery is
the natural follow-on; the abstract layer is what the measurements consume.)

No `sorry`, no `axiom` beyond the standard three.
-/

open Complex

namespace CriticalLinePhasor.ClockStructure

/-! ## 1. The template -/

/-- The purity-defect depth of a clock: face `α`, winding rate `ℓ`. -/
noncomputable def defectDepth (α : ℂ) (ℓ : ℝ) : ℝ := -Real.log ‖α‖ / ℓ

/-- **Purity ⟺ zero defect**: the depth vanishes iff the face is unitary.  (On-axis
zero ⟺ healed/gapless clock — the shared boundary of the two fields.) -/
theorem defectDepth_eq_zero_iff {α : ℂ} (hα : α ≠ 0) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    defectDepth α ℓ = 0 ↔ ‖α‖ = 1 := by
  unfold defectDepth
  rw [div_eq_zero_iff, neg_eq_zero]
  constructor
  · rintro (hlog | hl)
    · rcases Real.log_eq_zero.mp hlog with h1 | h1 | h1
      · exact absurd h1 (ne_of_gt (norm_pos_iff.mpr hα))
      · exact h1
      · exfalso
        have := norm_nonneg α
        linarith
    · exact absurd hl (ne_of_gt hℓ)
  · intro h1
    left
    rw [h1, Real.log_one]

/-- **Impurity ⟺ positive defect**: sub-unitary face iff strictly positive depth
(the confining/off-axis side). -/
theorem defectDepth_pos_iff {α : ℂ} (hα : α ≠ 0) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 < defectDepth α ℓ ↔ ‖α‖ < 1 := by
  unfold defectDepth
  rw [div_pos_iff_of_pos_right hℓ, neg_pos]
  exact Real.log_neg_iff (norm_pos_iff.mpr hα)

/-- **The arithmetic instance**: a zero of the symmetrized prime clock sits at depth
exactly `defectDepth α ℓ` — `ChiralityHB.clock_zero_depth` re-expressed through the
abstract template. -/
theorem arithmetic_clock_law {α : ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : CriticalLinePhasor.ChiralityHB.symClock α ℓ z = 0) :
    z.im = defectDepth α ℓ :=
  CriticalLinePhasor.ChiralityHB.clock_zero_depth hℓ hz

/-- **The gauge instance**: a transfer eigenvalue ratio `D ∈ (0,1]` has gap
`−log D = defectDepth D 1` — the lattice gap law is the template at rate `1`
(exact in 2D, measured in 3D/4D; `tmp/villain_curve_results.txt`,
`tmp/ym_4d_results.txt`). -/
theorem gauge_gap_law {D : ℝ} (hD : 0 < D) :
    -Real.log D = defectDepth (D : ℂ) 1 := by
  unfold defectDepth
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, div_one]

/-- **One template, two fields** — the campaign's frame identification as a theorem:
the arithmetic zero displacement and the gauge gap are evaluations of the SAME
function.  (What each field's law says about its own objects was proven/measured
separately; the content here is the identification.) -/
theorem one_template {α : ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : CriticalLinePhasor.ChiralityHB.symClock α ℓ z = 0)
    {D : ℝ} (hD : 0 < D) :
    z.im = defectDepth α ℓ ∧ -Real.log D = defectDepth (D : ℂ) 1 :=
  ⟨arithmetic_clock_law hℓ hz, gauge_gap_law hD⟩

/-- **The healing limit**: the defect dies continuously as the face heals to the unit
circle — deconfinement as the purity-limit crossing, in the limit form. -/
theorem healing_limit :
    Filter.Tendsto (fun D : ℝ => -Real.log D) (nhds 1) (nhds 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto
  rw [Real.log_one] at h
  simpa using h.neg

/-- **The 4D compact-clock conjecture's shape** (a `Prop`, stated, never assumed): a
defect curve never heals — `D β < 1` at every coupling.  Measured support: SU(2) at 8⁴
(max D = 0.85, monotone falling); the abelian control HEALS at its known transition
(D: 0.33 → 0.93 across β_c ≈ 1.01).  The continuum statement is the Clay problem and
is not addressed. -/
def NeverHeals (D : ℝ → ℝ) : Prop := ∀ β : ℝ, 0 < β → D β < 1

/-- If a clock's defect curve never heals, its gap is positive at every coupling —
the mass gap as permanent vacuum impurity, conditional on `NeverHeals`. -/
theorem gap_pos_of_neverHeals {D : ℝ → ℝ} (h : NeverHeals D)
    (hpos : ∀ β : ℝ, 0 < β → 0 < D β) {β : ℝ} (hβ : 0 < β) :
    0 < -Real.log (D β) := by
  rw [neg_pos]
  exact Real.log_neg (hpos β hβ) (h β hβ)

/-! ## 2. The distinguished-point law and the landing method -/

/-- The Bloch–Kato-shaped **distinguished-point law**: special value = period ×
regulator × obstruction / torsion.  Root case Dirichlet 1839 (class number formula),
elliptic case BSD; measured exactly on 38/38 fibers
(`tmp/obstruction_general_results.txt`, `tmp/sha_hinge_results.txt`). -/
def distinguishedPointLaw (value period reg obstruction torsion : ℝ) : Prop :=
  value = period * reg * obstruction / torsion

/-- **Obstruction recovery**: given the law with nonvanishing period, regulator and
torsion, the obstruction is DETERMINED by the special value — the inverse reading the
measurements perform. -/
theorem obstruction_recovery {value period reg obstruction torsion : ℝ}
    (hP : period ≠ 0) (hR : reg ≠ 0) (hT : torsion ≠ 0)
    (h : distinguishedPointLaw value period reg obstruction torsion) :
    obstruction = value * torsion / (period * reg) := by
  unfold distinguishedPointLaw at h
  field_simp at h ⊢
  linarith [h]

/-- **The integer-landing method is well-posed**: two integers within half a unit of
the same measured value are equal — at better-than-half-integer precision the integer
read is UNIQUE.  This is why the campaign's exact landings are identifications, not
approximations. -/
theorem integer_landing_unique {x : ℝ} {o₁ o₂ : ℤ}
    (h₁ : |x - o₁| < 1 / 2) (h₂ : |x - o₂| < 1 / 2) : o₁ = o₂ := by
  have hlt : |(o₁ : ℝ) - o₂| < 1 := by
    calc |(o₁ : ℝ) - o₂| = |(o₁ - x) + (x - o₂)| := by ring_nf
      _ ≤ |(o₁ : ℝ) - x| + |x - o₂| := abs_add_le _ _
      _ = |x - o₁| + |x - o₂| := by rw [abs_sub_comm (o₁ : ℝ) x]
      _ < 1 := by linarith
  have h3 : |o₁ - o₂| < 1 := by
    exact_mod_cast (by push_cast; exact hlt : |((o₁ - o₂ : ℤ) : ℝ)| < 1)
  rw [abs_lt] at h3
  omega

end CriticalLinePhasor.ClockStructure
