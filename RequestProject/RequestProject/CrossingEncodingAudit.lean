import RequestProject.CrossingInduction

/-!
# Auditing the crossing/zero-readout encoding (the "regime" question)

The review distinguishes two genuinely different conditionals and asks, for each, the only
question that matters once "this is RH-strength" is set aside as a thought-terminator:

> does the hypothesis *assume* RH, or is it *circular*?  If neither, it is a valid target.

This file records the result of actually **reading the definitions** rather than guessing, and
backs the verdict with machine-checked witnesses.

## 1. `midpoint_forcing` (the Weil / Frobenius balance) — status

`ChiralCup.midpoint_forcing` is already an **unconditional, fully-proved** theorem:

```
midpoint_forcing (q : ℝ) (hq : 1 < q) (s : ℂ) (h : ‖(q : ℂ) ^ s‖ ^ 2 = q) : s.re = 1 / 2
```

It does *not* assume RH and is *not* circular: it is the elementary observation that pinning the
modulus `‖q^s‖² = q` forces `Re s = ½`.  The mathematical content has been pushed entirely into
the **hypothesis** `‖α‖² = q` (the Weil/Frobenius balance `|α| = √q`).  Discharging that hypothesis
for a *genuine* Frobenius eigenvalue is RH-for-curves (Weil/Deligne) — a theorem, not an open
problem, but absent from Mathlib, and only meaningful once `α`, `q` are the Frobenius eigenvalue and
the field cardinality of an *actual* curve over `𝔽_q`.  In the present code `α = q^s` is a
hand-built scalar, so the honest target is "build a genuine function-field L-function model and
formalize RH-for-curves", a large construction.  No claim about that is made here.

## 2. `CrossingsExhaustZeroReadout` — verdict: **structural and contingent**

Reading `CrossingInduction.lean`:

```
def CrossingsExhaustZeroReadout (C : CrossingHelix) : Prop := ‖C.fwd 0‖ = ‖C.rev 0‖
```

The "crossing object" (`fwd`, `rev`, `trans`) is a tuple of **arbitrary hand-built scalar
functions** `ℕ → ℂ` on a free-floating `CrossingHelix`; nothing in scope ties it to an L-function
or to any analytic zero set.  Therefore `CrossingsExhaustZeroReadout`, *as currently encoded*, is a
plain modulus equation about the helix's base multipliers.  Applying the review's test:

* It does **not assume RH** — it never mentions a zero set, an L-function, or `IsHB`.
* It is **not circular** — it is not defined in terms of the conclusion it feeds.
* But it also **does not yield RH for free**: because the helix is decoupled from any arithmetic
  object, the property is simply a *contingent structural* condition — true for some helices, false
  for others.  This is exactly the review's first regime ("rfl-level structural fact"), with the
  real content (a genuine bijection `crossing ↔ analytic zero`) still to be supplied.  That missing
  linkage is what would have to be *built*, and is not present.

The two `#check`-able witnesses below make this precise and machine-checked:

* `balancedHelix` satisfies all hypotheses with a real Frobenius weight `q = ‖2‖² = 4 > 1`, so
  `CrossingsExhaustZeroReadout` holds and the full crossing induction
  (`no_dominance_by_crossing_induction`) discharges **unconditionally** — confirming the hypothesis
  is dischargeable and structural, not RH-strength.
* `unbalancedHelix` *violates* `CrossingsExhaustZeroReadout` (`‖1‖ ≠ ‖2‖`), confirming the property
  is contingent: it is neither vacuous nor a theorem, hence carries no RH content by itself.

`Mathlib`-only, `sorry`/`axiom`-free.
-/

open Complex
open scoped ComplexConjugate
open CriticalLinePhasor.ChiralCup

namespace CriticalLinePhasor.CrossingInduction
noncomputable section

/-! ## A concrete *balanced* helix with a genuine Frobenius weight `q = 4 > 1` -/

/-- A concrete crossing helix: one nonzero fibre, forward and reverse multipliers `2^n` (equal
moduli), and constant height-transport multiplier `2`, so the Frobenius weight is `q = ‖2‖² = 4`. -/
def balancedHelix : CrossingHelix where
  fibre := Finsupp.single 0 1
  fwd := fun n => (2 : ℂ) ^ n
  rev := fun n => (2 : ℂ) ^ n
  trans := fun _ => (2 : ℂ)

theorem balancedHelix_positiveCup : PositiveFrobeniusCup balancedHelix := by
  constructor
  · simp [balancedHelix]
  · intro n; simp [balancedHelix]

theorem balancedHelix_transport : WeightedForwardReverseTransport balancedHelix := by
  constructor
  · intro n; simp [balancedHelix, pow_succ]; ring
  · intro n; simp only [balancedHelix, map_ofNat, pow_succ]; ring

theorem balancedHelix_exhaust : CrossingsExhaustZeroReadout balancedHelix := by
  simp [balancedHelix, CrossingsExhaustZeroReadout]

/-- The Frobenius weight carried at every height of `balancedHelix` is `q = 4 > 1`. -/
theorem balancedHelix_frobenius_weight (n : ℕ) :
    ‖balancedHelix.trans n‖ ^ 2 = 4 := by
  simp [balancedHelix]; norm_num

/-- **The hypothesis is dischargeable and structural.**  For the concrete `balancedHelix` the entire
crossing induction goes through with no extra assumptions: every crossing is balanced. -/
theorem balancedHelix_no_dominance :
    NoChiralDominanceAtAllCrossings balancedHelix :=
  no_dominance_by_crossing_induction balancedHelix
    balancedHelix_positiveCup balancedHelix_transport balancedHelix_exhaust

/-! ## A concrete helix that *violates* the readout — the property is contingent -/

/-- A crossing helix whose base readout is unbalanced: `‖fwd 0‖ = 1 ≠ 2 = ‖rev 0‖`. -/
def unbalancedHelix : CrossingHelix where
  fibre := Finsupp.single 0 1
  fwd := fun _ => (1 : ℂ)
  rev := fun _ => (2 : ℂ)
  trans := fun _ => (1 : ℂ)

/-- **The property is contingent (not RH-encoding, not vacuous).**  `CrossingsExhaustZeroReadout`
fails for `unbalancedHelix`, since `‖1‖ ≠ ‖2‖`. -/
theorem unbalancedHelix_not_exhaust :
    ¬ CrossingsExhaustZeroReadout unbalancedHelix := by
  simp [unbalancedHelix, CrossingsExhaustZeroReadout]

end
end CriticalLinePhasor.CrossingInduction
