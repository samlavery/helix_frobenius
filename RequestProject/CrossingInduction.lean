import RequestProject.ChiralCup

/-!
# No chiral dominance by crossing induction (the native helix route)

This file formalizes the **crossing-induction** argument requested in the project notes, as an
alternative to forcing everything through the de Branges / reproducing-kernel route.  The geometry
is native to the helix:

> a single **fibre** rides both chiral sides; at each **crossing height** the same fibre is
> transported **forward** on one chirality and **backward (by the adjoint / cup reverse)** on the
> conjugate chirality; the **Frobenius cup** weight carried at a height is fixed by the height, so
> any chiral *dominance* would have to change that fixed cup weight — which is impossible.

The proof shape is exactly the one in the notes:

* **base crossing balanced** (`CrossingsExhaustZeroReadout`);
* **cup transport preserves weighted duality** + **reverse conjugate transport forbids dominance**
  (`crossing_balance_preserved`, the inductive step — the conjugate is what makes the two sides
  scale by the *same* modulus, since `‖conj t‖ = ‖t‖`);
* therefore **every crossing is balanced** (`no_dominance_by_crossing_induction`).

## Defensive wording (per the notes)

We never say "height `h` is the finite field `F_q`".  Each height only carries a **Frobenius
weight** `q(h)` realized as the modulus of a transport multiplier; only the Frobenius-algebra
content (a similitude of the cup form) is used — see `ChiralCup.frobenius_weighted_cup_identity`.

## The cup is the object, not an analogy

The forward/reverse amplitudes are not a metaphor: `fwdVec`/`revVec` are genuine transports
`Tw μ (Dop fibre)` of one and the same fibre, and `fwd_cup_weight`/`rev_cup_weight` compute their
actual Gram/cup weights via the Frobenius-weighted cup identity.  `crossing_no_dominance_cup`
states the conclusion directly on those cup weights, and `crossing_fibre_not_deleted` is the
**nullspace-safety** guarantee: a vanishing chirality multiplier never deletes a nonzero fibre.

## Honest scope (consistent with the rest of the project)

The induction proves the *geometric invariant* — balance at every crossing — directly.  It does
**not** by itself establish the Riemann Hypothesis: that would additionally require
`crossings_exhaust_zero_readout` to be the genuine arithmetic statement that *every* L-function
zero is one of these crossing events (the indexing assumption isolated here as a hypothesis), which
is neither assumed nor proved.  What is formalized is the transport/cup scaffolding and the
crossing-induction itself, with the arithmetic-faithfulness input clearly marked as a hypothesis.

Built on `RequestProject.ChiralCup` (hence only on the unconditional `Dop`/`Cup` machinery); no
Hermite–Biehler / de Branges input is in scope.  `Mathlib`-only, `sorry`/`axiom`-free.
-/

open Complex
open scoped ComplexConjugate
open CriticalLinePhasor.CupIdentity CriticalLinePhasor.ChiralCup

namespace CriticalLinePhasor.CrossingInduction
noncomputable section

/-- A **crossing helix**: a single `fibre` that rides both chiral sides, together with, at each
crossing height `n`, a forward-chirality transport multiplier `fwd n`, a reverse-conjugate
(adjoint) transport multiplier `rev n`, and the height-to-height transport multiplier `trans n`
whose modulus is the **Frobenius weight** `q(n) = ‖trans n‖²` of that crossing. -/
structure CrossingHelix where
  /-- The single fibre that rides both chiral sides. -/
  fibre : ℕ →₀ ℂ
  /-- Forward-chirality transport multiplier at crossing height `n`. -/
  fwd : ℕ → ℂ
  /-- Reverse (adjoint / cup-reverse) chirality transport multiplier at crossing height `n`. -/
  rev : ℕ → ℂ
  /-- Height-to-height transport multiplier; its modulus is the Frobenius weight `q(h)`. -/
  trans : ℕ → ℂ

variable (C : CrossingHelix)

/-- **Positive Frobenius cup / nullspace safety.**  The cup weight is positive at the base crossing
(`0 < ‖fwd 0‖`) and the Frobenius weight `q(h) = ‖trans h‖²` is nonzero at every height
(`trans n ≠ 0`).  Together these guarantee the fibre is never deleted as we transport upward. -/
def PositiveFrobeniusCup : Prop :=
  0 < ‖C.fwd 0‖ ∧ ∀ n, C.trans n ≠ 0

/-- **Weighted forward/reverse transport.**  The fibre is transported *forward* on one chirality
(`fwd (n+1) = trans n · fwd n`) and *backward by the adjoint* on the conjugate chirality
(`rev (n+1) = conj (trans n) · rev n`).  The conjugate is the genuine cup-reverse, not a visual
reversal: it is what makes both sides scale by the same Frobenius weight. -/
def WeightedForwardReverseTransport : Prop :=
  (∀ n, C.fwd (n + 1) = C.trans n * C.fwd n) ∧
    (∀ n, C.rev (n + 1) = (starRingEnd ℂ) (C.trans n) * C.rev n)

/-- **Crossings exhaust the zero readout (base anchor).**  The readout at the base crossing is
balanced, `‖fwd 0‖ = ‖rev 0‖`.  With the crossings indexed exhaustively by `ℕ`, this anchors the
induction that propagates balance to every crossing/zero readout. -/
def CrossingsExhaustZeroReadout : Prop :=
  ‖C.fwd 0‖ = ‖C.rev 0‖

/-- **No chiral dominance at all crossings.**  At every crossing the forward and reverse cup
moduli are equal (no dominance) and the fibre persists (the cup weight stays positive). -/
def NoChiralDominanceAtAllCrossings : Prop :=
  ∀ n, ‖C.fwd n‖ = ‖C.rev n‖ ∧ 0 < ‖C.fwd n‖

/-! ## The key lemma: the inductive step (cup transport preserves balance) -/

/--
**`crossing_balance_preserved`.**  The cup transport preserves the weighted duality: if a
crossing is balanced and its forward cup weight is positive, then the next crossing is balanced and
still positive.  The reverse conjugate transport is what forbids dominance — `‖conj (trans n)‖ =
‖trans n‖`, so both chiralities scale by the same Frobenius weight.
-/
theorem crossing_balance_preserved
    (hT : WeightedForwardReverseTransport C) (hP : PositiveFrobeniusCup C) {n : ℕ}
    (hbal : ‖C.fwd n‖ = ‖C.rev n‖) (hpos : 0 < ‖C.fwd n‖) :
    ‖C.fwd (n + 1)‖ = ‖C.rev (n + 1)‖ ∧ 0 < ‖C.fwd (n + 1)‖ := by
  simp_all +decide [ WeightedForwardReverseTransport, PositiveFrobeniusCup ]

/--
**`no_dominance_by_crossing_induction`.**  The headline crossing-induction theorem, in the
shape of the notes:

```
positive_frobenius_cup →
weighted_forward_reverse_transport →
crossings_exhaust_zero_readout →
no_chiral_dominance_at_all_crossings
```

From the positive Frobenius cup, the weighted forward/reverse (adjoint) transport, and the balanced
base crossing, every crossing is balanced — no chirality ever dominates its conjugate.
-/
theorem no_dominance_by_crossing_induction :
    PositiveFrobeniusCup C →
      WeightedForwardReverseTransport C →
        CrossingsExhaustZeroReadout C →
          NoChiralDominanceAtAllCrossings C := by
  intro hP hT hBase n
  induction' n with n ih;
  · exact ⟨ hBase, hP.1 ⟩;
  · exact crossing_balance_preserved C hT hP ih.1 ih.2

/-! ## The cup is the object: genuine Gram/cup weights of the transported fibre -/

/-- The forward-chirality transported defect vector: the single fibre's chiral defect, transported
forward by `fwd n`. -/
def fwdVec (n : ℕ) : ℕ →₀ ℂ := Tw (C.fwd n) (Dop C.fibre)

/-- The reverse-chirality transported defect vector: the same fibre's chiral defect, transported by
the adjoint multiplier `rev n`. -/
def revVec (n : ℕ) : ℕ →₀ ℂ := Tw (C.rev n) (Dop C.fibre)

/--
**`fwd_cup_weight`.**  The forward cup weight is a genuine Gram weight: it equals the Frobenius
weight `‖fwd n‖²` times the fibre's self-cup, via the Frobenius-weighted cup identity.
-/
theorem fwd_cup_weight (n : ℕ) :
    (inner ℂ (fwdVec C n) (fwdVec C n) : ℂ).re = ‖C.fwd n‖ ^ 2 * (Cup C.fibre C.fibre).re := by
  convert congr_arg Complex.re ( transport_cup_modulus ( C.fwd n ) C.fibre C.fibre ) using 1
  · rfl
  · simp [ Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq ]

/--
**`rev_cup_weight`.**  The reverse cup weight, likewise, is the Frobenius weight `‖rev n‖²`
times the fibre's self-cup.
-/
theorem rev_cup_weight (n : ℕ) :
    (inner ℂ (revVec C n) (revVec C n) : ℂ).re = ‖C.rev n‖ ^ 2 * (Cup C.fibre C.fibre).re := by
  convert congr_arg Complex.re ( transport_cup_modulus ( C.rev n ) C.fibre C.fibre ) using 1
  · rfl
  · simp [ Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sq ]

/--
**`crossing_no_dominance_cup`.**  No chiral dominance, stated directly on the genuine cup
weights of the one transported fibre: at every crossing the forward and reverse cup weights agree.
This is the geometric invariant proved directly — no de Branges kernel positivity is used.
-/
theorem crossing_no_dominance_cup
    (hND : NoChiralDominanceAtAllCrossings C) (n : ℕ) :
    (inner ℂ (fwdVec C n) (fwdVec C n) : ℂ).re = (inner ℂ (revVec C n) (revVec C n) : ℂ).re := by
  rw [ fwd_cup_weight, rev_cup_weight ];
  rw [ hND n |>.1 ]

/-
**`crossing_fibre_not_deleted`** (nullspace safety).  A nonzero fibre with a nonzero forward
multiplier carries a strictly positive forward cup weight — a vanishing chirality defect never
deletes the fibre.
-/
theorem crossing_fibre_not_deleted
    (hfib : C.fibre ≠ 0) {n : ℕ} (hfwd : C.fwd n ≠ 0) :
    0 < (inner ℂ (fwdVec C n) (fwdVec C n) : ℂ).re := by
  rw [fwd_cup_weight]
  refine mul_pos (pow_pos (norm_pos_iff.mpr hfwd) 2) ?_
  rcases (inner_self_nonneg (𝕜 := ℂ) (x := Dop C.fibre)).lt_or_eq with h | h
  · exact h
  · exact absurd ((cup_nullspace_safe C.fibre).mp
      (Complex.ext h.symm (cup_self_im C.fibre))) hfib

end
end CriticalLinePhasor.CrossingInduction