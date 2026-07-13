import RequestProject.JordanDriftTower

/-!
# The Hodge dial: the terminus architecture, machine-checked

The companion paper's terminus reads the Hodge conjecture in the carrier frame as
**source exhaustion on the clock's fixed axis**: every rational DC mode has an algebraic
source.  This file fixes that architecture the way `HelixResolventCapture` fixed the GRH
part's: the reduction spine is **unconditional**, and the open content is isolated into two
named hypotheses -- exactly the two ingredients the program has been measuring:

* **`Retention`** -- no silent rational DC mode: every nonzero rational DC class fires at
  some finite tower level (the detection direction; the ledger keeps enough to separate).
  On the semisimple model this is **already a theorem** (`momentTower_exhaustive`), and the
  instantiation below consumes it: on model states the terminus needs `Recognition` alone.
* **`Recognition`** -- every fired rational DC class has an algebraic source (the converse
  leg: detection -> alignment -> construction -> exact landing; closed at grade one by
  Gross--Zagier/Kolyvagin, run in-house by `tmp/heegner_recognition.py`; open above).

`hodge_of_retention_recognition` is then the machine-checked reduction: the two hypotheses
together give source exhaustion.  The theorem is logic glue -- its value, as with the GRH
spine, is that the *architecture* is kernel-fixed: any future landing of either ingredient
composes into the terminus with no further argument.  Nothing here asserts either
hypothesis; nothing here proves the Hodge conjecture.  No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The Hodge dial**: an abstract class space carrying the four data of the terminus ---
the DC (clock-fixed, type-`(p,p)`) condition, rationality, an algebraic-source predicate,
and the tower readouts.  Instances range from the finite model (below, where `Retention`
is proven) to the arithmetic dials the instruments measure. -/
structure HodgeDial (Z : Type*) [Zero Z] where
  /-- the clock-fixed (DC / type-`(p,p)`) condition. -/
  DC : Z → Prop
  /-- rationality of the class. -/
  Rational : Z → Prop
  /-- the class has an algebraic source. -/
  Algebraic : Z → Prop
  /-- the tower readouts. -/
  T : ℕ → Z → ℂ

variable {Z : Type*} [Zero Z]

/-- **Source exhaustion** -- the Hodge conjecture in the carrier frame: every nonzero
rational DC mode has an algebraic source. -/
def SourceExhaustion (D : HodgeDial Z) : Prop :=
  ∀ z : Z, z ≠ 0 → D.DC z → D.Rational z → D.Algebraic z

/-- **Retention** (the detection ingredient): no nonzero rational DC mode is silent at
every tower level. -/
def Retention (D : HodgeDial Z) : Prop :=
  ∀ z : Z, z ≠ 0 → D.DC z → D.Rational z → ∃ d, D.T d z ≠ 0

/-- **Recognition** (the converse-leg ingredient): every fired rational DC mode has an
algebraic source. -/
def Recognition (D : HodgeDial Z) : Prop :=
  ∀ z : Z, (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z → D.Algebraic z

/-- **The terminus reduction, unconditional**: retention and recognition together give
source exhaustion.  The architecture of the Hodge program, kernel-fixed. -/
theorem hodge_of_retention_recognition {D : HodgeDial Z}
    (hret : Retention D) (hrec : Recognition D) : SourceExhaustion D :=
  fun z hz hdc hrat => hrec z (hret z hz hdc hrat) hdc hrat

/-- Retention is exactly exhaustion relativized to the rational DC locus; in particular a
tower that is `Exhaustive` on all of `Z` retains. -/
theorem retention_of_exhaustive {D : HodgeDial Z}
    (hex : Exhaustive D.T) : Retention D :=
  fun z hz _ _ => hex z hz

/-- **The model dial**: the semisimple carrier state with the moment tower, every class
counted as DC and rational (the worst case for retention), and an arbitrary source
predicate.  Retention is the PROVEN Vandermonde separation, so on the model the terminus
needs recognition alone. -/
def modelDial {m : ℕ} (lam : Fin m → ℂ) (Alg : (Fin m → ℂ) → Prop) :
    HodgeDial (Fin m → ℂ) where
  DC _ := True
  Rational _ := True
  Algebraic := Alg
  T d c := ∑ i, c i * (lam i) ^ d

/-- **On the model, source exhaustion reduces to recognition alone** -- retention is
unconditional (`momentTower_detects`/`momentTower_exhaustive`). -/
theorem model_sourceExhaustion_of_recognition {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) (Alg : (Fin m → ℂ) → Prop)
    (hrec : Recognition (modelDial lam Alg)) :
    SourceExhaustion (modelDial lam Alg) :=
  hodge_of_retention_recognition
    (retention_of_exhaustive (momentTower_exhaustive lam hdistinct)) hrec

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_of_retention_recognition
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.model_sourceExhaustion_of_recognition
