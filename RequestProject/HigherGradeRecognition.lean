import RequestProject.RecognitionBridge

/-!
# Typed source construction and recognition above grade one

`RecognitionBridge.recognizedCycle` already constructs a cycle from a detected carrier fiber and
`recognition_closes` certifies that cycle.  This file connects that certificate to the source
predicate of a `HodgeDial` without replacing either proof.

The bridge is packaged with an algebraic realization map from cycles to dial states, an exact
landing theorem for recognized cycles, and a detector for fired rational DC states above grade
one.  The resulting source is an explicit term.  A second typed constructor covers grades zero
and one; the grade split then proves the dial's full `Recognition` theorem.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {Z : Type*} [Zero Z]

/-- A source type together with its realization in a Hodge dial.  Algebraicity is attached to
the realized source itself, rather than supplied later as a bare proposition. -/
structure AlgebraicSourceRealization (D : HodgeDial Z) (Source : Type*) where
  realize : Source → Z
  algebraic_realize : ∀ source, D.Algebraic (realize source)

/-- The complete higher-grade recognition datum.  It combines the existing radial--Torelli--cycle
bridge with the exact arithmetic landing of its cycle in the dial state. -/
structure HigherGradeRecognitionPackage
    (D : HodgeDial Z)
    (AngularDossier RadialDossier Curve Cycle IsogClass : Type*) where
  grade : Z → ℕ
  bridge : RecognitionBridge Z AngularDossier RadialDossier Curve Cycle IsogClass
  sourceRealization : AlgebraicSourceRealization D Cycle
  detected_of_fired_above_one :
    ∀ z, (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z → 1 < grade z → bridge.Detected z
  realizes_of_recognizes :
    ∀ source z, bridge.Recognizes source z → sourceRealization.realize source = z

variable {D : HodgeDial Z}
variable {AngularDossier RadialDossier Curve Cycle IsogClass : Type*}

/-- The explicit higher-grade algebraic source: radial reading, Torelli reconstruction, then the
cycle constructor already carried by `RecognitionBridge`. -/
def HigherGradeRecognitionPackage.source
    (P : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    (z : Z) : Cycle :=
  P.bridge.recognizedCycle z

/-- The constructed higher-grade source carries the bridge's recognition certificate. -/
theorem HigherGradeRecognitionPackage.source_recognizes
    (P : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    (z : Z) (hfired : ∃ d, D.T d z ≠ 0) (hdc : D.DC z) (hrat : D.Rational z)
    (hgrade : 1 < P.grade z) :
    P.bridge.Recognizes (P.source z) z :=
  recognition_closes P.bridge z (P.detected_of_fired_above_one z hfired hdc hrat hgrade)

/-- The source constructor with its recognition proof retained in the term. -/
def HigherGradeRecognitionPackage.certifiedSource
    (P : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    (z : Z) (hfired : ∃ d, D.T d z ≠ 0) (hdc : D.DC z) (hrat : D.Rational z)
    (hgrade : 1 < P.grade z) : {source : Cycle // P.bridge.Recognizes source z} :=
  ⟨P.source z, P.source_recognizes z hfired hdc hrat hgrade⟩

/-- Exact landing: the constructed higher-grade cycle realizes the original dial state. -/
theorem HigherGradeRecognitionPackage.source_realizes
    (P : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    (z : Z) (hfired : ∃ d, D.T d z ≠ 0) (hdc : D.DC z) (hrat : D.Rational z)
    (hgrade : 1 < P.grade z) :
    P.sourceRealization.realize (P.source z) = z :=
  P.realizes_of_recognizes (P.source z) z
    (P.source_recognizes z hfired hdc hrat hgrade)

/-- The certified source's realization is definitionally the same exact higher-grade landing. -/
theorem HigherGradeRecognitionPackage.certifiedSource_realizes
    (P : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    (z : Z) (hfired : ∃ d, D.T d z ≠ 0) (hdc : D.DC z) (hrat : D.Rational z)
    (hgrade : 1 < P.grade z) :
    P.sourceRealization.realize (P.certifiedSource z hfired hdc hrat hgrade).1 = z :=
  P.source_realizes z hfired hdc hrat hgrade

/-- Recognition above grade one follows from the explicit source and its exact landing. -/
theorem HigherGradeRecognitionPackage.recognition_above_one
    (P : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    (z : Z) (hfired : ∃ d, D.T d z ≠ 0) (hdc : D.DC z) (hrat : D.Rational z)
    (hgrade : 1 < P.grade z) : D.Algebraic z := by
  rw [← P.source_realizes z hfired hdc hrat hgrade]
  exact P.sourceRealization.algebraic_realize (P.source z)

/-- A typed source constructor for the already-understood grades zero and one. -/
structure AtMostGradeOneSourceConstructor (D : HodgeDial Z) (grade : Z → ℕ)
    (Source : Type*) where
  sourceRealization : AlgebraicSourceRealization D Source
  construct :
    ∀ z, (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z → grade z ≤ 1 → Source
  realize_construct :
    ∀ z hfired hdc hrat hgrade,
      sourceRealization.realize (construct z hfired hdc hrat hgrade) = z

/-- The lower-grade constructor also lands directly in the algebraic-source predicate. -/
theorem AtMostGradeOneSourceConstructor.recognition
    {grade : Z → ℕ} {Source : Type*}
    (P : AtMostGradeOneSourceConstructor D grade Source)
    (z : Z) (hfired : ∃ d, D.T d z ≠ 0) (hdc : D.DC z) (hrat : D.Rational z)
    (hgrade : grade z ≤ 1) : D.Algebraic z := by
  rw [← P.realize_construct z hfired hdc hrat hgrade]
  exact P.sourceRealization.algebraic_realize (P.construct z hfired hdc hrat hgrade)

/-- Grade-zero/one source construction plus the higher-grade recognition bridge proves the
unrestricted recognition theorem for the dial. -/
theorem recognition_of_gradeSplit_sourceConstruction
    (higher : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    {LowSource : Type*}
    (lower : AtMostGradeOneSourceConstructor D higher.grade LowSource) :
    Recognition D := by
  intro z hfired hdc hrat
  rcases le_or_gt (higher.grade z) 1 with hgrade | hgrade
  · exact lower.recognition z hfired hdc hrat hgrade
  · exact higher.recognition_above_one z hfired hdc hrat hgrade

/-- Once retention is available, the two explicit grade-wise source constructors assemble all the
way to source exhaustion. -/
theorem sourceExhaustion_of_retention_gradeSplit_sourceConstruction
    (hret : Retention D)
    (higher : HigherGradeRecognitionPackage D AngularDossier RadialDossier Curve Cycle IsogClass)
    {LowSource : Type*}
    (lower : AtMostGradeOneSourceConstructor D higher.grade LowSource) :
    SourceExhaustion D :=
  hodge_of_retention_recognition hret
    (recognition_of_gradeSplit_sourceConstruction higher lower)

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.HigherGradeRecognitionPackage.source_recognizes
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.HigherGradeRecognitionPackage.certifiedSource_realizes
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.HigherGradeRecognitionPackage.source_realizes
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.HigherGradeRecognitionPackage.recognition_above_one
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.recognition_of_gradeSplit_sourceConstruction
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_of_retention_gradeSplit_sourceConstruction
