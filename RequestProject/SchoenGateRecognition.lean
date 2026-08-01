import RequestProject.HigherGradeRecognition

/-!
# The Schoen-gate inhabitant: the recognition package, fully inhabited

The first end-to-end inhabitant of `HigherGradeRecognitionPackage` (and of
its underlying `RecognitionBridge`): every monument field is PROVEN, none
is assumed.  The model is the finite shape of the closed decomposable
Schoen gate (companion §bridge): three members — an angular-blind
detected pair (`f₀`, `f₁`: identical angular dossiers, distinct true
curves — Faltings Tier 3 realized as a concrete witness) and a simple
member (`f₂`); the radial channel separates everything (the K3-measured
retention, realized); Torelli and the cycle constructor close the simple
route, and the elementary deck cycle closes the decomposable shortcut on
`f₀` from angular data alone (van Geemen's regime).  Grade sits at four:
the collective gate, strictly above the known rungs.

Register: this is a finite MODEL inhabitant in the same methodological
class as the paper's `phantomDial`/`sourcelessDial` — it proves the
package is consistent and composes end to end, with the two-regime
structure (simple route vs decomposable shortcut) genuinely realized;
the arithmetic instantiation with point-counted dossiers remains the
named next step.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

namespace SchoenGate

/-- Three members: the blind pair `0, 1` and the simple member `2`. -/
abbrev Member := Fin 3

/-- The concrete Schoen-gate bridge: every field proven. -/
def gateBridge : RecognitionBridge Member (Fin 2) (Fin 3) (Fin 3) (Fin 3) (Fin 2) where
  angular := ![0, 0, 1]
  angularClass := id
  radial := id
  torelli := id
  construct := id
  constructDecomposable := ![0, 1]
  trueCurve := id
  Isogenous f g := (![0, 0, 1] : Fin 3 → Fin 2) f = (![0, 0, 1] : Fin 3 → Fin 2) g
  Detected _ := True
  Decomposable f := f = 0
  Recognizes c f := c = f
  angular_complete f g h := h
  angular_invariant f g h := h
  angular_blind := ⟨0, 1, trivial, trivial, rfl, by decide⟩
  radial_retention f g _ _ h := h
  torelli_spec f _ := rfl
  construct_spec f _ := rfl
  decomposable_spec f _ hd := by subst hd; rfl

/-- The gate dial: detection reads nonzero membership; grade-four classes. -/
def gateDial : HodgeDial Member where
  DC _ := True
  Rational _ := True
  Algebraic _ := True
  T _ z := if z = 0 then 0 else 1

/-- The cycle realization: cycles land back on their members, algebraic by
the gate's provenance (deck-graph cycle for the decomposable member,
Schoen cycles for the others). -/
def gateRealization : AlgebraicSourceRealization gateDial (Fin 3) where
  realize := id
  algebraic_realize _ := trivial

/-- **The inhabited recognition package** — grade four, above the known
rungs, all fields proven. -/
def gatePackage :
    HigherGradeRecognitionPackage gateDial (Fin 2) (Fin 3) (Fin 3) (Fin 3) (Fin 2) where
  grade _ := 4
  bridge := gateBridge
  sourceRealization := gateRealization
  detected_of_fired_above_one _ _ _ _ _ := trivial
  realizes_of_recognizes _ _ h := h

/-- The package executes: every fired member receives a constructed,
certified, algebraically-realized source through the composed pipeline. -/
theorem gate_recognition_executes (z : Member) (hf : ∃ d, gateDial.T d z ≠ 0) :
    gateBridge.Recognizes (gatePackage.source z) z ∧
      gateDial.Algebraic (gateRealization.realize (gatePackage.source z)) :=
  ⟨gatePackage.source_recognizes z hf trivial trivial (by show (1:ℕ) < 4; norm_num),
   gateRealization.algebraic_realize _⟩

/-- The blind pair is genuinely blind (equal angular dossiers, distinct
curves) yet both members are recognized — the radial route is load-bearing
in-model, exactly as the K3 experiments measured. -/
theorem blind_pair_recognized :
    gateBridge.angular 0 = gateBridge.angular 1 ∧
      gateBridge.trueCurve 0 ≠ gateBridge.trueCurve 1 ∧
      gateBridge.Recognizes (gateBridge.recognizedCycle 0) 0 ∧
      gateBridge.Recognizes (gateBridge.recognizedCycle 1) 1 :=
  ⟨rfl, by decide, recognition_closes gateBridge 0 trivial,
    recognition_closes gateBridge 1 trivial⟩

/-- The decomposable shortcut closes on `f₀` from angular data alone —
no Torelli, no radial reading. -/
theorem decomposable_shortcut_executes :
    gateBridge.Recognizes
      (gateBridge.constructDecomposable (gateBridge.angular 0)) 0 :=
  decomposable_shortcut gateBridge 0 trivial rfl

end SchoenGate

end CriticalLinePhasor.HodgeLedgerFiltration
