import RequestProject.HodgeDial

/-!
# The recognition bridge: the last mystery's pipeline, machine-checked

The collective recognition loop (companion memos `tmp/construction_arm_notes.md`,
`tmp/carrier_inversion_notes.md`; GRADE4 items 42--43) reads a detected Weil/collective
class on a carrier fiber and returns a **theorem-certified algebraic cycle**.  Its candidate
closure is a three-link pipeline

```
    cycle  =  Construction  ∘  Torelli  ∘  RadialReading
```

with every classical monument along the way an *unproven input consumed as a named
hypothesis*, exactly as `HodgeDial` fixes the Hodge terminus and `HelixResolventCapture`
fixes the GRH spine.  This file makes the pipeline's composition logic -- and the sharp
negative that gates it -- kernel-checked, while asserting none of the monuments.

**The four monuments, as named structure fields (asserted by no one):**

* **Faltings** (the angular boundary, Tier 2/3 of the inversion memo).  The angular stream
  (the `L`-function / per-prime Frobenius data) determines the isogeny class **exactly** and
  **no finer**.  Split into `angular_complete` (Tier 2: equal angular class ⟹ isogenous --
  Faltings' isogeny theorem) and `angular_invariant` (its converse), together the biconditional
  `angular_reads_isogeny_class`; and `angular_blind` (Tier 3: two *detected*, non-isomorphic
  members with **identical** angular dossiers exist -- the `L`-invisible fine coordinate).
* **Retention** (the radial channel, the K3-measured statement).  The radial/period channel
  **separates** the very members the angular channel conflates: distinct true curves force
  distinct radial dossiers (`radial_retention`).
* **Torelli** (effective genus-3, non-hyperelliptic locus).  The curve reconstructed from the
  radial dossier is the true one (`torelli_spec`).
* **Schoen** (unconditional cyclic-cover branch; van Geemen for the decomposable regime).
  The cycle built from the true curve certifies the fiber's frozen lane (`construct_spec`), and
  in the decomposable regime the elementary deck cycle does so from the **angular data alone**
  (`decomposable_spec`).

**The unconditional content (the theorems):**

* `recognition_closes` -- the simple-regime pipeline composes: every detected fiber has a
  constructed, certified cycle, from `{radial, torelli, construct}`.
* `decomposable_shortcut` -- the second route: in the decomposable regime recognition closes
  from `{angular, constructDecomposable}` **without the torelli/radial links** (item 42).
* `boundary_necessity` -- the sharp negative (Faltings Tier 3): from `angular_blind`, **no
  function of angular data alone can output the correct curve** for both conflated members --
  so member-level recognition cannot be done on the angular instrument.
* `boundary_radial_separates` -- the positive complement: on the very witnesses where the
  angular reading is blind, the radial reading distinguishes them (`C′` is not an *angular*
  carrier invariant but **is** a radial one).

Nothing here asserts any monument; nothing here proves any Hodge or Tate statement.  The
value, as with the sibling files, is that the *architecture* is kernel-fixed: any future
landing of Torelli/Schoen/retention composes into recognition with no further argument, and
the impossibility is a theorem, not a slogan.  A finite `toyBridge` witnesses that all fields
are simultaneously satisfiable.  No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The recognition bridge**: the collective recognition pipeline over abstract carrier
data, with every classical monument carried as a named field.  `angular`/`radial` are the two
carrier readings; `angularClass` extracts the isogeny-class label the angular stream sees;
`torelli`/`construct` are the reconstruction and cycle-construction maps; `trueCurve` is the
fiber's actual underlying curve (the fine, `L`-invisible coordinate); `Recognizes` is the
Tate/algebraic certificate tying a cycle to a fiber's frozen lane. -/
structure RecognitionBridge
    (Fiber AngularDossier RadialDossier Curve Cycle IsogClass : Type*) where
  /-- the angular reading (the `L`-function / per-prime Frobenius stream). -/
  angular : Fiber → AngularDossier
  /-- the isogeny-class label read off the angular dossier. -/
  angularClass : AngularDossier → IsogClass
  /-- the radial/period-channel reading. -/
  radial : Fiber → RadialDossier
  /-- the Torelli reconstruction map: radial dossier ↦ recovered curve. -/
  torelli : RadialDossier → Curve
  /-- Schoen's construction: curve ↦ codimension-2 Weil cycle. -/
  construct : Curve → Cycle
  /-- the decomposable-regime elementary deck cycle, built from angular data alone. -/
  constructDecomposable : AngularDossier → Cycle
  /-- the fiber's actual underlying curve (the fine moduli coordinate). -/
  trueCurve : Fiber → Curve
  /-- the isogeny relation on fibers (the coarse invariant Faltings sees). -/
  Isogenous : Fiber → Fiber → Prop
  /-- the fiber carries a detected collective/Weil (frozen) class. -/
  Detected : Fiber → Prop
  /-- the fiber's dossier is decomposable-classed (imprimitive Weil type). -/
  Decomposable : Fiber → Prop
  /-- the cycle certifies the fiber's frozen lane (algebraic-and-Tate recognition). -/
  Recognizes : Cycle → Fiber → Prop
  /-- **Faltings, Tier 2 (completeness).**  Equal angular class ⟹ isogenous: the angular
  stream determines the isogeny class (the isogeny theorem). -/
  angular_complete :
    ∀ f g, angularClass (angular f) = angularClass (angular g) → Isogenous f g
  /-- **Faltings, Tier 2 (invariance).**  Isogenous fibers are angular-indistinguishable at
  class level -- the converse leg of the boundary. -/
  angular_invariant :
    ∀ f g, Isogenous f g → angularClass (angular f) = angularClass (angular g)
  /-- **Faltings, Tier 3 (blindness).**  Two *detected*, non-isomorphic members with
  **identical** angular dossiers and distinct true curves -- the `L`-invisible fine
  coordinate, provably absent from the angular stream. -/
  angular_blind :
    ∃ f g, Detected f ∧ Detected g ∧ angular f = angular g ∧ trueCurve f ≠ trueCurve g
  /-- **Retention (radial).**  The radial channel separates members the angular channel
  conflates: distinct true curves force distinct radial dossiers (the K3-measured statement). -/
  radial_retention :
    ∀ f g, Detected f → Detected g → trueCurve f ≠ trueCurve g → radial f ≠ radial g
  /-- **Torelli.**  The curve reconstructed from the radial dossier is the true one. -/
  torelli_spec : ∀ f, Detected f → torelli (radial f) = trueCurve f
  /-- **Schoen.**  The cycle built from the true curve certifies the fiber's frozen lane. -/
  construct_spec : ∀ f, Detected f → Recognizes (construct (trueCurve f)) f
  /-- **van Geemen (decomposable regime).**  In the decomposable regime the elementary deck
  cycle, built from the **angular data alone**, certifies the fiber. -/
  decomposable_spec :
    ∀ f, Detected f → Decomposable f → Recognizes (constructDecomposable (angular f)) f

variable {Fiber AngularDossier RadialDossier Curve Cycle IsogClass : Type*}
variable (RB : RecognitionBridge Fiber AngularDossier RadialDossier Curve Cycle IsogClass)

/-- **The recognized cycle** of a fiber via the full simple-regime pipeline
`construct ∘ torelli ∘ radial`. -/
def RecognitionBridge.recognizedCycle (f : Fiber) : Cycle :=
  RB.construct (RB.torelli (RB.radial f))

/-- **Recognition closes (simple regime), unconditional.**  Given the Torelli and Schoen
fields, every detected fiber has a constructed, certified cycle: the pipeline composes.  Uses
`{radial, torelli, construct}` -- the full three-link route. -/
theorem recognition_closes (f : Fiber) (hf : RB.Detected f) :
    RB.Recognizes (RB.recognizedCycle f) f := by
  show RB.Recognizes (RB.construct (RB.torelli (RB.radial f))) f
  rw [RB.torelli_spec f hf]
  exact RB.construct_spec f hf

/-- **The decomposable shortcut, unconditional (item 42).**  In the decomposable regime
recognition closes from `{angular, constructDecomposable}` alone -- the elementary deck cycle,
**no Torelli and no radial reading**.  This is the second route: the two-regime structure is
visible in which fields each theorem consumes (simple needs `{angular, radial, torelli,
construct}`; decomposable needs `{angular, constructDecomposable}`). -/
theorem decomposable_shortcut (f : Fiber) (hf : RB.Detected f) (hd : RB.Decomposable f) :
    RB.Recognizes (RB.constructDecomposable (RB.angular f)) f :=
  RB.decomposable_spec f hf hd

/-- **The angular stream reads exactly the isogeny class** (Faltings Tier 2, the biconditional
form): equal angular class ⇔ isogenous. -/
theorem angular_reads_isogeny_class (f g : Fiber) :
    RB.angularClass (RB.angular f) = RB.angularClass (RB.angular g) ↔ RB.Isogenous f g :=
  ⟨RB.angular_complete f g, RB.angular_invariant f g⟩

/-- **Boundary necessity: the sharp negative (Faltings Tier 3).**  From the blindness field,
**no function of angular data alone can output the correct curve** for every fiber: any
candidate `recover : AngularDossier → Curve` fails on the two conflated members.  So the
member-level curve -- which Schoen's simple-regime cycle consumes -- cannot be produced on the
angular instrument.  An honest impossibility in the model, the Tier-3 content as a theorem. -/
theorem boundary_necessity :
    ¬ ∃ recover : AngularDossier → Curve, ∀ f, recover (RB.angular f) = RB.trueCurve f := by
  rintro ⟨recover, hrec⟩
  obtain ⟨f, g, _, _, hang, hcurve⟩ := RB.angular_blind
  exact hcurve (by rw [← hrec f, ← hrec g, hang])

/-- **Boundary, positive complement: the radial reading separates what the angular reading
cannot.**  On the very witnesses where the angular dossiers coincide (Tier-3 blindness), the
radial dossiers differ -- `C′` is not an *angular* carrier invariant but **is** a radial one.
This is why the pipeline routes member recovery through the radial channel. -/
theorem boundary_radial_separates :
    ∃ f g, RB.angular f = RB.angular g ∧ RB.radial f ≠ RB.radial g := by
  obtain ⟨f, g, hf, hg, hang, hcurve⟩ := RB.angular_blind
  exact ⟨f, g, hang, RB.radial_retention f g hf hg hcurve⟩

/-! ## A finite witness: the structure is non-vacuous

`toyBridge` instantiates every field simultaneously on `Fin 3`, with a genuine two-regime
split: fibers `0, 1` are **simple** (angular-conflated -- `angular 0 = angular 1 = 0` -- so
recovered only through the radial channel), and fiber `2` is **decomposable** (recognized from
its angular label alone).  The blindness witness is the conflated pair `(0, 1)`, whose radial
readings nonetheless differ.  All named hypotheses hold, so the architecture is inhabited. -/

/-- **The finite witness.**  `angular = ![0, 0, 2]` conflates fibers `0` and `1`; every other
map is the identity; `Detected` is total; `Decomposable` singles out fiber `2`; `Recognizes c f`
is `c = f`. -/
def toyBridge : RecognitionBridge (Fin 3) (Fin 3) (Fin 3) (Fin 3) (Fin 3) (Fin 3) where
  angular := ![0, 0, 2]
  angularClass := id
  radial := id
  torelli := id
  construct := id
  constructDecomposable := id
  trueCurve := id
  Isogenous f g := (![0, 0, 2] : Fin 3 → Fin 3) f = ![0, 0, 2] g
  Detected _ := True
  Decomposable f := f = 2
  Recognizes c f := c = f
  angular_complete := fun _ _ h => h
  angular_invariant := fun _ _ h => h
  angular_blind := ⟨0, 1, trivial, trivial, by decide, by decide⟩
  radial_retention := fun _ _ _ _ h => h
  torelli_spec := fun _ _ => rfl
  construct_spec := fun _ _ => rfl
  decomposable_spec := by decide

/-- **The witness recognizes every detected fiber** (via the simple-regime pipeline) -- a
concrete non-vacuity certificate for the whole architecture. -/
theorem toyBridge_recognizes_all (f : Fin 3) (hf : toyBridge.Detected f) :
    ∃ c, toyBridge.Recognizes c f :=
  ⟨toyBridge.recognizedCycle f, recognition_closes toyBridge f hf⟩

/-- The witness fires the decomposable shortcut on fiber `2`, from its angular label alone. -/
theorem toyBridge_decomposable_shortcut :
    toyBridge.Recognizes (toyBridge.constructDecomposable (toyBridge.angular 2)) 2 :=
  decomposable_shortcut toyBridge 2 trivial rfl

/-- The witness exhibits the boundary: no angular-only map recovers the true curve everywhere. -/
theorem toyBridge_boundary :
    ¬ ∃ recover : Fin 3 → Fin 3, ∀ f, recover (toyBridge.angular f) = toyBridge.trueCurve f :=
  boundary_necessity toyBridge

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.recognition_closes
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.decomposable_shortcut
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.angular_reads_isogeny_class
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.boundary_necessity
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.boundary_radial_separates
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.toyBridge_recognizes_all
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.toyBridge_decomposable_shortcut
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.toyBridge_boundary
