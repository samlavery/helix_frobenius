import RequestProject.EffectiveLedger

/-!
# The Lefschetz rung: `H²` of a surface, with Lefschetz (1,1) as the recognition input

The first positive-dimensional rung of the realization ladder.  The geometric side is the
rational cohomology `H²(X, ℚ)` of a smooth projective surface, presented as a literature
bundle in the depth-one style: every field is a classical statement with its citation, and
everything downstream is proved from the bundle alone.

* the **Hodge decomposition** into the three weight-2 channels `k = q - p ∈ {-2, 0, 2}`
  (Hodge; Griffiths–Harris ch. 0) — `channel`, faithful (`channel_faithful`);
* the **degree/polarization reading** on the DC channel is rational on rational classes
  (intersection theory) — `dc_rational`;
* **Lefschetz (1,1)** (Lefschetz 1924; Hodge) — a rational class with both non-DC channels
  silent is a divisor class — `lefschetz`, with the converse containment `algebraic_dc`
  (the cycle class lands in `H^{1,1}`).

Proved from the bundle, unconditionally: the realization term
(`lefschetzRealization : FaithfulRealization …`, no-kernel from the decomposition's
faithfulness), retention through the bridge, recognition (`lefschetz_recognition` — the
cited classical theorem doing the converse leg), and the executed terminus
(`lefschetz_sourceExhaustion`): **every nonzero rational DC class of the surface has an
algebraic source** — the Hodge conjecture at the `(1,1)` rung, run end to end through the
carrier pipeline with its one open-input slot filled by a theorem of record.  Register:
nothing new is claimed about Lefschetz (1,1); what is new is that the pipeline executes on
positive-dimensional geometry with the recognition slot consuming it.  Also proved:
`dc_fires_at_dc_channel` — a nonzero rational DC class fires precisely at the frequency-zero
channel, the retention statement in its sharpest per-channel form.  No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- The weight-2 bank: three channels at the Hodge frequencies `-2, 0, 2`. -/
def lefschetzBank : IntFrequencyBank 3 where
  freq := ![-2, 0, 2]
  injective := by decide

/-- **The Lefschetz literature bundle** for the rational `H²` of a smooth projective
surface.  Every field is classical, cited in the module docstring. -/
structure LefschetzData (H : Type*) [AddCommGroup H] where
  /-- The three Hodge-channel readings of the complexified class (`(2,0)`, `(1,1)`, `(0,2)`).
  **Hodge decomposition.** -/
  channel : Fin 3 → H →+ ℂ
  /-- The decomposition is faithful: a class silent on all three channels is zero.
  **Hodge decomposition** (complexification embeds). -/
  channel_faithful : ∀ v : H, (∀ i, channel i v = 0) → v = 0
  /-- The DC (degree/polarization) reading is rational on rational classes.
  **Intersection theory.** -/
  dc_rational : ∀ v : H, ∃ q : ℚ, channel 1 v = (q : ℂ)
  /-- The divisor classes (image of the cycle-class map). -/
  Algebraic : H → Prop
  /-- **Lefschetz (1,1)**: a rational class with both non-DC channels silent is a divisor
  class. -/
  lefschetz : ∀ v : H, channel 0 v = 0 → channel 2 v = 0 → Algebraic v

namespace LefschetzData

variable {H : Type*} [AddCommGroup H] (D : LefschetzData H)

/-- The channel realization into the order-zero jet model on the weight-2 bank. -/
noncomputable def toModelHom : H →+ GeneralExtensionData 0 3 where
  toFun v := fun _ i => D.channel i v
  map_zero' := by
    funext l i
    simp
  map_add' a b := by
    funext l i
    simp [Pi.add_apply]

/-- The Lefschetz dial: DC = the `(1,1)` condition (both non-DC channels silent),
`Rational = True` (the space is the rational cohomology itself), `Algebraic` = divisor
classes, readouts = the winding tower of the channel realization. -/
noncomputable def dial : HodgeDial H where
  DC v := D.channel 0 v = 0 ∧ D.channel 2 v = 0
  Rational _ := True
  Algebraic := D.Algebraic
  T d v := generalExtensionTower lefschetzBank.toClockBank d (D.toModelHom v)

/-- **The Lefschetz realization term**: the five-condition bridge instance for `H²`. -/
noncomputable def realization : FaithfulRealization D.dial 0 lefschetzBank where
  toModel := D.toModelHom
  regCompat _ _ := rfl
  dcCompat v hdc := by
    intro l i hi
    fin_cases i
    · exact hdc.1
    · simp [lefschetzBank] at hi
    · exact hdc.2
  ratCompat v hdc _ := by
    intro l i
    fin_cases i
    · exact ⟨0, by rw [Rat.cast_zero]; exact hdc.1⟩
    · exact D.dc_rational v
    · exact ⟨0, by rw [Rat.cast_zero]; exact hdc.2⟩
  noKernel v _ _ h := by
    refine D.channel_faithful v fun i => ?_
    exact congrFun (congrFun h 0) i

/-- Retention for the Lefschetz dial — supplied by the bridge. -/
theorem retention : Retention D.dial :=
  D.realization.retention

/-- **Recognition is Lefschetz (1,1)**, consumed as the cited classical theorem. -/
theorem recognition : Recognition D.dial :=
  fun v _ hdc _ => D.lefschetz v hdc.1 hdc.2

/-- **The terminus, executed on positive-dimensional geometry**: every nonzero rational DC
class of the surface has an algebraic source. -/
theorem sourceExhaustion : SourceExhaustion D.dial :=
  D.realization.sourceExhaustion_of_recognition D.recognition

/-- Unpacked: a nonzero rational `(1,1)` class is a divisor class — Lefschetz through the
pipeline. -/
theorem divisor_law (v : H) (hv : v ≠ 0)
    (h20 : D.channel 0 v = 0) (h02 : D.channel 2 v = 0) : D.Algebraic v :=
  D.sourceExhaustion v hv ⟨h20, h02⟩ trivial

/-- **Sharp per-channel retention**: a nonzero rational DC class fires precisely at the
frequency-zero channel. -/
theorem dc_fires_at_dc_channel (v : H) (hv : v ≠ 0)
    (h20 : D.channel 0 v = 0) (h02 : D.channel 2 v = 0) :
    D.channel 1 v ≠ 0 := by
  intro h11
  refine hv (D.channel_faithful v fun i => ?_)
  fin_cases i
  · exact h20
  · exact h11
  · exact h02

end LefschetzData

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.LefschetzData.realization
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.LefschetzData.sourceExhaustion
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.LefschetzData.divisor_law
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.LefschetzData.dc_fires_at_dc_channel
