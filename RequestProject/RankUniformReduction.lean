import RequestProject.ThetaGateInterface
import RequestProject.CarrierLatticeWeld

/-!
# Rank-uniform reduction: `Sym^r` registration at every rank = gate 1 + one standing wave

The assembly statement of the program, as a theorem schema rather than prose.  The
registration wall of the rank-`r` rung — the functional equation of the rung's completed
readout on the carrier — reduces, uniformly in `r`, to exactly two per-rung inputs: the
typed transfer gate (`TransferGate`, gate 1) and ONE real condition on the weld axis
(the standing wave, gate 2).  This file is composition of already-compiled bricks; the
value is that the reduction is now a *type*, quantified over all ranks at once.

* `RungData κ` — the per-rank package: a coefficient sequence `a` (the rung's arithmetic
  profile read on the carrier), a typed gate for it, a chart factor `gamma` analytic on
  the gate's strip and Schwarz-real (the Γ/conductor factors of the completed chart),
  and a root number `eps`.
* `RungData.standingWave` — gate 2 typed: reality of the completed readout
  `Λ = γ · F` on the weld axis `Re s = κ/2`, in the exact FE-on-axis shape consumed by
  `TransferGate.fe_of_standingWave`.
* `RungData.fe_of_standingWave` — **the reduction**: a rung's standing wave yields its
  full functional equation on the gate's strip, against the literal
  conjugated-coefficient dual readout.  One application of the compiled gate capstone.
* `symr_reduction` — **the schema**: for ANY weight function and ANY rank-indexed family
  of rungs `D r : RungData (weight r)`, if every rung's standing wave holds then every
  rung's FE holds on its strip.  Rank-uniform registration reduces to the rank-uniform
  standing wave — the program statement, as a theorem.
* `WeldCoupling r D` — **certifier (a), typed**: what "couple the self-dual matrix bank
  to the rung profile" must provide — a derivation of the rung's standing wave *from*
  the carrier-lattice weld `θ_r(1/t) = t^{(r+1)²/2}·θ_r(t)`.  `WeldCoupling.standingWave`
  is the honesty direction: inhabitation at rank `r` discharges the rung's standing
  wave, with the compiled weld (`matrixTheta_inv`) entering as a provided lemma, not a
  hypothesis.  `WeldCoupling.fe` and `symr_reduction_of_weldCoupling` run the chain:
  weld coupling at every rank ⟹ FE at every rank.
* `zeroChartRung` — non-vacuity of the schema's types, DEGENERATE: the zero chart on the
  delta sequence inhabits `RungData`, its standing wave, and `WeldCoupling` at every
  rank.  Type-level smoke test only; it carries no arithmetic content.

Proven here: every implication above, unconditionally — pure composition of the compiled
gate engine (`ThetaGateInterface`) and the compiled rank-uniform weld
(`CarrierLatticeWeld`).  Not proven in this file: `RungData.standingWave` for arithmetic
rungs — and that is ONE proposition per rung, not two: since the weld antecedent of
`WeldCoupling.couple` is already compiled, `WeldCoupling r D` is propositionally
equivalent to `D.standingWave` (`weldCoupling_iff_standingWave` — the equivalence holds
at every `r`, so the rank index carries no logical content).  The `WeldCoupling` type
records certifier (a)'s intended *attack route* — derive the standing wave from the
carrier-lattice self-duality — but cannot enforce that route.  Which ranks' standing
waves are already dischargeable from the compiled corpus (the r = 1 slash-law FE and the
r = 2 RS-box FE are compiled elsewhere) is a corpus question this file does not settle.
-/

open Finset Complex ComplexConjugate

namespace CriticalLinePhasor.RankUniformReduction

open TransferContinuation CriticalLinePhasor.GateInterface
  CriticalLinePhasor.CarrierLatticeWeld

/-! ## The per-rank package -/

/-- The per-rank package of the rank-uniform reduction: the rung's coefficient sequence,
its typed transfer gate (gate 1), a chart factor analytic on the gate's strip and
Schwarz-real (the Γ/conductor factors of the completed chart), and a root number.
Carrying a `RungData κ` is exactly "gate 1 holds for this rung". -/
structure RungData (κ : ℝ) where
  /-- The rung's coefficient sequence — the arithmetic profile read on the carrier. -/
  a : ℕ → ℂ
  /-- Gate 1, typed: the transfer exponent for the rung's coefficients. -/
  gate : TransferGate a κ
  /-- The chart factor of the completed readout (Γ/conductor factors). -/
  gamma : ℂ → ℂ
  /-- The chart factor is analytic on the gate's strip. -/
  gamma_differentiableOn : DifferentiableOn ℂ gamma (transferStrip gate.θ κ)
  /-- The chart factor is Schwarz-real: `conj (γ s̄) = γ s`. -/
  gamma_schwarz : ∀ s : ℂ, conj (gamma (conj s)) = gamma s
  /-- The root number of the rung. -/
  eps : ℂ

namespace RungData

variable {κ : ℝ}

/-- **Gate 2, typed — the standing wave of the rung**: reality (in FE-on-axis shape) of
the completed readout `Λ(s) = γ(s) · F(s)` on the weld axis `Re s = κ/2`, where `F` is
the Abel-summed transfer continuation of the rung's coefficients.  This is the exact
`haxis` shape consumed by `TransferGate.fe_of_standingWave` — ONE real condition per
rung, on the fixed locus of the reflection. -/
def standingWave (D : RungData κ) : Prop :=
  ∀ t : ℝ,
    D.gamma ((κ : ℂ) / 2 + (t : ℂ) * I) *
        abelContinuation D.a ((κ : ℂ) / 2 + (t : ℂ) * I)
      = D.eps * conj (D.gamma ((κ : ℂ) / 2 + (t : ℂ) * I) *
          abelContinuation D.a ((κ : ℂ) / 2 + (t : ℂ) * I))

/-- **The per-rung reduction**: the rung's standing wave yields its full functional
equation on the gate's strip, against the literal conjugated-coefficient dual readout.
Direct application of the compiled `TransferGate.fe_of_standingWave`; nothing else is
consumed. -/
theorem fe_of_standingWave (D : RungData κ) (h : D.standingWave) :
    ∀ s ∈ transferStrip D.gate.θ κ,
      D.gamma ((κ : ℂ) - s) * abelContinuation D.a ((κ : ℂ) - s) =
        D.eps * (D.gamma s * abelContinuation (fun n => conj (D.a n)) s) :=
  D.gate.fe_of_standingWave D.gamma D.gamma_differentiableOn D.gamma_schwarz D.eps h

end RungData

/-! ## The rank-uniform schema -/

/-- **The rank-uniform reduction schema — the program statement as a theorem.**  For any
weight function and any rank-indexed family of rungs `D r : RungData (weight r)`: if
every rung's standing wave holds, then every rung's functional equation holds on its
gate's strip.  Registration at all ranks simultaneously reduces to the rank-uniform
standing wave; no per-rank analysis, no induction over rungs. -/
theorem symr_reduction (weight : ℕ → ℝ) (D : (r : ℕ) → RungData (weight r))
    (h : ∀ r : ℕ, (D r).standingWave) :
    ∀ r : ℕ, ∀ s ∈ transferStrip (D r).gate.θ (weight r),
      (D r).gamma ((weight r : ℂ) - s) *
          abelContinuation (D r).a ((weight r : ℂ) - s) =
        (D r).eps * ((D r).gamma s * abelContinuation (fun n => conj ((D r).a n)) s) :=
  fun r => (D r).fe_of_standingWave (h r)

/-! ## Certifier (a), typed -/

/-- **The certifier-(a) target, typed**: what "couple the self-dual matrix bank to the
rung profile" must provide at rank `r` — a derivation of the rung's standing wave *from*
the carrier-lattice weld `θ_r(1/t) = t^{(r+1)²/2}·θ_r(t)` on `M_{r+1}(ℤ)`.  The weld
statement is the antecedent of the single field, so a provider never proves it: the
compiled `matrixTheta_inv` discharges it (`WeldCoupling.standingWave`).  Inhabiting
`couple` for a genuine arithmetic rung is the open half of certifier (a). -/
structure WeldCoupling (r : ℕ) {κ : ℝ} (D : RungData κ) : Prop where
  /-- The coupling: the rank-`r` carrier-lattice weld implies the rung's standing wave.
  Since the antecedent is compiled (`matrixTheta_inv`), this field is propositionally
  equivalent to the standing wave itself (`weldCoupling_iff_standingWave`) — it records
  the intended derivation route, and cannot enforce it. -/
  couple : (∀ t : ℝ, 0 < t →
      matrixTheta r t⁻¹ = t ^ ((((r : ℝ) + 1) ^ 2) / 2) * matrixTheta r t) →
    D.standingWave

namespace WeldCoupling

variable {r : ℕ} {κ : ℝ} {D : RungData κ}

/-- **Honesty of the coupling target**: inhabitation of `WeldCoupling r D` discharges
the rung's standing wave outright — the compiled weld `matrixTheta_inv` enters as a
provided lemma, not a hypothesis. -/
theorem standingWave (W : WeldCoupling r D) : D.standingWave :=
  W.couple fun _ ht => matrixTheta_inv r ht

/-- **The collapse, recorded**: because the weld is compiled, the coupling target is
propositionally equivalent to the standing wave — at every rank uniformly, so the rank
index of `WeldCoupling` carries no logical content.  The remaining input is ONE
proposition per rung; `WeldCoupling` names the favored route to it, nothing more. -/
theorem weldCoupling_iff_standingWave (r : ℕ) :
    WeldCoupling r D ↔ D.standingWave :=
  ⟨fun W => W.standingWave, fun h => ⟨fun _ => h⟩⟩

/-- The full chain at one rank: weld coupling ⟹ standing wave ⟹ functional equation
on the gate's strip. -/
theorem fe (W : WeldCoupling r D) :
    ∀ s ∈ transferStrip D.gate.θ κ,
      D.gamma ((κ : ℂ) - s) * abelContinuation D.a ((κ : ℂ) - s) =
        D.eps * (D.gamma s * abelContinuation (fun n => conj (D.a n)) s) :=
  D.fe_of_standingWave W.standingWave

end WeldCoupling

/-- **The full program chain, all ranks**: a weld coupling at every rank yields the
functional equation at every rank, each on its own gate's strip.  Certifier (a),
inhabited rank-uniformly, closes rank-uniform registration. -/
theorem symr_reduction_of_weldCoupling (weight : ℕ → ℝ)
    (D : (r : ℕ) → RungData (weight r)) (W : ∀ r : ℕ, WeldCoupling r (D r)) :
    ∀ r : ℕ, ∀ s ∈ transferStrip (D r).gate.θ (weight r),
      (D r).gamma ((weight r : ℂ) - s) *
          abelContinuation (D r).a ((weight r : ℂ) - s) =
        (D r).eps * ((D r).gamma s * abelContinuation (fun n => conj ((D r).a n)) s) :=
  fun r => (D r).fe_of_standingWave (W r).standingWave

/-! ## Non-vacuity (degenerate) -/

/-- Non-vacuity of the schema's types, DEGENERATE: the zero chart over the delta
sequence at weight `1`.  Type-level smoke test only — the completed readout is
identically `0`, so it carries no arithmetic content. -/
noncomputable def zeroChartRung : RungData 1 where
  a := deltaSeq
  gate := unitGate
  gamma := fun _ => 0
  gamma_differentiableOn := differentiableOn_const 0
  gamma_schwarz := fun _ => by simp
  eps := 1

/-- The degenerate rung's standing wave holds (its completed readout is `0`). -/
theorem zeroChartRung_standingWave : zeroChartRung.standingWave := by
  intro t
  simp [zeroChartRung]

/-- The degenerate rung carries a weld coupling at every rank — the coupling types are
inhabited.  No arithmetic content. -/
theorem zeroChartRung_weldCoupling (r : ℕ) : WeldCoupling r zeroChartRung :=
  ⟨fun _ => zeroChartRung_standingWave⟩

end CriticalLinePhasor.RankUniformReduction

#print axioms CriticalLinePhasor.RankUniformReduction.RungData.standingWave
#print axioms CriticalLinePhasor.RankUniformReduction.RungData.fe_of_standingWave
#print axioms CriticalLinePhasor.RankUniformReduction.symr_reduction
#print axioms CriticalLinePhasor.RankUniformReduction.WeldCoupling.standingWave
#print axioms CriticalLinePhasor.RankUniformReduction.WeldCoupling.weldCoupling_iff_standingWave
#print axioms CriticalLinePhasor.RankUniformReduction.WeldCoupling.fe
#print axioms CriticalLinePhasor.RankUniformReduction.symr_reduction_of_weldCoupling
#print axioms CriticalLinePhasor.RankUniformReduction.zeroChartRung
#print axioms CriticalLinePhasor.RankUniformReduction.zeroChartRung_standingWave
#print axioms CriticalLinePhasor.RankUniformReduction.zeroChartRung_weldCoupling
