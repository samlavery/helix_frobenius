import RequestProject.CMProductRung
import RequestProject.ZetaSixLattice

/-!
# Phase three: the generating pairing and the lattice landing, typed

The endgame's two imports become interfaces with their reduction spines proved, so that the
attempt (phase four) is a single named field.

* **The generating-pairing compression** (`GeneratingPairingData`,
  `recognition_of_generating_pairing`): if every tower level factors through one pairing —
  the field Schmid's SL(2)-orbit theorem and Saito admissibility are staked to supply, via
  finite generation — then recognition for the *entire dial* follows from recognition of
  that *single pairing*.  Unconditional reduction: the universal quantifier over grades
  collapses; phase four's target is exactly the one field `sourced_of_pairing`.

* **The lattice landing** (`exact_closure_of_lattice_landing`): the Green–Griffiths–Kerr
  reading is staked to force integer-weighted common-height residuals *into* `ℤ[ζ₆]`; the
  proven rigidity threshold (`ZetaSixLattice.lattice_residual_exact`) then converts any
  sub-unit bound into exact vanishing.  Landing (cited, to be earned) + threshold (proven)
  = exact closure.

Register: neither import is claimed.  What is proved is that each import, once supplied,
finishes its half by composition with theorems already in-tree — and that the whole
remaining weight of the program rests on `sourced_of_pairing`, one recognition statement for
one pairing.  No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The generating-pairing bundle** over a dial: every tower level factors through a single
pairing (the finite-generation/admissibility collapse — Schmid, Saito; staked, cited at the
point of eventual use), with level maps that preserve zero, and the pairing recognizes its
own fired classes (phase four's single target field). -/
structure GeneratingPairingData {Z : Type*} [Zero Z] (D : HodgeDial Z) where
  /-- The single generating pairing. -/
  pairing : Z → ℂ
  /-- Level maps through which every tower readout factors. -/
  level : ℕ → ℂ → ℂ
  /-- Zero is preserved levelwise. -/
  level_zero : ∀ d, level d 0 = 0
  /-- **The collapse** (Schmid/Saito + finite generation, staked): every tower level factors
  through the generating pairing. -/
  generates : ∀ (d : ℕ) (z : Z), D.T d z = level d (pairing z)
  /-- **Phase four's target**: the pairing recognizes its own fired rational DC classes. -/
  sourced_of_pairing : ∀ z : Z, pairing z ≠ 0 → D.DC z → D.Rational z → D.Algebraic z

/-- **The compression theorem, unconditional**: recognition for the entire dial follows from
recognition of the single generating pairing — the universal quantifier over grades
collapses.  With the bridge, source exhaustion then needs exactly one construction. -/
theorem recognition_of_generating_pairing {Z : Type*} [Zero Z] {D : HodgeDial Z}
    (G : GeneratingPairingData D) : Recognition D := by
  rintro z ⟨d, hd⟩ hdc hrat
  refine G.sourced_of_pairing z (fun hp => ?_) hdc hrat
  rw [G.generates d z, hp, G.level_zero] at hd
  exact hd rfl

/-- The terminus through the generating pairing: retention (proven on the constructed dials)
plus the one-pairing recognition give source exhaustion. -/
theorem sourceExhaustion_of_generating_pairing {Z : Type*} [Zero Z] {D : HodgeDial Z}
    (hret : Retention D) (G : GeneratingPairingData D) : SourceExhaustion D :=
  hodge_of_retention_recognition hret (recognition_of_generating_pairing G)

/-- **Lattice landing plus the proven threshold = exact closure**: if the Green–Griffiths–Kerr
reading lands the residual in `ℤ[ζ₆]` (staked) and any bound places it below unit magnitude,
the residual is exactly zero — measurement becomes exactness by rigidity. -/
theorem exact_closure_of_lattice_landing {residual : ℂ} {a b : ℤ}
    (hland : residual = ZetaSixLattice.latticePoint a b)
    (hsub : Complex.normSq residual < 1) : residual = 0 := by
  rw [hland] at hsub ⊢
  exact ZetaSixLattice.lattice_residual_exact hsub

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.recognition_of_generating_pairing
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_of_generating_pairing
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.exact_closure_of_lattice_landing
