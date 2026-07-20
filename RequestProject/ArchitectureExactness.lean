import RequestProject.EllipticDepthOneRung

/-!
# The retention/recognition factorization is exact and independent

Answers the objection that `hodge_of_retention_recognition` "names the hard part rather than
reducing it" by making the naming itself a theorem package, at exactly the strength that is
true:

* **Exactness** (`sourceExhaustion_iff_recognition`): given the proven detector (retention) and
  zero-silence of the tower, recognition is *precisely* source exhaustion restricted to fired
  classes — the factorization is lossless.  Modulo the detector half, which the program proves
  on every constructed dial, recognition IS the conjecture: nothing thinner is claimed, nothing
  thicker is hidden.

* **Independence** (`factorization_exact_and_independent`): neither hypothesis implies the
  conclusion — or the other — alone, exhibited by two concrete model dials on `ℤ`:

  - `phantomDial` — every readout silent, recognition vacuously true, a nonzero rational DC
    class undetected: retention fails, source exhaustion fails.  This is the paper's
    pre-registered falsifier (a), the *phantom*, exhibited as a consistent scenario.
  - `sourcelessDial` — the identity readout fires on every nonzero class (retention holds) but
    nothing is algebraic: recognition fails, source exhaustion fails.  This is falsifier (b),
    the *false source* / sourceless branch of the dichotomy, likewise consistent.

  Because both failure modes have models, proving retention on the constructed dials
  (Vandermonde separation, the realization transports, the instance ladder) is substantive
  mathematics — the property genuinely fails elsewhere — and the assembly theorem does real
  work: it upgrades the strictly weaker hypothesis (recognition, which the sourceless model
  separates from source exhaustion) to the full statement, paying with the proven detector.

Register, exact: none of this proves any part of recognition above grade one.  It proves that
the architecture isolates recognition *losslessly*, that both halves are load-bearing, and
that the falsifiability register describes consistent mathematics rather than straw scenarios.
No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {Z : Type*} [Zero Z]

/-- **Exactness of the factorization**: given retention and zero-silence of the tower,
recognition is precisely source exhaustion — the reduction is lossless in both directions. -/
theorem sourceExhaustion_iff_recognition {D : HodgeDial Z}
    (hret : Retention D) (hT0 : ∀ d, D.T d 0 = 0) :
    SourceExhaustion D ↔ Recognition D := by
  constructor
  · intro hse z hfire hdc hrat
    rcases eq_or_ne z 0 with rfl | hz
    · obtain ⟨d, hd⟩ := hfire
      exact absurd (hT0 d) hd
    · exact hse z hz hdc hrat
  · exact fun hrec => hodge_of_retention_recognition hret hrec

/-- **The phantom dial** — the model of pre-registered falsifier (a): every readout is silent,
so a nonzero rational DC class is undetected.  Recognition holds vacuously; retention and
source exhaustion fail. -/
def phantomDial : HodgeDial ℤ where
  DC _ := True
  Rational _ := True
  Algebraic z := z = 0
  T _ _ := 0

theorem phantomDial_recognition : Recognition phantomDial := by
  rintro z ⟨d, hd⟩ - -
  exact absurd rfl hd

theorem phantomDial_not_retention : ¬ Retention phantomDial := by
  intro h
  obtain ⟨d, hd⟩ := h 1 one_ne_zero trivial trivial
  exact hd rfl

theorem phantomDial_not_sourceExhaustion : ¬ SourceExhaustion phantomDial := by
  intro h
  exact one_ne_zero (h 1 one_ne_zero trivial trivial)

/-- **The sourceless dial** — the model of falsifier (b), the sourceless branch of the
dichotomy: the identity readout fires on every nonzero class, but nothing is algebraic.
Retention holds; recognition and source exhaustion fail. -/
noncomputable def sourcelessDial : HodgeDial ℤ where
  DC _ := True
  Rational _ := True
  Algebraic _ := False
  T _ z := (z : ℂ)

theorem sourcelessDial_retention : Retention sourcelessDial :=
  fun z hz _ _ => ⟨0, by
    show (z : ℂ) ≠ 0
    exact_mod_cast hz⟩

theorem sourcelessDial_not_sourceExhaustion : ¬ SourceExhaustion sourcelessDial :=
  fun h => h 1 one_ne_zero trivial trivial

theorem sourcelessDial_not_recognition : ¬ Recognition sourcelessDial :=
  fun h => h 1 ⟨0, by norm_num [sourcelessDial]⟩ trivial trivial

/-- **The factorization is exact and both factors are independent.**  Recognition alone does
not give source exhaustion (the phantom model), retention alone does not give it (the
sourceless model), and together — by `hodge_of_retention_recognition` — they do, losslessly
(`sourceExhaustion_iff_recognition`).  The two models are the paper's pre-registered
falsifiers, exhibited as consistent scenarios. -/
theorem factorization_exact_and_independent :
    (∃ D : HodgeDial ℤ, Recognition D ∧ ¬ SourceExhaustion D ∧ ¬ Retention D) ∧
    (∃ D : HodgeDial ℤ, Retention D ∧ ¬ SourceExhaustion D ∧ ¬ Recognition D) :=
  ⟨⟨phantomDial, phantomDial_recognition, phantomDial_not_sourceExhaustion,
     phantomDial_not_retention⟩,
   ⟨sourcelessDial, sourcelessDial_retention, sourcelessDial_not_sourceExhaustion,
     sourcelessDial_not_recognition⟩⟩

/-- **A detector is not a constructor, as a theorem**: two dials with identical readouts, DC,
and rationality — identical freeze/detection data — one of which satisfies source exhaustion
while the other does not.  Detection data underdetermines algebraicity, so freeze *detects*
and never constructs; the constructor is always a separate, named input.  (The paper's own
register for the freeze detector, now model-theoretic fact.) -/
theorem detector_not_constructor :
    ∃ D₁ D₂ : HodgeDial ℤ, D₁.T = D₂.T ∧ D₁.DC = D₂.DC ∧ D₁.Rational = D₂.Rational ∧
      SourceExhaustion D₁ ∧ ¬ SourceExhaustion D₂ :=
  ⟨{ DC := fun _ => True
     Rational := fun _ => True
     Algebraic := fun _ => True
     T := fun _ z => (z : ℂ) },
   sourcelessDial, rfl, rfl, rfl, fun _ _ _ _ => trivial,
   sourcelessDial_not_sourceExhaustion⟩

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.detector_not_constructor
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_iff_recognition
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.phantomDial_recognition
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourcelessDial_retention
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.factorization_exact_and_independent
