import RequestProject.GeometricSourceRecognition

/-!
# The universal harmonic clock: one algebraic action, all projectors

The naming that closes the loop (Sam, 2026-07-28): the algebraic clock
behind every coherent rail block is THE universal harmonic clock — the
carrier's own graded action, whose integral character lattice is the
tower-stable `D`-lattice (`UniversalHarmonicLattice.
tower_denominator_stable`: one lattice, all ranks), and whose rails are
its shadows.  Its algebraic incarnations by regime:

* multiplication clocks `[n]` on an abelian variety — degree grading,
  Deninger–Murre context (`AbelianClockProjectors`);
* Frobenius correspondences in finite characteristic — arithmetic
  grading, the freeze instruments' native clock;
* the completion clock at the archimedean place
  (`GaussianClockUniqueness`: pinned by self-duality).

**The universal clock theorem, typed here**: if the clock preserves
algebraic sourcing (the single named hypothesis — the clock's graph is an
algebraic correspondence in the regime at hand), then EVERY spectral
projector of the clock lies in its polynomial calculus, and every
clock-channel component of an algebraic seed is recognized:
`ProjectorRecognition` holds with the projector manufactured by Lagrange
interpolation on the clock spectrum (`clockChannelProjector`).

Honest register: `clockAlgebraic` is a HYPOTHESIS FIELD.  It is
discharged for `[n]`-clocks on abelian varieties (cited) and for
Frobenius clocks in characteristic `p` (cited); for the collective/Weil
channel in characteristic zero it is exactly the named wall — the
Hodge–Tate bridge relocated to a single statement: THE UNIVERSAL CLOCK'S
GRAPH EXISTS IN CHARACTERISTIC ZERO ON THE COLLECTIVE CHANNEL.  Nothing
here proves that; everything here reduces to it.  Scope: does not assume
or prove RH/GRH or the Hodge conjecture.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {order m : ℕ}

/-- The polynomial calculus of the universal clock over a dial on the
model states: correspondences are polynomials in the one clock; the
algebraicity of the calculus is inherited from the single hypothesis that
the clock preserves algebraic sourcing. -/
noncomputable def universalClockCalculus (B : IntFrequencyBank m)
    (D : HodgeDial (GeneralExtensionData order m))
    (halg : ∀ (P : Polynomial ℂ) (z : GeneralExtensionData order m),
      D.Algebraic z → D.Algebraic (clockPolyAct B P z)) :
    CorrespondenceCalculus D where
  Corr := Polynomial ℂ
  act := clockPolyAct B
  AlgebraicCorr _ := True
  transport := fun P _ z hz => halg P z hz

/-- **The universal clock theorem**: one algebraic clock recognizes every
channel component of every algebraic seed — the projector is manufactured
by interpolation on the clock spectrum, algebraic by closure of the
clock's polynomial calculus. -/
theorem universalClock_projectorRecognition (B : IntFrequencyBank m)
    (D : HodgeDial (GeneralExtensionData order m))
    (halg : ∀ (P : Polynomial ℂ) (z : GeneralExtensionData order m),
      D.Algebraic z → D.Algebraic (clockPolyAct B P z))
    (hdecomp : ∀ z : GeneralExtensionData order m,
      (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z →
      ∃ (i₀ : Fin m) (η : GeneralExtensionData order m), D.Algebraic η ∧
        z = fun l i => if i = i₀ then η l i else 0) :
    ProjectorRecognition D (universalClockCalculus B D halg) := by
  intro z hf hdc hrat
  obtain ⟨i₀, η, hη, hz⟩ := hdecomp z hf hdc hrat
  obtain ⟨P, hP⟩ := clockChannelProjector (order := order) B i₀
  refine ⟨P, η, trivial, hη, ?_⟩
  show clockPolyAct B P η = z
  funext l i
  rw [hP η l i, hz]

/-- The terminus route through the universal clock: with retention, the
clock hypothesis and the decomposition hypothesis reach source
exhaustion. -/
theorem universalClock_sourceExhaustion (B : IntFrequencyBank m)
    (D : HodgeDial (GeneralExtensionData order m))
    (halg : ∀ (P : Polynomial ℂ) (z : GeneralExtensionData order m),
      D.Algebraic z → D.Algebraic (clockPolyAct B P z))
    (hdecomp : ∀ z : GeneralExtensionData order m,
      (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z →
      ∃ (i₀ : Fin m) (η : GeneralExtensionData order m), D.Algebraic η ∧
        z = fun l i => if i = i₀ then η l i else 0)
    (hret : Retention D) : SourceExhaustion D :=
  sourceExhaustion_of_projector _ hret
    (universalClock_projectorRecognition B D halg hdecomp)

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.universalClock_projectorRecognition
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.universalClock_sourceExhaustion
