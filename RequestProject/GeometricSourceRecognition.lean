import RequestProject.HodgeRealizationBridge

/-!
# Factored geometric recognition: the intermediate object demanded by type,
# and the clock ↔ multiplication-graph dictionary

The recognition target, refactored one level more flexibly (review
dialogue, 2026-07-28): a rational DC state need not be matched directly to
a cycle — it suffices to construct an intermediate GEOMETRIC object whose
standard algebraic-geometric realization produces the cycle:

    rational DC state → geometric object → algebraic cycle → class = state.

Two typed interfaces enforce the factoring:

* `GeometricRealizationChain` / `GeometricRecognition` — recognition must
  exhibit a term of a geometric type `Geom` BEFORE the class equality; a
  merely cohomological restatement is not expressible through the
  interface.
* `CorrespondenceCalculus` / `ProjectorRecognition` — the projector route:
  recognition via an algebraic correspondence applied to an algebraic
  seed, with the correspondence's algebraicity a HYPOTHESIS FIELD
  (`AlgebraicCorr π`) — the review's non-negotiable step ("the recovered
  projector must be shown algebraic") is a proof obligation by type,
  never smuggled.

Both compose to dial `Recognition`, hence with retention to the terminus.

**The dictionary entry** (`clockChannelProjector`): channel projectors are
polynomials in the clock operator — Lagrange/Vandermonde inversion over
the distinct channel multipliers.  On an abelian variety the clock
operator is realized by the multiplication-by-`n` graphs, which are
ALGEBRAIC correspondences, and the resulting projectors are the
Chow–Künneth/Beauville projectors — algebraic by the cited theorem of
Deninger–Murre.  The model theorem here is the Vandermonde half of that
construction; the identification clocks ↦ `[n]`-graphs is the dictionary
entry, and the algebraicity of projectors BEYOND the graph algebra (the
collective/Weil rail) is the named open wall, not a field of any
structure below.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {Z : Type*} [Zero Z]

/-! ## The factored interface -/

/-- The factored geometric source chain of a dial: intermediate geometric
objects, their standard realization as algebraic cycles, and the cycle
class map — with cycle classes algebraically sourced by provenance. -/
structure GeometricRealizationChain (D : HodgeDial Z) where
  /-- the intermediate geometric objects (correspondences, isogeny
  factors, degeneracy loci, …). -/
  Geom : Type*
  /-- the algebraic cycles. -/
  Cycle : Type*
  /-- the standard algebraic-geometric realization. -/
  realize : Geom → Cycle
  /-- the cycle class map into dial states. -/
  cycleClass : Cycle → Z
  /-- classes of algebraic cycles are algebraically sourced. -/
  algebraic_class : ∀ c, D.Algebraic (cycleClass c)

/-- **Factored geometric recognition**: every fired rational DC state is
the class of the realization of some geometric object — the intermediate
object is demanded before the class equality. -/
def GeometricRecognition (D : HodgeDial Z)
    (C : GeometricRealizationChain D) : Prop :=
  ∀ z : Z, (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z →
    ∃ g : C.Geom, C.cycleClass (C.realize g) = z

/-- The per-state source bundle (the review's exact shape): the geometric
object, with its landing carried as data — a bare cohomological projector
cannot inhabit this type. -/
structure GeometricSourceFor {D : HodgeDial Z}
    (C : GeometricRealizationChain D) (z : Z) where
  geom : C.Geom
  landing : C.cycleClass (C.realize geom) = z

/-- Factored recognition is exactly per-state source inhabitation. -/
theorem geometricRecognition_iff_sources {D : HodgeDial Z}
    (C : GeometricRealizationChain D) :
    GeometricRecognition D C ↔
      ∀ z : Z, (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z →
        Nonempty (GeometricSourceFor C z) := by
  constructor
  · intro h z hf hdc hrat
    obtain ⟨g, hg⟩ := h z hf hdc hrat
    exact ⟨⟨g, hg⟩⟩
  · intro h z hf hdc hrat
    obtain ⟨s⟩ := h z hf hdc hrat
    exact ⟨s.geom, s.landing⟩

/-- Factored geometric recognition yields dial recognition. -/
theorem recognition_of_geometric {D : HodgeDial Z}
    (C : GeometricRealizationChain D) (h : GeometricRecognition D C) :
    Recognition D := by
  intro z hf hdc hrat
  obtain ⟨g, hg⟩ := h z hf hdc hrat
  rw [← hg]
  exact C.algebraic_class _

/-- With retention, factored geometric recognition reaches the terminus. -/
theorem sourceExhaustion_of_geometric {D : HodgeDial Z}
    (C : GeometricRealizationChain D) (hret : Retention D)
    (h : GeometricRecognition D C) : SourceExhaustion D :=
  hodge_of_retention_recognition hret (recognition_of_geometric C h)

/-! ## The projector route -/

/-- A correspondence calculus over a dial: correspondences acting on
states, with an algebraicity predicate on correspondences and the
transport law "algebraic correspondences preserve algebraic sourcing".
The predicate is a FIELD: exhibiting it is a proof obligation at every
use — a merely cohomological projector cannot discharge it. -/
structure CorrespondenceCalculus (D : HodgeDial Z) where
  /-- the correspondences. -/
  Corr : Type*
  /-- cohomological action on dial states. -/
  act : Corr → Z → Z
  /-- algebraicity of a correspondence (graphs, their combinations, …). -/
  AlgebraicCorr : Corr → Prop
  /-- an algebraic correspondence carries algebraically sourced states to
  algebraically sourced states. -/
  transport : ∀ c, AlgebraicCorr c → ∀ z, D.Algebraic z →
    D.Algebraic (act c z)

/-- **Projector recognition**: every fired rational DC state is the image
of an algebraic seed under an ALGEBRAIC correspondence projector —
`π_z(η) = z` with the algebraicity of `π_z` a hypothesis, never assumed. -/
def ProjectorRecognition (D : HodgeDial Z)
    (K : CorrespondenceCalculus D) : Prop :=
  ∀ z : Z, (∃ d, D.T d z ≠ 0) → D.DC z → D.Rational z →
    ∃ (π : K.Corr) (η : Z),
      K.AlgebraicCorr π ∧ D.Algebraic η ∧ K.act π η = z

/-- Projector recognition yields dial recognition. -/
theorem recognition_of_projector {D : HodgeDial Z}
    (K : CorrespondenceCalculus D) (h : ProjectorRecognition D K) :
    Recognition D := by
  intro z hf hdc hrat
  obtain ⟨p, η, halg, hη, hact⟩ := h z hf hdc hrat
  rw [← hact]
  exact K.transport p halg η hη

/-- With retention, projector recognition reaches the terminus. -/
theorem sourceExhaustion_of_projector {D : HodgeDial Z}
    (K : CorrespondenceCalculus D) (hret : Retention D)
    (h : ProjectorRecognition D K) : SourceExhaustion D :=
  hodge_of_retention_recognition hret (recognition_of_projector K h)

/-! ## The clock ↔ multiplication-graph dictionary entry -/

/-- The model clock operator: channel `i` scales by its (distinct) clock
multiplier — the model avatar of the multiplication-by-`n` graph acting on
the Beauville-graded cohomology of an abelian variety. -/
noncomputable def clockOperator {order m : ℕ} (B : IntFrequencyBank m)
    (z : GeneralExtensionData order m) : GeneralExtensionData order m :=
  fun l i => (B.freq i : ℂ) * z l i

/-- The action of a polynomial in the clock operator: `P(S)` acts on
channel `i` by `P(freq i)` — a finite linear combination of clock powers,
i.e. of multiplication-graph correspondences in the algebraic avatar. -/
noncomputable def clockPolyAct {order m : ℕ} (B : IntFrequencyBank m)
    (P : Polynomial ℂ) (z : GeneralExtensionData order m) :
    GeneralExtensionData order m :=
  fun l i => P.eval ((B.freq i : ℤ) : ℂ) * z l i

/-- **The channel projectors are polynomials in the clock** (the
Vandermonde/Lagrange half of Deninger–Murre, at dictionary strength):
for each channel `i₀` there is a polynomial `P` with `P(S)` the exact
projector onto that channel.  In the algebraic avatar, `P(S)` is a
rational combination of multiplication-graph correspondences — algebraic
by construction — and these are the Chow–Künneth/Beauville projectors. -/
theorem clockChannelProjector {order m : ℕ} (B : IntFrequencyBank m)
    (i₀ : Fin m) :
    ∃ P : Polynomial ℂ, ∀ (z : GeneralExtensionData order m)
      (l : Fin (order + 1)) (i : Fin m),
      clockPolyAct B P z l i = if i = i₀ then z l i else 0 := by
  have hinj : Set.InjOn (fun i : Fin m => ((B.freq i : ℤ) : ℂ))
      ↑(Finset.univ : Finset (Fin m)) := fun a _ b _ hab =>
    B.injective (Int.cast_injective hab)
  refine ⟨Lagrange.interpolate Finset.univ
    (fun i : Fin m => ((B.freq i : ℤ) : ℂ))
    (fun i => if i = i₀ then 1 else 0), fun z l i => ?_⟩
  have hval := Lagrange.eval_interpolate_at_node
    (v := fun i : Fin m => ((B.freq i : ℤ) : ℂ))
    (r := fun i => if i = i₀ then (1:ℂ) else 0)
    hinj (Finset.mem_univ i)
  simp only [clockPolyAct, hval]
  by_cases hi : i = i₀
  · simp [hi]
  · simp [hi]

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.recognition_of_geometric
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_of_geometric
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.recognition_of_projector
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.sourceExhaustion_of_projector
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.clockChannelProjector
