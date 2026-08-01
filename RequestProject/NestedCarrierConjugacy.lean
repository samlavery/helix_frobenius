import Mathlib

/-!
# The conjugacy theorem: nested spheres ≅ ledgered carrier

The correspondent's theorem (2026-07-29), formalized: the nested-sphere
system and the ledgered carrier are two coordinate systems for the same
complete state — conjugate as dynamical systems with projection and
retained-loss structure.

    Φ ∘ T_S = T_C ∘ Φ,     P_C ∘ Φ = P_S,     L_C ∘ Φ = L_S.

The single substantive hypothesis — *every geometrically relevant sphere
coordinate discarded by the visible projection is retained in the carrier
ledger, including the ordered factorization of nested rotations* — is
embodied here as a DEFINITION: the ledger stack retains each depth's
child datum wholesale (`LedgerStack`), so `Flatten` is the associativity
re-bracketing of the nesting tree and nothing else.  Under that
retention:

* `flatten` — the state bijection Φ, an `Equiv` built by induction on
  nesting depth (base: identity; step: re-associate) — where
  `record_bijective` belongs, exactly as predicted;
* `transport_intertwines` — Φ ∘ T_S = T_C ∘ Φ: the child update reads its
  (pre-step) parent frame on both sides; the carrier side reconstructs
  the frame through Φ⁻¹, which is the formal content of "the ledger
  stores the ordered composition";
* `readout_compat` — P_C ∘ Φ = P_S for the multiplicative one-dimensional
  readout; with base data (H_n, n^{-1/2}, t·log n) the summed readout is
  the truncated critical phasor Σ n^{-1/2-it};
* `flatten_injective` — Φ-equality is state equality (full-state
  faithfulness), while `projected_eq_ne_state_eq` exhibits the strict gap
  for the bare readout: the booked winding (θ vs θ+2π) is invisible to
  the phasor but retained by the ledger — projected equality is NOT state
  equality, exactly the distinction the loss ledger exists to hold.

"Nearly definitional — but importantly, not vacuous": the theorem is the
license to apply the entire existing carrier theorem suite to the
nested-sphere geometry verbatim.
-/

namespace CriticalLinePhasor.NestedConjugacy

/-- The depth-zero base state: harmonic coordinate, radial amplitude,
accumulated phase. -/
structure BaseState where
  pos : ℝ
  radius : ℝ
  phase : ℝ

variable (Child : ℕ → Type)

/-- The nested-sphere state: base state with one child datum adjoined per
nesting level (rotation, attachment, orientation — whatever the level
carries). -/
def SphereState : ℕ → Type
  | 0 => BaseState
  | d + 1 => SphereState d × Child d

/-- The carrier's ledger stack: the same child data, serialized. -/
def LedgerStack : ℕ → Type
  | 0 => PUnit
  | d + 1 => LedgerStack d × Child d

/-- **Φ, the state bijection**: nested state ≅ base × ledger stack, by
induction on depth — the re-bracketing of the nesting tree, information
preserved wholesale. -/
def flatten : (d : ℕ) → SphereState Child d ≃ BaseState × LedgerStack Child d
  | 0 => (Equiv.prodPUnit BaseState).symm
  | d + 1 =>
    ((flatten d).prodCongr (Equiv.refl (Child d))).trans
      (Equiv.prodAssoc BaseState (LedgerStack Child d) (Child d))

/-- Full-state faithfulness: Φ-equality is state equality. -/
theorem flatten_injective (d : ℕ) :
    Function.Injective (flatten Child d) :=
  (flatten Child d).injective

section Transport

variable (baseStep : BaseState → BaseState)
variable (childStep : ∀ d, SphereState Child d → Child d → Child d)

/-- The nested transport: the base advances; each child advances in its
(pre-step) parent frame. -/
def sphereStep : (d : ℕ) → SphereState Child d → SphereState Child d
  | 0 => baseStep
  | d + 1 => fun sc =>
      (sphereStep d sc.1, childStep d sc.1 sc.2)

/-- The carrier transport on the flattened state: the same updates, with
each level's parent frame RECONSTRUCTED from the ledger through Φ⁻¹ —
the formal content of "the ledger stores the ordered composition". -/
def carrierStep : (d : ℕ) →
    BaseState × LedgerStack Child d → BaseState × LedgerStack Child d
  | 0 => fun bu => (baseStep bu.1, bu.2)
  | d + 1 => fun blc =>
      let s := (flatten Child d).symm (blc.1, blc.2.1)
      let prev := carrierStep d (blc.1, blc.2.1)
      (prev.1, (prev.2, childStep d s blc.2.2))

/-- **Transport intertwining**: Φ ∘ T_S = T_C ∘ Φ, at every nesting
depth. -/
theorem transport_intertwines : ∀ (d : ℕ) (s : SphereState Child d),
    flatten Child d (sphereStep Child baseStep childStep d s)
      = carrierStep Child baseStep childStep d (flatten Child d s)
  | 0, s => rfl
  | d + 1, sc => by
    obtain ⟨s, c⟩ := sc
    have ih := transport_intertwines d s
    show ((flatten Child d (sphereStep Child baseStep childStep d s)).1,
        ((flatten Child d (sphereStep Child baseStep childStep d s)).2,
          childStep d s c))
      = ((carrierStep Child baseStep childStep d (flatten Child d s)).1,
        ((carrierStep Child baseStep childStep d (flatten Child d s)).2,
          childStep d ((flatten Child d).symm (flatten Child d s)) c))
    rw [ih, (flatten Child d).symm_apply_apply s]

end Transport

section Readout

variable (rho : ∀ d, Child d → ℂ)

/-- The base readout: the phasor `R·e^{iθ}` — with base data
`(H_n, n^{-1/2}, t log n)` this is `n^{-1/2} e^{i t log n}`, and the
summed bank is the truncated critical phasor series. -/
noncomputable def baseReadout (b : BaseState) : ℂ :=
  (b.radius : ℂ) * Complex.exp (Complex.I * (b.phase : ℂ))

/-- The nested readout: multiplicative through the levels. -/
noncomputable def sphereReadout : (d : ℕ) → SphereState Child d → ℂ
  | 0 => baseReadout
  | d + 1 => fun sc => sphereReadout d sc.1 * rho d sc.2

/-- The carrier readout on the flattened state. -/
noncomputable def carrierReadout : (d : ℕ) →
    BaseState × LedgerStack Child d → ℂ
  | 0 => fun bu => baseReadout bu.1
  | d + 1 => fun blc => carrierReadout d (blc.1, blc.2.1) * rho d blc.2.2

/-- **Readout compatibility**: P_C ∘ Φ = P_S. -/
theorem readout_compat : ∀ (d : ℕ) (s : SphereState Child d),
    carrierReadout Child rho d (flatten Child d s)
      = sphereReadout Child rho d s
  | 0, s => rfl
  | d + 1, sc => by
    obtain ⟨s, c⟩ := sc
    have ih := readout_compat d s
    show carrierReadout Child rho d (flatten Child d s) * rho d c
        = sphereReadout Child rho d s * rho d c
    rw [ih]

/-- **Projected equality is not state equality**: the booked winding —
two base states differing by a full turn have identical phasor readouts
and distinct states; only the Φ-image (which carries the ledger) is
faithful.  The gap the loss ledger exists to hold, exhibited. -/
theorem projected_eq_ne_state_eq :
    ∃ b b' : BaseState, baseReadout b = baseReadout b' ∧ b ≠ b' := by
  refine ⟨⟨0, 1, 0⟩, ⟨0, 1, 2 * Real.pi⟩, ?_, ?_⟩
  · show ((1:ℝ) : ℂ) * Complex.exp (Complex.I * ((0:ℝ) : ℂ))
        = ((1:ℝ) : ℂ) * Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ))
    have h2pi : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ)
          = 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    rw [h2pi]
    simp
  · intro h
    have hph := congrArg BaseState.phase h
    simp only at hph
    exact Real.pi_ne_zero (by linarith)

end Readout

/-! ## The abstract conjugacy layer (the correspondent's structures) and
the closed instance

The general mechanism, verbatim from the review dialogue, then
instantiated: `encode := flatten`, `step_commutes := transport_intertwines`
(the "exact cable" — the one lemma the dialogue could not prove without
the repository), `readout_commutes := readout_compat`.  All finite
iterates then commute and the visible trajectories agree. -/

/-- A dynamical system with a visible readout. -/
structure Dynamics (State Output : Type*) where
  step : State → State
  readout : State → Output

/-- A conjugacy of readout dynamics: lossless encoding commuting with
transport and readout. -/
structure Conjugacy {S C O : Type*} (sphere : Dynamics S O)
    (carrier : Dynamics C O) where
  encode : S ≃ C
  step_commutes : ∀ s, encode (sphere.step s) = carrier.step (encode s)
  readout_commutes : ∀ s, carrier.readout (encode s) = sphere.readout s

/-- All finite iterates commute. -/
theorem Conjugacy.iterate_conjugacy {S C O : Type*}
    {sphere : Dynamics S O} {carrier : Dynamics C O}
    (h : Conjugacy sphere carrier) (k : ℕ) (s : S) :
    h.encode ((sphere.step)^[k] s) = (carrier.step)^[k] (h.encode s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      h.step_commutes, ih]

/-- The visible trajectories agree at every time. -/
theorem Conjugacy.iterate_readout_eq {S C O : Type*}
    {sphere : Dynamics S O} {carrier : Dynamics C O}
    (h : Conjugacy sphere carrier) (k : ℕ) (s : S) :
    carrier.readout ((carrier.step)^[k] (h.encode s))
      = sphere.readout ((sphere.step)^[k] s) := by
  rw [← h.iterate_conjugacy k s]
  exact h.readout_commutes _

section Instance

variable (Child : ℕ → Type) (d : ℕ)
variable (baseStep : BaseState → BaseState)
variable (childStep : ∀ k, SphereState Child k → Child k → Child k)
variable (rho : ∀ k, Child k → ℂ)

/-- The nested-sphere dynamics at depth `d`. -/
noncomputable def sphereDynamics : Dynamics (SphereState Child d) ℂ where
  step := sphereStep Child baseStep childStep d
  readout := sphereReadout Child rho d

/-- The ledgered-carrier dynamics at depth `d`. -/
noncomputable def carrierDynamics :
    Dynamics (BaseState × LedgerStack Child d) ℂ where
  step := carrierStep Child baseStep childStep d
  readout := carrierReadout Child rho d

/-- **The conjugacy theorem, closed**: the nested-sphere system and the
ledgered carrier are conjugate at every finite nesting depth — the
project-specific `hstep` is `transport_intertwines`, proven above. -/
noncomputable def nestedCarrierConjugacy :
    Conjugacy (sphereDynamics Child d baseStep childStep rho)
      (carrierDynamics Child d baseStep childStep rho) where
  encode := flatten Child d
  step_commutes := transport_intertwines Child baseStep childStep d
  readout_commutes := readout_compat Child rho d

end Instance

end CriticalLinePhasor.NestedConjugacy

#print axioms CriticalLinePhasor.NestedConjugacy.nestedCarrierConjugacy
#print axioms CriticalLinePhasor.NestedConjugacy.Conjugacy.iterate_readout_eq
#print axioms CriticalLinePhasor.NestedConjugacy.flatten_injective
#print axioms CriticalLinePhasor.NestedConjugacy.transport_intertwines
#print axioms CriticalLinePhasor.NestedConjugacy.readout_compat
#print axioms CriticalLinePhasor.NestedConjugacy.projected_eq_ne_state_eq
