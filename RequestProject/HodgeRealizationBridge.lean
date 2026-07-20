import RequestProject.HodgeSourceExhaustionAssembly

/-!
# The contentful model Hodge dial and the typed realization bridge

Upgrades the two register gaps of `GeneralExtensionRetention` into theorems, at exactly the
strength each admits:

1. **The contentful model dial.**  `generalExtensionDial` sets `DC = Rational = True` (worst case
   for retention, but no Hodge-theoretic content).  Here the predicates are genuine on the model:
   channel frequencies are integers `k = q - p` (`IntFrequencyBank`), `ModelDC` is support on the
   frequency-zero channels, `ModelRational` is rational amplitude.  `modelHodge_retention` proves
   retention for that dial — the statement now ranges over a genuine model rational-`(p,p)` locus.
   The proof still passes through full exhaustion (the worst case); the content is in the
   statement and in `modelDC_iff_angularFixed`, which machine-checks the harmonic dictionary's
   central entry **on the model**: a state is DC exactly when the angular part of the Deligne
   torus action fixes it.  This is the dictionary at dictionary strength — a re-expression, not
   an algebraicity statement.

2. **The typed bridge.**  `FaithfulRealization` types the five-condition faithful realization
   (paper §semisimple): (i) finite support and (ii) distinct frequencies are structural in the
   bank; (iii) rational structure, (iv) extension/regulator compatibility (additivity + readout
   identification), and (v) no kernel on the classes at issue are fields.
   `FaithfulRealization.retention` then proves **retention transports along any such
   realization** — no nonzero rational DC geometric class is silent — with first-visible depth
   preserved (`FaithfulRealization.isFirstVisible_iff`) and the terminus reduction specialized
   (`FaithfulRealization.sourceExhaustion_of_recognition`: a geometric dial admitting a faithful
   realization needs `Recognition` alone).

What this does **not** prove: retention for any actual cycle group, mixed Hodge structure,
normal function, or motivic extension.  Constructing the `FaithfulRealization` term for real
cycle data is the open arithmetic landing — after this file it is a single typed object to
construct, not a prose promise.  No `sorry`, no `axiom`.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-! ## The integer-frequency bank and the contentful predicates -/

/-- A finite bank of pairwise distinct **integer** channel frequencies `k = q - p` — the angular
data of a model Hodge decomposition. -/
structure IntFrequencyBank (m : ℕ) where
  freq : Fin m → ℤ
  injective : Function.Injective freq

/-- The associated complex clock bank: `ℤ ↪ ℂ` preserves distinctness. -/
noncomputable def IntFrequencyBank.toClockBank {m : ℕ} (B : IntFrequencyBank m) :
    DistinctClockBank m where
  frequency i := (B.freq i : ℂ)
  injective _ _ h := B.injective (Int.cast_injective h)

/-- **DC with content**: the state is supported on the frequency-zero channels at every jet
layer — the model form of type `(p,p)`. -/
def ModelDC {order m : ℕ} (B : IntFrequencyBank m) (z : GeneralExtensionData order m) : Prop :=
  ∀ (l : Fin (order + 1)) (i : Fin m), B.freq i ≠ 0 → z l i = 0

/-- **Rationality with content**: every amplitude is rational. -/
def ModelRational {order m : ℕ} (z : GeneralExtensionData order m) : Prop :=
  ∀ (l : Fin (order + 1)) (i : Fin m), ∃ q : ℚ, z l i = (q : ℂ)

/-- **The contentful model Hodge dial**: genuine frequency-zero `DC`, genuine rational-amplitude
`Rational`, the source predicate still arbitrary (recognition is not modeled here). -/
noncomputable def modelHodgeDial {order m : ℕ} (B : IntFrequencyBank m)
    (Algebraic : GeneralExtensionData order m → Prop) :
    HodgeDial (GeneralExtensionData order m) where
  DC := ModelDC B
  Rational := ModelRational
  Algebraic := Algebraic
  T := generalExtensionTower B.toClockBank

/-- **Retention on the contentful dial**: every nonzero rational frequency-zero state fires at
some paired layer/moment level.  Proved from the layerwise Vandermonde separation (full
exhaustion, the worst case); the upgrade over `generalExtension_retention` is that the statement
now quantifies over a genuine model rational-`(p,p)` locus rather than trivialized predicates. -/
theorem modelHodge_retention {order m : ℕ} (B : IntFrequencyBank m)
    (Algebraic : GeneralExtensionData order m → Prop) :
    Retention (modelHodgeDial B Algebraic) :=
  retention_of_exhaustive (generalExtensionTower_exhaustive B.toClockBank)

/-! ## The harmonic dictionary on the model, machine-checked -/

/-- The **angular part of the Deligne torus action** on the model: channel `i` turns at rate
`freq i`.  (The radial factor `r^{-n}` is channel-independent on a pure-weight structure, so the
angular action carries all channel information.) -/
noncomputable def angularAction {order m : ℕ} (B : IntFrequencyBank m) (theta : ℝ)
    (z : GeneralExtensionData order m) : GeneralExtensionData order m :=
  fun l i => Complex.exp (Complex.I * (B.freq i : ℂ) * (theta : ℂ)) * z l i

/-- **The dictionary entry, at dictionary strength**: a model state is DC exactly when the
angular torus action fixes it — `(p,p)` = frequency zero as a theorem on the model.  This
re-expresses the Hodge condition; it constructs nothing and says nothing about algebraicity. -/
theorem modelDC_iff_angularFixed {order m : ℕ} (B : IntFrequencyBank m)
    (z : GeneralExtensionData order m) :
    ModelDC B z ↔ ∀ theta : ℝ, angularAction B theta z = z := by
  constructor
  · intro hdc theta
    funext l i
    by_cases hk : B.freq i = 0
    · simp [angularAction, hk]
    · simp [angularAction, hdc l i hk]
  · intro hfix l i hk
    have hkC : (B.freq i : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h := congrFun (congrFun (hfix (Real.pi / (B.freq i : ℝ))) l) i
    simp only [angularAction] at h
    have harg : Complex.I * (B.freq i : ℂ) * ((Real.pi / (B.freq i : ℝ) : ℝ) : ℂ)
        = (Real.pi : ℂ) * Complex.I := by
      push_cast
      field_simp
    rw [harg, Complex.exp_pi_mul_I] at h
    have h2 : (2 : ℂ) * z l i = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ## The five-condition realization, typed -/

/-- **The five-condition faithful realization** of a geometric dial into the contentful model:
(i) finite support and (ii) distinct frequencies are structural (the bank is finite with
injective frequencies); (iii) rational structure, (iv) extension/regulator compatibility
(additivity of the realization + identification of the geometric readouts with the paired
layer/moment tower), and (v) no kernel on the classes at issue are the fields below.
Constructing a term of this structure for actual cycle data is the open arithmetic landing. -/
structure FaithfulRealization {Zg : Type*} [AddCommGroup Zg] (Dg : HodgeDial Zg)
    (order : ℕ) {m : ℕ} (B : IntFrequencyBank m) where
  /-- (iv-a) the realization is additive — compatible with the extension/group structure. -/
  toModel : Zg →+ GeneralExtensionData order m
  /-- (iv-b) the geometric readouts are exactly the paired layer/moment tower of the image. -/
  regCompat : ∀ (d : ℕ) (z : Zg), Dg.T d z = generalExtensionTower B.toClockBank d (toModel z)
  /-- (iii) rationality is read on the DC locus: a rational DC geometric class lands in the
  model's rational structure.  The unconditional form (every rational class channel-rational)
  is provably false in genuine instances — channel amplitudes of a rational class are
  Galois-spread, rational only where the class concentrates, on the DC channels.  Discovered by
  constructing the cyclic instance (`CyclicRealizationInstance.lean`); no bridge theorem
  consumed the stronger form. -/
  ratCompat : ∀ z : Zg, Dg.DC z → Dg.Rational z → ModelRational (toModel z)
  /-- (iii') DC geometric classes land on the model's frequency-zero locus. -/
  dcCompat : ∀ z : Zg, Dg.DC z → ModelDC B (toModel z)
  /-- (v) no kernel on the geometric classes at issue. -/
  noKernel : ∀ z : Zg, Dg.DC z → Dg.Rational z → toModel z = 0 → z = 0

/-- **Retention transports along any faithful realization**: no nonzero rational DC geometric
class is silent — its image is nonzero by (v), the layerwise Vandermonde separation fires on the
image, and (iv-b) pulls the firing back to the geometric readout. -/
theorem FaithfulRealization.retention {Zg : Type*} [AddCommGroup Zg] {Dg : HodgeDial Zg}
    {order m : ℕ} {B : IntFrequencyBank m} (R : FaithfulRealization Dg order B) :
    Retention Dg := by
  intro z hz hdc hrat
  have hmodel : R.toModel z ≠ 0 := fun h0 => hz (R.noKernel z hdc hrat h0)
  obtain ⟨d, hd⟩ := generalExtensionTower_exhaustive B.toClockBank (R.toModel z) hmodel
  exact ⟨d, by rw [R.regCompat]; exact hd⟩

/-- **Depth is preserved**: along a faithful realization the geometric first-visible depth equals
the model first-visible depth (consumes the transport lemmas of the dictionary file, with the
identity intertwiner supplied by `regCompat`). -/
theorem FaithfulRealization.isFirstVisible_iff {Zg : Type*} [AddCommGroup Zg]
    {Dg : HodgeDial Zg} {order m : ℕ} {B : IntFrequencyBank m}
    (R : FaithfulRealization Dg order B) (z : Zg) (d : ℕ) :
    IsFirstVisible (generalExtensionTower B.toClockBank) (R.toModel z) d ↔
      IsFirstVisible Dg.T z d :=
  isFirstVisible_map_iff (R.toModel : Zg → GeneralExtensionData order m) Dg.T
    (generalExtensionTower B.toClockBank) (fun _ => id) (fun _ => rfl)
    (fun _ => Function.injective_id) (fun j w => (R.regCompat j w).symm)

/-- **The geometric terminus reduction along a realization**: a geometric dial admitting a
five-condition faithful realization needs `Recognition` alone — retention is supplied by the
bridge, unconditionally. -/
theorem FaithfulRealization.sourceExhaustion_of_recognition {Zg : Type*} [AddCommGroup Zg]
    {Dg : HodgeDial Zg} {order m : ℕ} {B : IntFrequencyBank m}
    (R : FaithfulRealization Dg order B) (hrec : Recognition Dg) :
    SourceExhaustion Dg :=
  hodge_of_retention_recognition R.retention hrec

/-- Sanity: the contentful model dial faithfully realizes itself (the structure is inhabited;
the arithmetic instances are the open constructions). -/
noncomputable def idRealization {order m : ℕ} (B : IntFrequencyBank m)
    (Algebraic : GeneralExtensionData order m → Prop) :
    FaithfulRealization (modelHodgeDial B Algebraic) order B where
  toModel := AddMonoidHom.id _
  regCompat _ _ := rfl
  ratCompat _ _ h := h
  dcCompat _ h := h
  noKernel _ _ _ h := h

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.modelHodge_retention
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.modelDC_iff_angularFixed
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.FaithfulRealization.retention
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.FaithfulRealization.isFirstVisible_iff
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.FaithfulRealization.sourceExhaustion_of_recognition
