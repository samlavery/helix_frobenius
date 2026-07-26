import RequestProject.HodgeRealizationBridge

/-!
# The model Green operator: classical Hodge theory's pseudoinverse, at
# dictionary strength

The classical facts — the Hodge Laplacian's kernel is the harmonic forms,
the Green operator is its Moore–Penrose pseudoinverse, and every form
splits as harmonic part plus a piece in the Laplacian's image — hold on
the contentful model verbatim, with the dictionary identifications proven
rather than analogized:

* the model Laplacian acts channelwise by `freq²` (the second derivative
  of the angular Deligne-torus action);
* its kernel is EXACTLY the frequency-zero locus (`ModelDC`, the model
  form of type `(p,p)`), hence exactly the torus-fixed states — composing
  with `modelDC_iff_angularFixed` closes the classical chain
  harmonic ⟺ `(p,p)`-DC ⟺ torus-fixed (`modelHarmonic_iff_angularFixed`);
* the Green operator inverts on the nonzero-frequency channels and kills
  the harmonic part; the four Moore–Penrose-style identities and the
  model Hodge decomposition `z = harmonic ⊕ Δ(Green z)` are theorems,
  with the harmonic part unique.

Register: dictionary strength only.  This completes the classical-Hodge
column of the harmonic dictionary; it constructs no cycle and says
nothing about algebraicity — the pencil whose rank behavior detects
algebraic classes is the channel-constancy Gram, a different object.
Scope: does not assume or prove RH/GRH or the Hodge conjecture.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {order m : ℕ} (B : IntFrequencyBank m)

/-- The model Hodge Laplacian: channel `i` scales by `freq i ²` — the
(negated) second derivative of the angular torus action. -/
noncomputable def modelLaplacian (z : GeneralExtensionData order m) :
    GeneralExtensionData order m :=
  fun l i => ((B.freq i : ℂ)) ^ 2 * z l i

/-- The harmonic projector: restriction to the frequency-zero channels —
in the dictionary, projection onto the `(p,p)`-DC locus. -/
noncomputable def dcProjector (z : GeneralExtensionData order m) :
    GeneralExtensionData order m :=
  fun l i => if B.freq i = 0 then z l i else 0

/-- The model Green operator: the Moore–Penrose pseudoinverse of the
model Laplacian — zero on the harmonic (DC) channels, `freq⁻²` on the
rest. -/
noncomputable def greenOperator (z : GeneralExtensionData order m) :
    GeneralExtensionData order m :=
  fun l i => if B.freq i = 0 then 0 else ((B.freq i : ℂ) ^ 2)⁻¹ * z l i

/-- **Kernel = harmonic = DC**: the model Laplacian annihilates a state
iff it is supported on the frequency-zero channels. -/
theorem modelLaplacian_eq_zero_iff (z : GeneralExtensionData order m) :
    modelLaplacian B z = 0 ↔ ModelDC B z := by
  constructor
  · intro h l i hi
    have hli := congrFun (congrFun h l) i
    simp only [modelLaplacian, Pi.zero_apply] at hli
    have hk : ((B.freq i : ℂ)) ^ 2 ≠ 0 :=
      pow_ne_zero _ (Int.cast_ne_zero.mpr hi)
    exact (mul_eq_zero.mp hli).resolve_left hk
  · intro h
    funext l i
    by_cases hi : B.freq i = 0
    · simp [modelLaplacian, hi]
    · simp [modelLaplacian, h l i hi]

/-- **The classical chain closed on the model**: harmonic ⟺ torus-fixed —
the Laplacian kernel is exactly the fixed locus of the angular Deligne
torus action, through the DC dictionary entry. -/
theorem modelHarmonic_iff_angularFixed (z : GeneralExtensionData order m) :
    modelLaplacian B z = 0 ↔ ∀ theta : ℝ, angularAction B theta z = z :=
  (modelLaplacian_eq_zero_iff B z).trans (modelDC_iff_angularFixed B z)

/-- The Green operator kills harmonic states. -/
theorem greenOperator_eq_zero_of_dc (z : GeneralExtensionData order m)
    (h : ModelDC B z) : greenOperator B z = 0 := by
  funext l i
  by_cases hi : B.freq i = 0
  · simp [greenOperator, hi]
  · simp [greenOperator, hi, h l i hi]

/-- `Δ ∘ G = G ∘ Δ = id − harmonic projector`: the two compositions agree
and are the co-harmonic projector — the structural form of the
Moore–Penrose symmetry conditions (the operator is channel-diagonal and
real, hence self-adjoint in any channelwise inner product). -/
theorem laplacian_green_eq_sub_dc (z : GeneralExtensionData order m) :
    modelLaplacian B (greenOperator B z) = z - dcProjector B z := by
  funext l i
  by_cases hi : B.freq i = 0
  · simp [modelLaplacian, greenOperator, dcProjector, hi]
  · have hk : ((B.freq i : ℂ)) ^ 2 ≠ 0 :=
      pow_ne_zero _ (Int.cast_ne_zero.mpr hi)
    simp only [modelLaplacian, greenOperator, dcProjector, if_neg hi,
      Pi.sub_apply]
    rw [sub_zero, ← mul_assoc, mul_inv_cancel₀ hk, one_mul]

theorem green_laplacian_eq_sub_dc (z : GeneralExtensionData order m) :
    greenOperator B (modelLaplacian B z) = z - dcProjector B z := by
  funext l i
  by_cases hi : B.freq i = 0
  · simp [modelLaplacian, greenOperator, dcProjector, hi]
  · have hk : ((B.freq i : ℂ)) ^ 2 ≠ 0 :=
      pow_ne_zero _ (Int.cast_ne_zero.mpr hi)
    simp only [modelLaplacian, greenOperator, dcProjector, if_neg hi,
      Pi.sub_apply]
    rw [sub_zero, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

/-- Moore–Penrose identity 1: `Δ G Δ = Δ`. -/
theorem laplacian_green_laplacian (z : GeneralExtensionData order m) :
    modelLaplacian B (greenOperator B (modelLaplacian B z))
      = modelLaplacian B z := by
  rw [green_laplacian_eq_sub_dc]
  funext l i
  by_cases hi : B.freq i = 0
  · simp [modelLaplacian, dcProjector, hi]
  · simp [modelLaplacian, dcProjector, hi, Pi.sub_apply]

/-- Moore–Penrose identity 2: `G Δ G = G`. -/
theorem green_laplacian_green (z : GeneralExtensionData order m) :
    greenOperator B (modelLaplacian B (greenOperator B z))
      = greenOperator B z := by
  rw [laplacian_green_eq_sub_dc]
  funext l i
  by_cases hi : B.freq i = 0
  · simp [greenOperator, dcProjector, hi]
  · simp [greenOperator, dcProjector, hi, Pi.sub_apply]

/-- **The model Hodge decomposition**: every state is its harmonic (DC)
part plus a Laplacian image, `z = P_harm z + Δ (G z)`. -/
theorem hodge_decomposition (z : GeneralExtensionData order m) :
    z = dcProjector B z + modelLaplacian B (greenOperator B z) := by
  rw [laplacian_green_eq_sub_dc]
  funext l i
  simp

/-- **Uniqueness of the harmonic part**: if `z = h + Δ w` with `h`
harmonic (DC), then `h` is the harmonic projection of `z`. -/
theorem harmonic_part_unique (z h w : GeneralExtensionData order m)
    (hh : ModelDC B h) (hz : z = h + modelLaplacian B w) :
    h = dcProjector B z := by
  funext l i
  by_cases hi : B.freq i = 0
  · have := congrFun (congrFun hz l) i
    simp only [Pi.add_apply, modelLaplacian, hi] at this
    simp only [dcProjector, if_pos hi, this]
    push_cast
    ring
  · simp [dcProjector, hi, hh l i hi]

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.modelHarmonic_iff_angularFixed
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.hodge_decomposition
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.laplacian_green_laplacian
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.green_laplacian_green
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.harmonic_part_unique
