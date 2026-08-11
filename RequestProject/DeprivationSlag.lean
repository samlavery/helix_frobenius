import Mathlib

/-!
# The deprivation slag: exact algebra, and the tombstone

The closing record of the Euler-deprivation route to the rung-five
containment (Sato–Tate closure campaign, 2026-08-10).  Deprivation at a
prime acts on the two-dimensional mode plane of a defect ledger entry as a
hyperbolic translation; in the reflection-parity basis its mixing
coefficient — the *slag* — is exactly `(Ex − Ey)/2`, where `Ex, Ey` are the
local Euler polynomial's values at the two mode exponents.  The route hoped
to force `Ex = Ey` primewise from the system's own constraints.  It cannot:

* `slag_offDiagonal` / `defectLine_eigen_iff` — **the exact algebra**: the
  deprivation matrix in the parity basis has off-diagonal `(Ex − Ey)/2`,
  and preserves the defect parity line *iff* `Ex = Ey`;
* `deprived_antiReflective` — **the vacuity**: the transported ledger data
  satisfies the anti-reflection (defect) identity for EVERY residue and
  every pair `(Ex, Ey)` — anti-reflection compares the two ends of the
  carrier across the reflection and never compares parities at the same
  end, so it is blind to the mixing;
* `deprived_parityPure_iff` — **the constraint located**: parity purity of
  the transported data is equivalent to `r = 0 ∨ Ex = Ey`;
* `purity_not_forced` — **THE TOMBSTONE**: for every `r ≠ 0`, `Ex ≠ Ey`,
  the transported data is anti-reflective and NOT parity-pure.  The
  internal machinery (annihilation pairing + anti-reflection) cannot force
  the primewise equality; the analytic counterpart (the T₃-translate
  pairing) vanishes on the whole mode plane at denominator zeros, and
  parity purity of the deprived defect is equivalent to a functional
  equation for the deprived Mellin transform — the very symmetry
  deprivation breaks.

Register.  The route is closed at this named junction; the constraint
`Ex = Ey` survives only as the *definition* of what an external detector
must certify.  The replacement cable (registered 2026-08-10): finite
residue ledger ⟹ finite-pole twisted quotient family
`Q_χ = Λ((f×Sym⁴f)⊗χ)/Λ(Sym³f⊗χ)` ⟹ hyperbolic/converse rigidity in the
Neururer–Oliver two-circles class (a genuinely same-side detector) ⟹
Sym⁵ object ⟹ containment.  The open question is whether the Sym⁵-shaped
archimedean progression and Euler structure let GL(1) twists suffice at
degree six.  No `axiom`, no `sorry`.
-/

namespace CriticalLinePhasor.DeprivationSlag

open Matrix

/-! ## The boost algebra: slag is the off-diagonal -/

/-- The deprivation operator on a mode plane in the exponential basis:
diagonal with the two local Euler values. -/
def expMatrix (Ex Ey : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Ex, 0; 0, Ey]

/-- The same operator in the reflection-parity basis. -/
noncomputable def parityMatrix (Ex Ey : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/2 : ℂ) • (!![1, 1; 1, -1] * expMatrix Ex Ey * !![1, 1; 1, -1])

theorem parityMatrix_eq (Ex Ey : ℂ) :
    parityMatrix Ex Ey =
      !![(Ex + Ey)/2, (Ex - Ey)/2; (Ex - Ey)/2, (Ex + Ey)/2] := by
  unfold parityMatrix expMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal,
        Fin.sum_univ_two]
      ring

/-- **The slag is the off-diagonal entry**: exact mixing coefficient
`(Ex − Ey)/2` into the opposite parity sector. -/
theorem slag_offDiagonal (Ex Ey : ℂ) :
    parityMatrix Ex Ey 0 1 = (Ex - Ey)/2 := by
  rw [parityMatrix_eq]
  simp

/-- **The defect parity line is preserved iff the primewise equality holds.** -/
theorem defectLine_eigen_iff (Ex Ey : ℂ) :
    (∃ c : ℂ, (parityMatrix Ex Ey).mulVec ![1, 0] = c • ![1, 0]) ↔ Ex = Ey := by
  rw [parityMatrix_eq]
  constructor
  · rintro ⟨c, hc⟩
    have h1 := congrFun hc 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1
    have h2 : Ex - Ey = 0 := by
      first
      | exact h1
      | linear_combination h1
      | linear_combination 2 * h1
    exact sub_eq_zero.mp h2
  · intro h
    refine ⟨(Ex + Ey)/2, ?_⟩
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]

/-! ## The two-ended ledger data: vacuity of anti-reflection -/

/-- Power content of a defect-type object at its two carrier ends: the
`v^ρ` and `v^{1−ρ}` coefficients at `v → ∞` and at `v → 0`. -/
structure TwoEndedPowerData where
  aInf : ℂ
  bInf : ℂ
  a0 : ℂ
  b0 : ℂ

/-- The anti-reflection (defect) identity on end data: the content at one
end is the reflected content of the other. -/
def AntiReflective (ε : ℂ) (d : TwoEndedPowerData) : Prop :=
  d.aInf = -ε * d.b0 ∧ d.bInf = -ε * d.a0

/-- Parity purity: the same power content at both ends — the property a
genuine two-sided mode superposition has. -/
def ParityPure (d : TwoEndedPowerData) : Prop :=
  d.aInf = d.a0 ∧ d.bInf = d.b0

/-- The transported (deprived) content of a ledger mode with residue `r`:
weights `Ex, Ey` at infinity and the swapped pair at zero — the exact
outcome of the transport computation. -/
def deprivedData (ε r Ex Ey : ℂ) : TwoEndedPowerData :=
  ⟨r * Ex, -ε * (r * Ey), r * Ey, -ε * (r * Ex)⟩

/-- **Vacuity**: the transported ledger is anti-reflective for EVERY
residue and every pair of Euler values — the defect identity carries no
constraint. -/
theorem deprived_antiReflective (ε r Ex Ey : ℂ) (hε : ε ^ 2 = 1) :
    AntiReflective ε (deprivedData ε r Ex Ey) := by
  constructor
  · show r * Ex = -ε * (-ε * (r * Ex))
    linear_combination (-(r * Ex)) * hε
  · show -ε * (r * Ey) = -ε * (r * Ey)
    rfl

/-- **The constraint, located**: parity purity of the transported ledger
is exactly `r = 0 ∨ Ex = Ey`. -/
theorem deprived_parityPure_iff (ε r Ex Ey : ℂ) (hε : ε ≠ 0) :
    ParityPure (deprivedData ε r Ex Ey) ↔ (r = 0 ∨ Ex = Ey) := by
  constructor
  · rintro ⟨h1, _⟩
    have hz : r * (Ex - Ey) = 0 := by
      have h1' : r * Ex = r * Ey := h1
      linear_combination h1'
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (h | h)
    · constructor <;> simp [deprivedData, h]
    · constructor <;> simp [deprivedData, h]

/-- **THE TOMBSTONE.**  Whenever the ledger is occupied (`r ≠ 0`) and the
Euler values differ, the transported data satisfies every identity the
internal system can impose (anti-reflection) and is NOT parity-pure: the
deprivation route cannot force the primewise equality from within. -/
theorem purity_not_forced (ε r Ex Ey : ℂ) (hε : ε ^ 2 = 1) (hε0 : ε ≠ 0)
    (hr : r ≠ 0) (hxy : Ex ≠ Ey) :
    AntiReflective ε (deprivedData ε r Ex Ey) ∧
      ¬ ParityPure (deprivedData ε r Ex Ey) := by
  refine ⟨deprived_antiReflective ε r Ex Ey hε, ?_⟩
  rw [deprived_parityPure_iff ε r Ex Ey hε0]
  rintro (h | h)
  · exact hr h
  · exact hxy h

end CriticalLinePhasor.DeprivationSlag

#print axioms CriticalLinePhasor.DeprivationSlag.slag_offDiagonal
#print axioms CriticalLinePhasor.DeprivationSlag.defectLine_eigen_iff
#print axioms CriticalLinePhasor.DeprivationSlag.deprived_antiReflective
#print axioms CriticalLinePhasor.DeprivationSlag.purity_not_forced
