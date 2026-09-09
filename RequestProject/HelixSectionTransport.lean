import RequestProject.HelixCellSections3D
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Transport for the finite section construction.

The two candidates are tested separately. Scalar Cayley transport has exact
constant norm at every power. Multiplication by X on Taylor jets has a shift
term: (P(a), P'(a)) is sent to (a P(a), P(a) + a P'(a)). At the actual carrier
height zero, a = -1, this term grows linearly in the power.

The DC (power zero) is the identity. The carrier phase has modulus one; the
remaining contribution in the two-jet model is the first-order Taylor shift.
The formulas retain this contribution before estimating the norm.

Searches: `rg -n 'castelnuovo|cup_growth|cupGrowth|hgrow|transport.*norm|
norm.*transport|powerBound|power_bound' RequestProject .lake/packages/mathlib/Mathlib`;
`rg -n 'Jordan.*pow|jordan.*pow|pow.*Jordan|taylor_mul|coeff_X_mul|
tendsto.*pow.*mul.*zero' .lake/packages/mathlib/Mathlib`.
LeanSearch: polynomial times a geometric sequence tends to zero.
Loogle: `Filter.Tendsto, "pow", "mul", "zero"`.
-/

open Complex Polynomial ConeProjection
open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Readout

namespace CriticalLinePhasor.HelixSectionTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The scalar phase action on the carrier space. -/
noncomputable def phaseTransport (f : Fiber) : E →ₗ[ℂ] E :=
  circleReadout f • LinearMap.id

theorem phaseTransport_pow (f : Fiber) (v : E) (k : ℕ) :
    (phaseTransport f ^ k) v = circleReadout f ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change circleReadout f • (circleReadout f ^ k • v) = _
    rw [smul_smul, pow_succ']

/-- The power bound for this specified transport is an exact equality. -/
theorem phaseTransport_power_norm (f : Fiber) (v : E) (k : ℕ) :
    ‖(phaseTransport f ^ k) v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [phaseTransport_pow, norm_smul, norm_pow, circleReadout_norm_one, one_pow, one_mul]

/-- Multiplication by the coordinate on the two-jet space. -/
noncomputable def twoJetTransport (a : ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun v := (a * v.1, v.1 + a * v.2)
  map_add' v w := by ext <;> simp <;> ring
  map_smul' b v := by ext <;> simp <;> ring

/-- The operator comes from the actual polynomial jet map, including its shift term. -/
theorem twoJetTransport_taylor (a : ℂ) (P : ℂ[X]) :
    twoJetTransport a ((Polynomial.taylor a P).coeff 0, (Polynomial.taylor a P).coeff 1) =
      ((Polynomial.taylor a (X * P)).coeff 0, (Polynomial.taylor a (X * P)).coeff 1) := by
  rw [Polynomial.taylor_mul, Polynomial.taylor_X, add_mul]
  ext <;> simp [twoJetTransport, Polynomial.coeff_X_mul]

/-- Height zero is an actual carrier node; its Cayley readout is minus one. -/
theorem circleReadout_height_zero (r θ : ℝ) :
    circleReadout (r, θ, 0) = -1 := by
  norm_num [circleReadout, height, cayley]

theorem twoJetTransport_pow_neg_one (k : ℕ) :
    (twoJetTransport (-1) ^ k) (1, 0) =
      ((-1 : ℂ) ^ k, -(k : ℂ) * (-1 : ℂ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    ext <;> simp [twoJetTransport, pow_succ, Nat.cast_add, Nat.cast_one]; ring

theorem twoJetTransport_power_second_norm (k : ℕ) :
    ‖((twoJetTransport (-1) ^ k) (1, 0)).2‖ = k := by
  rw [twoJetTransport_pow_neg_one]
  simp

theorem twoJetTransport_power_norm_le (k : ℕ) :
    ‖(twoJetTransport (-1) ^ k) (1, 0)‖ ≤ 1 + (k : ℝ) := by
  rw [twoJetTransport_pow_neg_one, Prod.norm_def]
  simp only [norm_pow, norm_neg, norm_one, one_pow, norm_mul, Complex.norm_natCast, mul_one]
  exact max_le (le_add_of_nonneg_right (Nat.cast_nonneg k)) (by linarith)

/-- Retaining multiplicity gives a proved polynomial envelope. -/
theorem twoJetTransport_power_sq_le (k : ℕ) :
    ‖(twoJetTransport (-1) ^ k) (1, 0)‖ ^ 2 ≤ 2 * (1 + (k : ℝ) ^ 2) := by
  have h := twoJetTransport_power_norm_le k
  have hnorm := norm_nonneg ((twoJetTransport (-1) ^ k) (1, 0))
  nlinarith [sq_nonneg ((k : ℝ) - 1)]

/-- The multiplicity-two transport has no constant power envelope. -/
theorem twoJetTransport_not_power_bounded :
    ¬ ∃ C : ℝ, ∀ k : ℕ, ‖(twoJetTransport (-1) ^ k) (1, 0)‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have hle := norm_snd_le ((twoJetTransport (-1) ^ k) (1, 0))
  rw [twoJetTransport_power_second_norm] at hle
  exact (not_lt_of_ge (hle.trans (hC k))) hk

#print axioms phaseTransport_power_norm
#print axioms twoJetTransport_taylor
#print axioms twoJetTransport_not_power_bounded
#print axioms twoJetTransport_power_sq_le

end CriticalLinePhasor.HelixSectionTransport
