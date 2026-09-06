import RequestProject.ThreeDAntihelixPairing
import RequestProject.PencilCellEdgeDoor

/-!
# The positive anti-helix pairing on the actual end-pair coordinates

Unfolded target: for a(ρ)=exp(Re(ρ)-1/2) and Eρ=1-conjugate(ρ),
Gρ=(I+R(a(ρ))*R(a(ρ))) tensor I_3 is positive, and the full radial
carrier D(a(ρ)) transports Gρ to G(Eρ).  The anti-linear exchange is
an involution and preserves the corresponding quadratic mass.
These statements hold at every complex input, hence also at each zeta zero.

The per-spatial-coordinate trace Pρ=Re tr(I+R*R) is strictly positive
and satisfies P(Eρ)=Pρ.  Its scalar similitude law is tested separately.

What would I do without a prior expectation? Substitute the actual end
coordinates in the matrix identities before applying the RH receiver.
Two decompositions: use inverse transport (`rw [endPairFace_endExchange]`),
or use the real radius (`rw [endPairFace_eq_ofReal]`).
Searches:
`rg -n 'endPairFace_eq_norm|endPairMetric|endPairWeight|endPair.*trace|
endPairFace_eq_ofReal|endPairFace_endExchange' RequestProject --glob '*.lean'`
`rg -n 'RiemannHypothesis|trace_nonneg|PosDef|conjTranspose'
.lake/packages/mathlib/Mathlib --glob '*.lean'`
-/

open Matrix Complex
open scoped BigOperators Kronecker ComplexOrder

namespace CriticalLinePhasor.Pencil3D

open CellEdgeDoor

noncomputable def endPairMetric (ρ : ℂ) := spatial (exchangeMetric (endPairFace ρ))

noncomputable def endPairWeight (ρ : ℂ) : ℝ :=
  (exchangeMetric (endPairFace ρ)).trace.re

theorem endPairMetric_posDef (ρ : ℂ) : (endPairMetric ρ).PosDef :=
  spatial_exchangeMetric_posDef _

theorem endPairWeight_pos (ρ : ℂ) : 0 < endPairWeight ρ := exchangeMetric_trace_pos _

theorem endPairWeight_endExchange (ρ : ℂ) :
    endPairWeight (endExchange ρ) = endPairWeight ρ := by
  simp only [endPairWeight, endPairFace_endExchange, exchangeMetric_trace_inverse]

theorem endPairMetric_transport (ρ : ℂ) :
    (spatial (laneDiagonal (endPairFace ρ) (endPairFace ρ)⁻¹))ᴴ * endPairMetric ρ *
      spatial (laneDiagonal (endPairFace ρ) (endPairFace ρ)⁻¹) =
        endPairMetric (endExchange ρ) := by
  simp only [endPairMetric, spatial, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    reciprocal_exchangeMetric_transport (endPairFace_ne_zero ρ), endPairFace_endExchange]

theorem endPairFace_eq_norm (ρ : ℂ) : endPairFace ρ = (‖endPairFace ρ‖ : ℂ) := by
  rw [norm_endPairFace, endPairFace_eq_ofReal]

theorem endPairConjugate_involutive (ρ : ℂ) :
    Function.Involutive (antihelixConjugate ‖endPairFace ρ‖) :=
  antihelixConjugate_involutive (norm_ne_zero_iff.mpr (endPairFace_ne_zero ρ))

theorem endPairConjugate_mass (ρ : ℂ) (v : (Fin 1 ⊕ Fin 1) × Fin 3 → ℂ) :
    star (antihelixConjugate ‖endPairFace ρ‖ v) ⬝ᵥ
      (endPairMetric ρ).mulVec (antihelixConjugate ‖endPairFace ρ‖ v) =
        star v ⬝ᵥ (endPairMetric ρ).mulVec v := by
  have hmetric : endPairMetric ρ = spatial (exchangeMetric (‖endPairFace ρ‖ : ℂ)) := by
    exact congrArg (fun z : ℂ => spatial (exchangeMetric z)) (endPairFace_eq_norm ρ)
  rw [hmetric]
  exact antihelixConjugate_mass (norm_ne_zero_iff.mpr (endPairFace_ne_zero ρ)) v

end CriticalLinePhasor.Pencil3D

#print axioms CriticalLinePhasor.Pencil3D.endPairMetric_posDef
#print axioms CriticalLinePhasor.Pencil3D.endPairWeight_pos
#print axioms CriticalLinePhasor.Pencil3D.endPairWeight_endExchange
#print axioms CriticalLinePhasor.Pencil3D.endPairMetric_transport
#print axioms CriticalLinePhasor.Pencil3D.endPairConjugate_involutive
#print axioms CriticalLinePhasor.Pencil3D.endPairConjugate_mass
