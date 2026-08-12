import RequestProject.CPSConventionalCompletedRankinSelberg3D

/-!
# Uncompleted continuation of a conventional arithmetic CPS source

The completed source already supplies an entire function.  This file removes its literal
conductor and Deligne Gamma factors by multiplying by their entire reciprocals.  On every
`CPSCompletionPoint` this uncompleted continuation is proved equal to the original Euler readout.
-/

open Complex

namespace CriticalLinePhasor.GlobalHelix
namespace ConventionalCompletedRankinSelbergSource3D

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- The reciprocal of Deligne's complex Gamma factor is entire. -/
theorem differentiable_Gammaℂ_inv :
    Differentiable ℂ (fun s : ℂ ↦ (Complex.Gammaℂ s)⁻¹) := by
  have hfun : (fun s : ℂ ↦ (Complex.Gammaℂ s)⁻¹) =
      fun s : ℂ ↦ (Complex.Gammaℝ s)⁻¹ * (Complex.Gammaℝ (s + 1))⁻¹ := by
    funext s
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    simpa [mul_comm] using
      (mul_inv_rev (Complex.Gammaℝ s) (Complex.Gammaℝ (s + 1)))
  rw [hfun]
  exact Complex.differentiable_Gammaℝ_inv.mul
    (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1))

/-- The entire reciprocal of the literal conductor/Gamma completion factor. -/
noncomputable def inverseCompletionFactor
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (s : ℂ) : ℂ :=
  (L.conductor : ℂ) ^ (-s) *
    (L.gammaShifts.map fun μ ↦ (Complex.Gammaℂ (s + μ))⁻¹).prod

/-- The uncompleted analytic continuation attached to the same completed source. -/
noncomputable def uncompletedContinuation
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (s : ℂ) : ℂ :=
  L.inverseCompletionFactor s * L.completed s

/-- The reciprocal completion factor is entire. -/
theorem inverseCompletionFactor_entire
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    Differentiable ℂ L.inverseCompletionFactor := by
  unfold inverseCompletionFactor conductor gammaShifts
  apply Differentiable.mul
  · exact (differentiable_id.neg).const_cpow
      (Or.inl (ofReal_ne_zero.mpr D.conductor_pos.ne'))
  · induction D.tensorShifts with
    | nil => simp
    | cons μ μs ih =>
        simp only [List.map_cons, List.prod_cons]
        exact ((differentiable_Gammaℂ_inv.comp
          (differentiable_id.add_const μ))).mul ih

/-- The uncompleted continuation is entire. -/
theorem uncompletedContinuation_entire
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    Differentiable ℂ L.uncompletedContinuation :=
  L.inverseCompletionFactor_entire.mul L.completed_entire

/-- At a point where every shifted Gamma argument has positive real part, the literal completion
factor and its reciprocal multiply to one. -/
theorem completionFactor_mul_inverseCompletionFactor
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) (s : ℂ)
    (hμ : ∀ μ ∈ L.gammaShifts, 0 < (s + μ).re) :
    ((L.conductor : ℂ) ^ s *
        (L.gammaShifts.map fun μ ↦ Complex.Gammaℂ (s + μ)).prod) *
      L.inverseCompletionFactor s = 1 := by
  have hC : (L.conductor : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr D.conductor_pos.ne'))
  have hΓ : (L.gammaShifts.map fun μ ↦ Complex.Gammaℂ (s + μ)).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    rw [List.mem_map] at hz
    obtain ⟨μ, hμmem, hzero⟩ := hz
    have hne : Complex.Gammaℂ (s + μ) ≠ 0 := by
      rw [Complex.Gammaℂ_def]
      exact mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero
          (ofReal_ne_zero.mpr Real.pi_ne_zero)))))
        (Complex.Gamma_ne_zero_of_re_pos (hμ μ hμmem))
    exact hne hzero
  unfold inverseCompletionFactor
  rw [Complex.cpow_neg]
  have hinvprod :
      (L.gammaShifts.map fun μ ↦ (Complex.Gammaℂ (s + μ))⁻¹).prod =
        ((L.gammaShifts.map fun μ ↦ Complex.Gammaℂ (s + μ)).prod)⁻¹ := by
    induction L.gammaShifts with
    | nil => simp
    | cons μ μs ih => simp [ih, mul_comm]
  rw [hinvprod]
  field_simp

/-- On the common initial half-plane, the uncompleted continuation is exactly the original Euler
readout of the arithmetic Satake bank. -/
theorem uncompletedContinuation_initialIdentification
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (hm : 0 < m)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist r m pi tau) (D.clock hm)) :
    L.uncompletedContinuation point.s = L.uncompletedEuler point.s := by
  rw [uncompletedContinuation, L.completed_initialIdentification hm point]
  unfold cpsPolynomialFullPrimalCompletedReadout
  have hfactor := L.completionFactor_mul_inverseCompletionFactor point.s point.shifts_pos
  unfold uncompletedEuler
  calc
    L.inverseCompletionFactor point.s *
        ((L.conductor : ℂ) ^ point.s *
          (L.gammaShifts.map fun μ ↦ Complex.Gammaℂ (point.s + μ)).prod *
          CarrierTheta.dirichlet
            (cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau)) point.s) =
        (((L.conductor : ℂ) ^ point.s *
          (L.gammaShifts.map fun μ ↦ Complex.Gammaℂ (point.s + μ)).prod) *
          L.inverseCompletionFactor point.s) *
          CarrierTheta.dirichlet
            (cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau)) point.s := by
      ring
    _ = CarrierTheta.dirichlet
          (cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist r m pi tau)) point.s := by
      rw [hfactor, one_mul]

end ConventionalCompletedRankinSelbergSource3D
end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.differentiable_Gammaℂ_inv
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.inverseCompletionFactor_entire
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_entire
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.completionFactor_mul_inverseCompletionFactor
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.uncompletedContinuation_initialIdentification
