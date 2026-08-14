import RequestProject.CPSTemperedLogDerivative3D
import RequestProject.CPSMaassCoefficientSurfaceReality3D

/-!
# Reality of the generalized von Mangoldt coefficients

The Tauberian transfer reads `(logarithmicCoefficient n).re`, and the Wiener--Ikehara bridge needs
that real sequence's Dirichlet series to be the continuation itself — so the coefficients have to
be real, not merely have a real part that is used.

Reality is inherited from the bank, and the inheritance is algebraic.  Conjugation is a ring
endomorphism for Dirichlet convolution, the logarithmic weight `Complex.log n` is real, and the
bank of a self-dual tower is real (`maassStandardCoefficientSurface_real`).  Since

  `logCoeff ⋆ A = logMul A`

with both `A` and `logMul A` fixed by conjugation, `conj logCoeff` and `logCoeff` have the same
convolution with `A`; multiplying by the Dirichlet inverse cancels `A` and they agree.  No
convergence and no growth data enter — the Dirichlet inverse is used purely as a formal
cancellation.
-/

open Complex

namespace ArithmeticFunction

/-- Coefficientwise complex conjugation of an arithmetic function. -/
noncomputable def starArithmetic (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := (starRingEnd ℂ) (f n)
  map_zero' := by simp

@[simp] theorem starArithmetic_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    starArithmetic f n = (starRingEnd ℂ) (f n) := rfl

/-- Conjugation is multiplicative for Dirichlet convolution. -/
theorem starArithmetic_mul (f g : ArithmeticFunction ℂ) :
    starArithmetic (f * g) = starArithmetic f * starArithmetic g := by
  ext n
  rw [starArithmetic_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun x _ => by
    rw [map_mul, starArithmetic_apply, starArithmetic_apply]

end ArithmeticFunction

namespace CriticalLinePhasor.GlobalHelix
namespace ConventionalCompletedRankinSelbergSource3D

open ArithmeticFunction

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- The logarithmic weight is real, so a real bank has a real logarithmically weighted bank. -/
theorem starArithmetic_weightedArithmeticCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (hA : starArithmetic L.arithmeticCoefficient = L.arithmeticCoefficient) :
    starArithmetic L.weightedArithmeticCoefficient = L.weightedArithmeticCoefficient := by
  ext n
  have hAn : (starRingEnd ℂ) (L.arithmeticCoefficient n) = L.arithmeticCoefficient n := by
    simpa using congrArg (fun f : ArithmeticFunction ℂ => f n) hA
  show (starRingEnd ℂ) (Complex.log (n : ℂ) * L.arithmeticCoefficient n) =
    Complex.log (n : ℂ) * L.arithmeticCoefficient n
  rw [map_mul, hAn, ← Complex.natCast_log, Complex.conj_ofReal]

/-- **Reality of the generalized von Mangoldt coefficients.**  A real bank has real logarithmic
coefficients; the Dirichlet inverse enters only to cancel. -/
theorem starArithmetic_logarithmicCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (hA : starArithmetic L.arithmeticCoefficient = L.arithmeticCoefficient) :
    starArithmetic L.logarithmicCoefficient = L.logarithmicCoefficient := by
  have key : starArithmetic L.logarithmicCoefficient * L.arithmeticCoefficient =
      L.logarithmicCoefficient * L.arithmeticCoefficient := by
    calc
      starArithmetic L.logarithmicCoefficient * L.arithmeticCoefficient =
          starArithmetic L.logarithmicCoefficient *
            starArithmetic L.arithmeticCoefficient := by rw [hA]
      _ = starArithmetic (L.logarithmicCoefficient * L.arithmeticCoefficient) :=
          (starArithmetic_mul _ _).symm
      _ = starArithmetic L.weightedArithmeticCoefficient := by
          rw [logarithmicCoefficient_mul_arithmeticCoefficient]
      _ = L.weightedArithmeticCoefficient :=
          starArithmetic_weightedArithmeticCoefficient L hA
      _ = L.logarithmicCoefficient * L.arithmeticCoefficient :=
          (logarithmicCoefficient_mul_arithmeticCoefficient L).symm
  have hcancel := congrArg (fun f : ArithmeticFunction ℂ =>
    f * L.inverseArithmeticCoefficient) key
  simp only [mul_assoc, inverseArithmeticCoefficient,
    ArithmeticFunction.self_mul_dirichletInverse, mul_one] at hcancel
  exact hcancel

/-- The real part of a real logarithmic coefficient is the coefficient. -/
theorem ofReal_re_logarithmicCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (hA : starArithmetic L.arithmeticCoefficient = L.arithmeticCoefficient) (n : ℕ) :
    ((L.logarithmicCoefficient n).re : ℂ) = L.logarithmicCoefficient n := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (starArithmetic_logarithmicCoefficient L hA)
  simp only [starArithmetic_apply] at h
  exact Complex.conj_eq_iff_re.mp h

end ConventionalCompletedRankinSelbergSource3D
end CriticalLinePhasor.GlobalHelix

/-! ## The Maass standard rung is real -/

namespace CriticalLinePhasor.ThreeDConverse

open CriticalLinePhasor.GeneralSeed CriticalLinePhasor.GlobalHelix
open CriticalLinePhasor.MaassSatoTate ArithmeticFunction

/-- The retained standard Maass source has a real bank at every rank: its coefficients are the
symmetric-power coefficient surface, which is fixed by conjugation once the tower ceiling has
closed the two extreme Satake strands. -/
theorem standard_starArithmetic_arithmeticCoefficient
    {M : GenuineMaassCuspForm3D} (hC : MaassTowerCeiling M.eigenData) {r : ℕ}
    {D : ArithmeticCPSCompletionData r 1}
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D) :
    starArithmetic L.arithmeticCoefficient = L.arithmeticCoefficient := by
  ext n
  rw [starArithmetic_apply]
  show (starRingEnd ℂ)
      (CarrierTheta.coefficientArithmetic
        (cpsPolynomialPrimalCoeff
          (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
            trivialPolynomialSatakePair3D)) n) =
    CarrierTheta.coefficientArithmetic
      (cpsPolynomialPrimalCoeff
        (arithmeticCPSPolynomialTwist r 1 (maassCPSBase M)
          trivialPolynomialSatakePair3D)) n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [CarrierTheta.coefficientArithmetic]
  · have hval : ∀ b : ℕ → ℂ, CarrierTheta.coefficientArithmetic b n = b (n - 1) := by
      intro b
      show (if n = 0 then 0 else b (n - 1)) = b (n - 1)
      rw [if_neg hn]
    rw [hval, standardTwist_primalCoeff_eq_maassStandardCoefficientSurface M r (n - 1)]
    exact maassStandardCoefficientSurface_real M hC r (n - 1)

/-- Every generalized von Mangoldt coefficient of the retained standard Maass source is real. -/
theorem standard_ofReal_re_logarithmicCoefficient
    {M : GenuineMaassCuspForm3D} (hC : MaassTowerCeiling M.eigenData) {r : ℕ}
    {D : ArithmeticCPSCompletionData r 1}
    (L : ConventionalCompletedRankinSelbergSource3D r 1 (maassCPSBase M)
      trivialPolynomialSatakePair3D D) (n : ℕ) :
    ((L.logarithmicCoefficient n).re : ℂ) = L.logarithmicCoefficient n :=
  ConventionalCompletedRankinSelbergSource3D.ofReal_re_logarithmicCoefficient L
    (standard_starArithmetic_arithmeticCoefficient hC L) n

end CriticalLinePhasor.ThreeDConverse

#print axioms ArithmeticFunction.starArithmetic_mul
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.starArithmetic_logarithmicCoefficient
#print axioms CriticalLinePhasor.ThreeDConverse.standard_starArithmetic_arithmeticCoefficient
#print axioms CriticalLinePhasor.ThreeDConverse.standard_ofReal_re_logarithmicCoefficient
