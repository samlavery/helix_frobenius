import RequestProject.CPSTemperedBankAbscissa3D
import RequestProject.CPSGeneralizedVonMangoldtSupport3D
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The tempered logarithmic-derivative identity on the readout half-plane

`ConventionalCompletedRankinSelbergSource3D.LSeries_logarithmicCoefficient_eq_neg_logDeriv`
already identifies the generalized von Mangoldt series with `-L'/L`, but only to the right of
`logDerivativeConvergenceThreshold`, which is `max (card + primalExponent + 1)
(inverse-growth exponent + 1)` — far out in the chart.  The Wiener--Ikehara consumer reads the
boundary of the *projected* series, so the identity has to hold wherever that projection
converges absolutely, i.e. on `Re s > 1` under temperedness.  (The abscissa is a chart datum:
the carrier object itself has no convergence gate.)

The route here removes the Dirichlet inverse from the analysis entirely.  The inverse enters the
identity only algebraically, through

  `logCoeff ⋆ A = (logMul A ⋆ A⁻¹) ⋆ A = logMul A`,

which is an identity of arithmetic functions with no convergence content.  So only two series
need to converge on `Re s > 1`: the bank `A` (from `CPSTemperedBankAbscissa3D`) and the
logarithmic coefficient itself, which is dominated pointwise by `card ι` times the ordinary von
Mangoldt function — the exact power-sum formula plus unit roots, again a computation rather than
an estimate.  Nothing is asked of the growth of `A⁻¹`.

Output: `LSeries logCoeff · LSeries A = -(LSeries A)'` on `Re s > 1`, which is the
`ContinuousLSeriesBoundary3D.eqOn` field as soon as the entire continuation is identified with
`LSeries A` there.
-/

open ArithmeticFunction Complex

set_option maxHeartbeats 1000000

namespace CriticalLinePhasor.GlobalHelix
namespace ConventionalCompletedRankinSelbergSource3D

variable {r m : ℕ} {pi : PolynomialSatakeDualPair (Fin 2)}
  {tau : PolynomialSatakeDualPair (Fin m)}
  {D : ArithmeticCPSCompletionData r m}

/-- The tensor root of the arithmetic CPS twist is the primal weight of the twist. -/
theorem arithmeticCPSTensorRoot_eq_primal (p : Nat.Primes) (i : CPSTensorIndex r m) :
    arithmeticCPSTensorRoot r m pi tau p i =
      (arithmeticCPSPolynomialTwist r m pi tau).primal p i := rfl

/-! ## The bank series on the readout half-plane -/

/-- Under temperedness the Rankin--Selberg bank converges absolutely on `Re s > 1`. -/
theorem arithmeticCoefficient_LSeriesSummable_of_tempered
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑L.arithmeticCoefficient) s :=
  bankArithmetic_LSeriesSummable_of_tempered
    (arithmeticCPSPolynomialTwist r m pi tau).primal htemp hs

/-- Under temperedness the bank abscissa of absolute convergence is at most one. -/
theorem arithmeticCoefficient_abscissaOfAbsConv_le_one
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1) :
    LSeries.abscissaOfAbsConv (⇑L.arithmeticCoefficient) ≤ 1 :=
  bankArithmetic_abscissaOfAbsConv_le_one
    (arithmeticCPSPolynomialTwist r m pi tau).primal htemp

/-! ## The von Mangoldt majorant for the logarithmic coefficient -/

/-- **The tempered logarithmic coefficient is dominated by the von Mangoldt function.**  Off
prime powers both sides vanish; at `p ^ j` the coefficient is exactly `log p` times a sum of
`card ι` unit-modulus powers. -/
theorem norm_logarithmicCoefficient_le_vonMangoldt
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1)
    (n : ℕ) :
    ‖L.logarithmicCoefficient n‖ ≤
      (Fintype.card (CPSTensorIndex r m) : ℝ) * ArithmeticFunction.vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · rcases hn with ⟨p, j, hp, hj, rfl⟩
    have hpn := hp.nat_prime
    rw [logarithmicCoefficient_prime_pow_eq_satakePowerSum L hpn hj,
      ArithmeticFunction.vonMangoldt_apply_pow hj.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hpn, norm_mul,
      ← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (mod_cast hpn.one_le)), mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (mod_cast hpn.one_le))
    calc
      ‖∑ i : CPSTensorIndex r m,
          arithmeticCPSTensorRoot r m pi tau ⟨p, hpn⟩ i ^ j‖ ≤
          ∑ i : CPSTensorIndex r m,
            ‖arithmeticCPSTensorRoot r m pi tau ⟨p, hpn⟩ i ^ j‖ := norm_sum_le _ _
      _ = (Fintype.card (CPSTensorIndex r m) : ℝ) := by
        rw [Finset.sum_congr rfl (fun i _ => ?_), Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
        rw [norm_pow,
          show ‖arithmeticCPSTensorRoot r m pi tau ⟨p, hpn⟩ i‖ = 1 from htemp ⟨p, hpn⟩ i,
          one_pow]
  · rw [L.logarithmicCoefficient_eq_zero_of_not_isPrimePow hn,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    simp

/-- The tempered logarithmic coefficient series converges absolutely on `Re s > 1`. -/
theorem logarithmicCoefficient_LSeriesSummable_of_tempered
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑L.logarithmicCoefficient) s := by
  have hΛ : LSeriesSummable (fun n : ℕ ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  refine Summable.of_norm
    ((hΛ.norm.mul_left ((Fintype.card (CPSTensorIndex r m) : ℝ))).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_)
  rcases eq_or_ne n 0 with rfl | h0
  · simp [LSeries.term]
  · have hden : (0 : ℝ) < ‖(n : ℂ) ^ s‖ := by
      rw [norm_pos_iff]
      exact cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr h0))
    have hΛnorm : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ =
        ArithmeticFunction.vonMangoldt n := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [LSeries.term_of_ne_zero h0, LSeries.term_of_ne_zero h0, norm_div, norm_div,
      hΛnorm, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (norm_logarithmicCoefficient_le_vonMangoldt L htemp n) hden.le

/-! ## The identity -/

/-- The generalized von Mangoldt coefficient convolved with the bank is the logarithmically
weighted bank.  This is pure Dirichlet algebra: the inverse cancels and no convergence is used. -/
theorem logarithmicCoefficient_mul_arithmeticCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D) :
    L.logarithmicCoefficient * L.arithmeticCoefficient =
      L.weightedArithmeticCoefficient := by
  calc
    L.logarithmicCoefficient * L.arithmeticCoefficient =
        L.weightedArithmeticCoefficient *
          (L.inverseArithmeticCoefficient * L.arithmeticCoefficient) := by
      rw [logarithmicCoefficient]; ring
    _ = L.weightedArithmeticCoefficient * 1 := by
      rw [inverseArithmeticCoefficient, ArithmeticFunction.dirichletInverse_mul_self]
    _ = L.weightedArithmeticCoefficient := mul_one _

/-- **The logarithmic-derivative identity on the readout half-plane.**  For a tempered twist the
generalized von Mangoldt series times the bank series is minus the derivative of the bank series,
everywhere on `Re s > 1` — the whole strip the Wiener--Ikehara consumer needs, not just the far
half-plane of the polynomial-growth threshold. -/
theorem LSeries_logarithmicCoefficient_mul_arithmeticCoefficient
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (⇑L.logarithmicCoefficient) s * LSeries (⇑L.arithmeticCoefficient) s =
      -deriv (LSeries (⇑L.arithmeticCoefficient)) s := by
  have hlog := logarithmicCoefficient_LSeriesSummable_of_tempered L htemp hs
  have hA := arithmeticCoefficient_LSeriesSummable_of_tempered L htemp hs
  have habs : LSeries.abscissaOfAbsConv (⇑L.arithmeticCoefficient) < (s.re : EReal) :=
    lt_of_le_of_lt (arithmeticCoefficient_abscissaOfAbsConv_le_one L htemp)
      (by exact_mod_cast hs)
  rw [← ArithmeticFunction.LSeries_mul' hlog hA,
    logarithmicCoefficient_mul_arithmeticCoefficient L, LSeries_deriv habs, neg_neg]
  exact LSeries_congr (fun _ => L.weightedArithmeticCoefficient_eq_logMul _) s

/-- The same identity as a quotient, once the bank series is known to be nonzero. -/
theorem LSeries_logarithmicCoefficient_eq_neg_logDeriv_of_tempered
    (L : ConventionalCompletedRankinSelbergSource3D r m pi tau D)
    (htemp : ∀ (p : Nat.Primes) (i : CPSTensorIndex r m),
      ‖(arithmeticCPSPolynomialTwist r m pi tau).primal p i‖ = 1)
    {s : ℂ} (hs : 1 < s.re)
    (hne : LSeries (⇑L.arithmeticCoefficient) s ≠ 0) :
    LSeries (⇑L.logarithmicCoefficient) s =
      -logDeriv (LSeries (⇑L.arithmeticCoefficient)) s := by
  rw [logDeriv_apply, ← neg_div,
    ← LSeries_logarithmicCoefficient_mul_arithmeticCoefficient L htemp hs,
    mul_div_assoc, div_self hne, mul_one]

end ConventionalCompletedRankinSelbergSource3D
end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.arithmeticCoefficient_LSeriesSummable_of_tempered
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.norm_logarithmicCoefficient_le_vonMangoldt
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.logarithmicCoefficient_LSeriesSummable_of_tempered
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.logarithmicCoefficient_mul_arithmeticCoefficient
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.LSeries_logarithmicCoefficient_mul_arithmeticCoefficient
#print axioms CriticalLinePhasor.GlobalHelix.ConventionalCompletedRankinSelbergSource3D.LSeries_logarithmicCoefficient_eq_neg_logDeriv_of_tempered
