import RequestProject.GlobalHelixCPSDualPair
import RequestProject.CarrierThetaAutomaticReadout

/-!
# CPS dual pairs with radial Satake growth retained

The 3D source keeps arbitrary nonzero radial Satake magnitudes.  Primal and contragredient local
weights have independent polynomial prime bounds; these bounds imply polynomial all-place
coefficient growth, after which the geometric carrier constructs the reflected strong pair.
-/

open Real Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- A primal/contragredient Satake pair with polynomial radial growth at the primes. -/
structure PolynomialSatakeDualPair (ι : Type*) where
  primal : Nat.Primes → ι → ℂ
  dual : Nat.Primes → ι → ℂ
  primalExponent : ℕ
  dualExponent : ℕ
  primal_ne_zero : ∀ p i, primal p i ≠ 0
  dual_eq_inv : ∀ p i, dual p i = (primal p i)⁻¹
  primal_bound : ∀ p i, ‖primal p i‖ ≤ (p.1 : ℝ) ^ primalExponent
  dual_bound : ∀ p i, ‖dual p i‖ ≤ (p.1 : ℝ) ^ dualExponent

/-- The CPS tensor rank at twist degree `m`. -/
abbrev CPSTensorIndex (r m : ℕ) := Fin (r + 1) × Fin m

/-- The non-self-dual CPS input at symmetric-power rank `r` and twist degree `m`. -/
abbrev CPSPolynomialTwist (r m : ℕ) := PolynomialSatakeDualPair (CPSTensorIndex r m)

/-- A local coefficient with weight bound `Q` is bounded by multichoose times `Q^n`. -/
theorem norm_radialLocalEulerCoeff_le_multichoose_mul_pow
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (Q : ℝ) (_hQ : 0 ≤ Q)
    (hw : ∀ i, ‖w i‖ ≤ Q) (n : ℕ) :
    ‖radialLocalEulerCoeff w n‖ ≤
      ((Fintype.card ι).multichoose n : ℝ) * Q ^ n := by
  classical
  unfold radialLocalEulerCoeff
  calc
    ‖∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
        ∏ i, w i ^ l i‖
        ≤ ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
            ‖∏ i, w i ^ l i‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n, Q ^ n := by
      apply Finset.sum_le_sum
      intro l hl
      rw [norm_prod]
      calc
        ∏ i, ‖w i ^ l i‖ ≤ ∏ i, Q ^ l i := by
          apply Finset.prod_le_prod
          · intro i _
            exact norm_nonneg _
          · intro i _
            simpa [norm_pow] using
              pow_le_pow_left₀ (norm_nonneg (w i)) (hw i) (l i)
        _ = Q ^ (∑ i, l i) := by rw [← Finset.prod_pow_eq_pow_sum]
        _ = Q ^ n := by rw [(Finset.mem_finsuppAntidiag.mp hl).1]
    _ = ((Fintype.card ι).multichoose n : ℝ) * Q ^ n := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      norm_cast
      simp [Finset.card_finsuppAntidiag_nat_eq_multichoose]

/-- Prime-wise polynomial radial bounds give a polynomial all-place coefficient bound. -/
theorem radialGlobalSatakeCoeff_norm_le_of_prime_pow
    {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (B : ℕ)
    (hw : ∀ p i, ‖w p i‖ ≤ (p.1 : ℝ) ^ B) (n : ℕ) :
    ‖radialGlobalSatakeCoeff w n‖ ≤
      (((n + 1 : ℕ) : ℝ) ^ (Fintype.card ι + B : ℕ)) := by
  classical
  let m : ℕ := n + 1
  let d : ℕ := Fintype.card ι
  have hm : m ≠ 0 := by
    dsimp [m]
    omega
  have hlocal : ∀ p : ↑m.primeFactors,
      ‖radialLocalEulerCoeff
        (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
        (m.factorization p.1)‖ ≤
        (((m.factorization p.1 + 1) ^ d : ℕ) : ℝ) *
          (p.1 : ℝ) ^ (B * m.factorization p.1) := by
    intro p
    let pp : Nat.Primes := ⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩
    have hraw := norm_radialLocalEulerCoeff_le_multichoose_mul_pow
      (w pp) ((p.1 : ℝ) ^ B) (by positivity) (hw pp) (m.factorization p.1)
    calc
      ‖radialLocalEulerCoeff (w pp) (m.factorization p.1)‖
          ≤ (((Fintype.card ι).multichoose (m.factorization p.1) : ℕ) : ℝ) *
              ((p.1 : ℝ) ^ B) ^ (m.factorization p.1) := hraw
      _ ≤ (((m.factorization p.1 + 1) ^ d : ℕ) : ℝ) *
              ((p.1 : ℝ) ^ B) ^ (m.factorization p.1) := by
            gcongr
            exact_mod_cast multichoose_le_add_one_pow d (m.factorization p.1)
      _ = (((m.factorization p.1 + 1) ^ d : ℕ) : ℝ) *
              (p.1 : ℝ) ^ (B * m.factorization p.1) := by rw [pow_mul]
  change ‖∏ p : ↑m.primeFactors, _‖ ≤ (m : ℝ) ^ (d + B)
  rw [norm_prod]
  calc
    ∏ p : ↑m.primeFactors,
        ‖radialLocalEulerCoeff
          (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
          (m.factorization p.1)‖
        ≤ ∏ p : ↑m.primeFactors,
          ((((m.factorization p.1 + 1) ^ d : ℕ) : ℝ) *
            (p.1 : ℝ) ^ (B * m.factorization p.1)) := by
          exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => hlocal p)
    _ = (∏ p : ↑m.primeFactors,
          (((m.factorization p.1 + 1) ^ d : ℕ) : ℝ)) *
        (∏ p : ↑m.primeFactors,
          (p.1 : ℝ) ^ (B * m.factorization p.1)) := by rw [Finset.prod_mul_distrib]
    _ = (((m.divisors.card : ℕ) : ℝ) ^ d) * (m : ℝ) ^ B := by
      congr 1
      · simp_rw [Nat.cast_pow]
        rw [show (∏ p : ↑m.primeFactors,
              ((m.factorization p.1 + 1 : ℕ) : ℝ) ^ d) =
            (∏ p : ↑m.primeFactors,
              ((m.factorization p.1 + 1 : ℕ) : ℝ)) ^ d by
              simpa using Finset.prod_pow
                (Finset.univ : Finset ↑m.primeFactors) d
                (fun p => ((m.factorization p.1 + 1 : ℕ) : ℝ))]
        congr 1
        have hnat :
            (∏ p : ↑m.primeFactors, (m.factorization p.1 + 1)) =
              m.divisors.card := by
          rw [Finset.prod_coe_sort
            m.primeFactors (fun p : ℕ => m.factorization p + 1)]
          exact (Nat.card_divisors hm).symm
        exact_mod_cast hnat
      · have hpow : ∀ p : ↑m.primeFactors,
            (p.1 : ℝ) ^ (B * m.factorization p.1) =
              ((p.1 : ℝ) ^ m.factorization p.1) ^ B := by
          intro p
          rw [mul_comm]
          exact pow_mul _ _ _
        simp_rw [hpow]
        rw [show (∏ p : ↑m.primeFactors,
              ((p.1 : ℝ) ^ m.factorization p.1) ^ B) =
            (∏ p : ↑m.primeFactors,
              (p.1 : ℝ) ^ m.factorization p.1) ^ B by
              simpa using Finset.prod_pow
                (Finset.univ : Finset ↑m.primeFactors) B
                (fun p => (p.1 : ℝ) ^ m.factorization p.1)]
        have hmprod := Nat.prod_pow_primeFactors_factorization hm
        congr 1
        exact_mod_cast hmprod.symm
    _ ≤ (m : ℝ) ^ d * (m : ℝ) ^ B := by
      gcongr
      exact_mod_cast Nat.card_divisors_le_self m
    _ = (m : ℝ) ^ (d + B) := by rw [pow_add]

/-- Primal all-place coefficients with the radial ledger retained. -/
noncomputable def cpsPolynomialPrimalCoeff
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) : ℕ → ℂ :=
  radialGlobalSatakeCoeff W.primal

/-- Contragredient all-place coefficients. -/
noncomputable def cpsPolynomialDualCoeff
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) : ℕ → ℂ :=
  radialGlobalSatakeCoeff W.dual

theorem cpsPolynomialPrimalCoeff_norm_le
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (n : ℕ) :
    ‖cpsPolynomialPrimalCoeff W n‖ ≤
      (((n + 1 : ℕ) : ℝ) ^ (Fintype.card ι + W.primalExponent : ℕ)) :=
  radialGlobalSatakeCoeff_norm_le_of_prime_pow W.primal W.primalExponent W.primal_bound n

theorem cpsPolynomialDualCoeff_norm_le
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (n : ℕ) :
    ‖cpsPolynomialDualCoeff W n‖ ≤
      (((n + 1 : ℕ) : ℝ) ^ (Fintype.card ι + W.dualExponent : ℕ)) :=
  radialGlobalSatakeCoeff_norm_le_of_prime_pow W.dual W.dualExponent W.dual_bound n

@[reducible] noncomputable def cpsPolynomialPrimalOneInvertible
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) :
    Invertible ((CarrierTheta.coefficientArithmetic (cpsPolynomialPrimalCoeff W)) 1) := by
  rw [CarrierTheta.coefficientArithmetic]
  simp [cpsPolynomialPrimalCoeff, radialGlobalSatakeCoeff_zero]
  exact invertibleOne

@[reducible] noncomputable def cpsPolynomialDualOneInvertible
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) :
    Invertible ((CarrierTheta.coefficientArithmetic (cpsPolynomialDualCoeff W)) 1) := by
  rw [CarrierTheta.coefficientArithmetic]
  simp [cpsPolynomialDualCoeff, radialGlobalSatakeCoeff_zero]
  exact invertibleOne

theorem cpsPolynomialPrimalArithmetic_norm_le
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (n : ℕ) :
    ‖(CarrierTheta.coefficientArithmetic (cpsPolynomialPrimalCoeff W)) n‖ ≤
      (1 : ℝ) * (n : ℝ) ^ (Fintype.card ι + W.primalExponent : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simp [CarrierTheta.coefficientArithmetic]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hbound := cpsPolynomialPrimalCoeff_norm_le W (n - 1)
    rw [Nat.sub_add_cancel hn1] at hbound
    simpa [CarrierTheta.coefficientArithmetic, hn] using hbound

theorem cpsPolynomialDualArithmetic_norm_le
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (n : ℕ) :
    ‖(CarrierTheta.coefficientArithmetic (cpsPolynomialDualCoeff W)) n‖ ≤
      (1 : ℝ) * (n : ℝ) ^ (Fintype.card ι + W.dualExponent : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simp [CarrierTheta.coefficientArithmetic]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hbound := cpsPolynomialDualCoeff_norm_le W (n - 1)
    rw [Nat.sub_add_cancel hn1] at hbound
    simpa [CarrierTheta.coefficientArithmetic, hn] using hbound

noncomputable def cpsPolynomialPrimalKernel
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) : ℝ → ℂ :=
  CarrierTheta.dilationKernel
    (ArithmeticFunction.dirichletInverse
      (CarrierTheta.coefficientArithmetic (cpsPolynomialPrimalCoeff W))
      (cpsPolynomialPrimalOneInvertible W))
    (CriticalLinePhasor.StrandExchange.completedLogTheta
      twistedSymmetricPowerExchangeCarrier 1)

noncomputable def cpsPolynomialDualKernel
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) : ℝ → ℂ :=
  CarrierTheta.dilationKernel
    (ArithmeticFunction.dirichletInverse
      (CarrierTheta.coefficientArithmetic (cpsPolynomialDualCoeff W))
      (cpsPolynomialDualOneInvertible W))
    (CriticalLinePhasor.StrandExchange.completedLogThetaDual
      twistedSymmetricPowerExchangeCarrier 1)

/-- The radial primal Satake bank in 3D. -/
noncomputable def cpsPolynomialPrimal3DBankReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPolynomialPrimalCoeff W) n x) *
      cpsPolynomialPrimalKernel W
        (multiplicativeHeight (coefficientFiber (cpsPolynomialPrimalCoeff W) n x))

/-- The radial contragredient Satake bank in 3D. -/
noncomputable def cpsPolynomialDual3DBankReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPolynomialDualCoeff W) n x) *
      cpsPolynomialDualKernel W
        (multiplicativeHeight (coefficientFiber (cpsPolynomialDualCoeff W) n x))

theorem cpsPolynomialPrimal3DBankReadout_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialPrimal3DBankReadout W x =
      CarrierTheta.theta (cpsPolynomialPrimalCoeff W) (cpsPolynomialPrimalKernel W) x := by
  unfold cpsPolynomialPrimal3DBankReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPolynomialPrimalCoeff W) n hx]

theorem cpsPolynomialDual3DBankReadout_eq_theta
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialDual3DBankReadout W x =
      CarrierTheta.theta (cpsPolynomialDualCoeff W) (cpsPolynomialDualKernel W) x := by
  unfold cpsPolynomialDual3DBankReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPolynomialDualCoeff W) n hx]

/-- The strong pair of the full radial primal/contragredient 3D source. -/
noncomputable def cpsPolynomialStrongFEPair
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) : StrongFEPair ℂ :=
  CarrierTheta.automaticCoefficientThetaStrongFEPair
    twistedSymmetricPowerExchangeCarrier
    twistedSymmetricPowerExchangeCarrier_continuous
    1 one_ne_zero twistedSymmetricPowerExchangeCarrier_exchange
    1 zero_lt_one 0 twistedSymmetricPowerExchangeCarrier_logTheta_isBigO
    (cpsPolynomialPrimalCoeff W) (cpsPolynomialDualCoeff W)
    (cpsPolynomialPrimalOneInvertible W) (cpsPolynomialDualOneInvertible W)
    (Fintype.card ι + W.primalExponent) (Fintype.card ι + W.dualExponent)
    1 1 zero_le_one zero_le_one
    (cpsPolynomialPrimalArithmetic_norm_le W)
    (cpsPolynomialDualArithmetic_norm_le W)

/-- Exact audit of the synthesized pair: its primal completed transform is the Mellin transform
of the common completed carrier.

**Seam (this is the engineered demonstration route, NOT the load-bearing one).**  The pair above uses
the Dirichlet-inverse dilation kernel, whose theta convolution *cancels the coefficients*: this
theorem shows `Λ` equals the Mellin of the fixed self-dual profile `completedLogTheta`
(**coefficient-independent**).  So this pair is a proof that *a* self-dual completion with a chosen
reflection can be built; it is **not** the standard completed `L(s, Sym^r π × τ)` and must not be
read as one.  The standard-normalized niceness rides two other, non-engineered facts: the finite
functional equation from the **local reciprocal identity** `FiniteWeightFiber.localPoly_reciprocal`
(a rational palindrome, not a supplied field, not coefficient-canceling — see
`symTensorCompleted_FE`), and the **standard Γℂ completion** identified natively by
`cpsPolynomialPrimal_fixedGamma_initialIdentification` (`mellin (…completionKernel [μ]) =
dirichlet · Γℂ(s+μ)`).  Do not cite this synthesized-kernel pair as the arithmetic object. -/
theorem cpsPolynomialStrongFEPair_Lambda_eq_carrierMellin
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (s : ℂ) :
    (cpsPolynomialStrongFEPair W).Λ s =
      mellin (CriticalLinePhasor.StrandExchange.completedLogTheta
        twistedSymmetricPowerExchangeCarrier 1) s := by
  change mellin
      (CarrierTheta.theta (cpsPolynomialPrimalCoeff W)
        (cpsPolynomialPrimalKernel W)) s = _
  exact CarrierTheta.mellin_theta_dirichletInverse_completedLogTheta_of_polynomial
    (cpsPolynomialPrimalCoeff W) (cpsPolynomialPrimalOneInvertible W)
    twistedSymmetricPowerExchangeCarrier 1 0
    twistedSymmetricPowerExchangeCarrier_logTheta_isBigO
    (Fintype.card ι + W.primalExponent) 1 zero_le_one
    (cpsPolynomialPrimalArithmetic_norm_le W) s

/-- The dual completed transform is the common anti-carrier Mellin transform. -/
theorem cpsPolynomialStrongFEPair_dualLambda_eq_carrierMellin
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) (s : ℂ) :
    (cpsPolynomialStrongFEPair W).symm.Λ s =
      mellin (CriticalLinePhasor.StrandExchange.completedLogThetaDual
        twistedSymmetricPowerExchangeCarrier 1) s := by
  change mellin
      (CarrierTheta.theta (cpsPolynomialDualCoeff W)
        (cpsPolynomialDualKernel W)) s = _
  exact CarrierTheta.mellin_theta_dirichletInverse_completedLogThetaDual_of_polynomial
    (cpsPolynomialDualCoeff W) (cpsPolynomialDualOneInvertible W)
    twistedSymmetricPowerExchangeCarrier 1 0
    twistedSymmetricPowerExchangeCarrier_logTheta_isBigO
    (Fintype.card ι + W.dualExponent) 1 zero_le_one
    (cpsPolynomialDualArithmetic_norm_le W) s

theorem cpsPolynomialStrongFEPair_f_eq_3DBankReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) {x : ℝ} (hx : 0 < x) :
    (cpsPolynomialStrongFEPair W).f x = cpsPolynomialPrimal3DBankReadout W x := by
  rw [cpsPolynomialPrimal3DBankReadout_eq_theta W hx]
  rfl

theorem cpsPolynomialStrongFEPair_g_eq_3DBankReadout
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) {x : ℝ} (hx : 0 < x) :
    (cpsPolynomialStrongFEPair W).g x = cpsPolynomialDual3DBankReadout W x := by
  rw [cpsPolynomialDual3DBankReadout_eq_theta W hx]
  rfl

/-- Exact global reflection of the radial primal and contragredient 3D banks. -/
theorem cpsPolynomial3D_globalHelixReflection
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) {x : ℝ} (hx : 0 < x) :
    cpsPolynomialPrimal3DBankReadout W (1 / x) =
      (x : ℂ) * cpsPolynomialDual3DBankReadout W x := by
  let P := cpsPolynomialStrongFEPair W
  have hfe := P.h_feq x hx
  have hkP : P.k = 1 := rfl
  have hεP : P.ε = 1 := by
    simp [P, cpsPolynomialStrongFEPair,
      CarrierTheta.automaticCoefficientThetaStrongFEPair,
      CarrierTheta.coefficientThetaStrongFEPair]
  rw [hkP, hεP] at hfe
  rw [← cpsPolynomialStrongFEPair_f_eq_3DBankReadout W (one_div_pos.mpr hx),
      ← cpsPolynomialStrongFEPair_g_eq_3DBankReadout W hx]
  simpa using hfe

/-- Full CPS analytic niceness for a radial primal/contragredient twist. -/
theorem cpsPolynomial_twistedNiceness
    {ι : Type*} [Fintype ι] (W : PolynomialSatakeDualPair ι) :
    let P := cpsPolynomialStrongFEPair W
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := cpsPolynomialStrongFEPair W
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip P u v,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip P.symm u v,
    P.functional_equation⟩

/-- Every twist degree in the CPS range has radial 3D reflection and analytic niceness. -/
theorem cpsPolynomialAllTwists_payload
    (r : ℕ) : ∀ m : ℕ, 1 ≤ m → m < r → ∀ W : CPSPolynomialTwist r m,
      (∀ x : ℝ, 0 < x →
        cpsPolynomialPrimal3DBankReadout W (1 / x) =
          (x : ℂ) * cpsPolynomialDual3DBankReadout W x) ∧
      (let P := cpsPolynomialStrongFEPair W;
        Differentiable ℂ P.Λ ∧
        Differentiable ℂ P.symm.Λ ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
        (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
          u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
        (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s)) := by
  intro m _ _ W
  exact ⟨fun x hx => cpsPolynomial3D_globalHelixReflection W hx,
    cpsPolynomial_twistedNiceness W⟩

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.norm_radialLocalEulerCoeff_le_multichoose_mul_pow
#print axioms CriticalLinePhasor.GlobalHelix.radialGlobalSatakeCoeff_norm_le_of_prime_pow
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialStrongFEPair_Lambda_eq_carrierMellin
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialStrongFEPair_dualLambda_eq_carrierMellin
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomial3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomial_twistedNiceness
#print axioms CriticalLinePhasor.GlobalHelix.cpsPolynomialAllTwists_payload
