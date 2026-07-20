import RequestProject.GlobalHelixTwistedSymmetricPowerFEPair
import RequestProject.ThreeDConverse

/-!
# The general CPS twisted dual pair, constructed in three dimensions

This file removes the self-duality restriction from the twist input.  A primal Satake family is
paired with its pointwise contragredient family, the two all-place coefficient banks are assembled,
and only then are their scalar theta projections and strong functional-equation pair constructed.
-/

open Real Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.GlobalHelix

/-- A unitary prime phase, packaged as data rather than a separate proposition argument. -/
structure UnitaryPrimePhase where
  phase : Nat.Primes → ℂ
  unit : ∀ p, ‖phase p‖ = 1

/-- A possibly non-self-dual unitary Satake family of rank `κ`. -/
structure UnitarySatakeFamily (κ : Type*) where
  weight : Nat.Primes → κ → ℂ
  unit : ∀ p i, ‖weight p i‖ = 1

/-- The local `Sym^r π ⊗ τ` weights without imposing self-duality on `τ`. -/
noncomputable def cpsTensorWeight
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (p : Nat.Primes) : Fin (r + 1) × κ → ℂ :=
  fun i => α.phase p ^ ((r : ℤ) - 2 * (i.1.val : ℤ)) * τ.weight p i.2

theorem cpsTensorWeight_unit
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (p : Nat.Primes) (i : Fin (r + 1) × κ) :
    ‖cpsTensorWeight r α τ p i‖ = 1 := by
  rw [cpsTensorWeight, norm_mul, norm_zpow, α.unit, one_zpow, τ.unit, one_mul]

/-- The local contragredient weights. -/
noncomputable def cpsTensorDualWeight
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (p : Nat.Primes) : Fin (r + 1) × κ → ℂ :=
  fun i => (cpsTensorWeight r α τ p i)⁻¹

theorem cpsTensorDualWeight_unit
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (p : Nat.Primes) (i : Fin (r + 1) × κ) :
    ‖cpsTensorDualWeight r α τ p i‖ = 1 := by
  rw [cpsTensorDualWeight, norm_inv, cpsTensorWeight_unit, inv_one]

/-- The complete-homogeneous symmetric coefficient `h_n(w)` of a finite weight family `w`.

**Radius-live — no unit-modulus assumption.**  This is `∑ ∏ w_i^{l_i}` over the `n`-antidiagonal,
a polynomial in the weights that is well defined for *arbitrary* nonzero radial magnitudes; the
`radial…` name is deliberate.  (An earlier `unitary…` name was a misnomer: only some of the *bound*
lemmas below take `‖w‖ = 1`; the coefficient itself, and the polynomial-bound lemmas in
`GlobalHelixCPSPolynomialDualPair`, are radial.  Temperedness `‖α_p‖ = 1` is never an input to the
niceness that consumes this — it is the radial-limit *output*, `RamanujanLimit`.) -/
noncomputable def radialLocalEulerCoeff
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (n : ℕ) : ℂ :=
  by
    classical
    exact ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
      ∏ i, w i ^ l i

/-- A local unitary Euler coefficient is bounded by the standard multichoose majorant. -/
theorem norm_radialLocalEulerCoeff_le_add_one_pow
    {ι : Type*} [Fintype ι] (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1) (n : ℕ) :
    ‖radialLocalEulerCoeff w n‖ ≤ ((n + 1) ^ Fintype.card ι : ℕ) := by
  classical
  unfold radialLocalEulerCoeff
  calc
    ‖∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
        ∏ i, w i ^ l i‖
        ≤ ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n,
            ‖∏ i, w i ^ l i‖ := norm_sum_le _ _
    _ = ∑ _l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) n, 1 := by
      apply Finset.sum_congr rfl
      intro l _
      simp [norm_prod, hw]
    _ = #(Finset.finsuppAntidiag (Finset.univ : Finset ι) n) := by simp
    _ = (Fintype.card ι).multichoose n := by
      simp [Finset.card_finsuppAntidiag_nat_eq_multichoose]
    _ ≤ (((n + 1) ^ Fintype.card ι : ℕ) : ℝ) := by
      exact_mod_cast multichoose_le_add_one_pow (Fintype.card ι) n

/-- The all-place coefficient bank attached to a local weight family — **radius-live**, arbitrary
nonzero radial magnitudes (see `radialLocalEulerCoeff`); the `radial…` name is deliberate, not a
unit-modulus bank. -/
noncomputable def radialGlobalSatakeCoeff
    {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (n : ℕ) : ℂ :=
  ∏ p : ↑(n + 1).primeFactors,
    radialLocalEulerCoeff
      (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
      ((n + 1).factorization p.1)

/-- The all-place unitary bank has a polynomial bound determined only by its rank. -/
theorem radialGlobalSatakeCoeff_norm_le
    {ι : Type*} [Fintype ι]
    (w : Nat.Primes → ι → ℂ) (hw : ∀ p i, ‖w p i‖ = 1) (n : ℕ) :
    ‖radialGlobalSatakeCoeff w n‖ ≤
      (((n + 1 : ℕ) : ℝ) ^ (Fintype.card ι : ℕ)) := by
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
        (((m.factorization p.1 + 1 : ℕ) : ℝ) ^ d) := by
    intro p
    simpa [d, Nat.cast_pow] using
      norm_radialLocalEulerCoeff_le_add_one_pow
        (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
        (hw (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
        (m.factorization p.1)
  change ‖∏ p : ↑m.primeFactors, _‖ ≤ (m : ℝ) ^ d
  rw [norm_prod]
  calc
    ∏ p : ↑m.primeFactors,
        ‖radialLocalEulerCoeff
          (w (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
          (m.factorization p.1)‖
        ≤ ∏ p : ↑m.primeFactors,
          (((m.factorization p.1 + 1 : ℕ) : ℝ) ^ d) := by
            exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => hlocal p)
    _ = ((∏ p : ↑m.primeFactors,
          (((m.factorization p.1 + 1 : ℕ) : ℝ))) ^ d) := by
            rw [Finset.prod_pow]
    _ = (((m.divisors.card : ℕ) : ℝ) ^ d) := by
            congr 1
            have hnat :
                (∏ p : ↑m.primeFactors, (m.factorization p.1 + 1)) =
                  m.divisors.card := by
              rw [Finset.prod_coe_sort
                m.primeFactors (fun p : ℕ => m.factorization p + 1)]
              exact (Nat.card_divisors hm).symm
            exact_mod_cast hnat
    _ ≤ (m : ℝ) ^ d := by
            gcongr
            exact_mod_cast Nat.card_divisors_le_self m

/-- Every all-place unitary coefficient bank starts with coefficient one. -/
theorem radialGlobalSatakeCoeff_zero
    {ι : Type*} [Fintype ι] (w : Nat.Primes → ι → ℂ) :
    radialGlobalSatakeCoeff w 0 = 1 := by
  unfold radialGlobalSatakeCoeff
  letI : IsEmpty ↥(Nat.primeFactors 1) :=
    ⟨fun p => by simpa using p.property⟩
  exact Fintype.prod_empty _

/-- The primal global CPS coefficient bank. -/
noncomputable def cpsPrimalSatakeCoeff
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) : ℕ → ℂ :=
  radialGlobalSatakeCoeff (cpsTensorWeight r α τ)

/-- The contragredient global CPS coefficient bank. -/
noncomputable def cpsDualSatakeCoeff
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) : ℕ → ℂ :=
  radialGlobalSatakeCoeff (cpsTensorDualWeight r α τ)

theorem cpsPrimalSatakeCoeff_norm_le
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (n : ℕ) :
    ‖cpsPrimalSatakeCoeff r α τ n‖ ≤
      (((n + 1 : ℕ) : ℝ) ^ (Fintype.card (Fin (r + 1) × κ) : ℕ)) :=
  radialGlobalSatakeCoeff_norm_le _ (cpsTensorWeight_unit r α τ) n

theorem cpsDualSatakeCoeff_norm_le
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (n : ℕ) :
    ‖cpsDualSatakeCoeff r α τ n‖ ≤
      (((n + 1 : ℕ) : ℝ) ^ (Fintype.card (Fin (r + 1) × κ) : ℕ)) :=
  radialGlobalSatakeCoeff_norm_le _ (cpsTensorDualWeight_unit r α τ) n

@[reducible] noncomputable def cpsPrimalCoefficientOneInvertible
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) :
    Invertible ((CarrierTheta.coefficientArithmetic (cpsPrimalSatakeCoeff r α τ)) 1) := by
  rw [CarrierTheta.coefficientArithmetic]
  simp [cpsPrimalSatakeCoeff, radialGlobalSatakeCoeff_zero]
  exact invertibleOne

@[reducible] noncomputable def cpsDualCoefficientOneInvertible
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) :
    Invertible ((CarrierTheta.coefficientArithmetic (cpsDualSatakeCoeff r α τ)) 1) := by
  rw [CarrierTheta.coefficientArithmetic]
  simp [cpsDualSatakeCoeff, radialGlobalSatakeCoeff_zero]
  exact invertibleOne

theorem cpsPrimalCoefficientArithmetic_norm_le
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (n : ℕ) :
    ‖(CarrierTheta.coefficientArithmetic (cpsPrimalSatakeCoeff r α τ)) n‖ ≤
      (1 : ℝ) * (n : ℝ) ^ (Fintype.card (Fin (r + 1) × κ) : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simp [CarrierTheta.coefficientArithmetic]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hbound := cpsPrimalSatakeCoeff_norm_le r α τ (n - 1)
    rw [Nat.sub_add_cancel hn1] at hbound
    simpa [CarrierTheta.coefficientArithmetic, hn] using hbound

theorem cpsDualCoefficientArithmetic_norm_le
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (n : ℕ) :
    ‖(CarrierTheta.coefficientArithmetic (cpsDualSatakeCoeff r α τ)) n‖ ≤
      (1 : ℝ) * (n : ℝ) ^ (Fintype.card (Fin (r + 1) × κ) : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simp [CarrierTheta.coefficientArithmetic]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hbound := cpsDualSatakeCoeff_norm_le r α τ (n - 1)
    rw [Nat.sub_add_cancel hn1] at hbound
    simpa [CarrierTheta.coefficientArithmetic, hn] using hbound

/-- The primal completion kernel synthesized from the complete primal Satake bank. -/
noncomputable def cpsPrimalCarrierKernel
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) : ℝ → ℂ :=
  CarrierTheta.dilationKernel
    (ArithmeticFunction.dirichletInverse
      (CarrierTheta.coefficientArithmetic (cpsPrimalSatakeCoeff r α τ))
      (cpsPrimalCoefficientOneInvertible r α τ))
    (CriticalLinePhasor.StrandExchange.completedLogTheta
      twistedSymmetricPowerExchangeCarrier 1)

/-- The anti-helix completion kernel synthesized from the contragredient Satake bank. -/
noncomputable def cpsDualCarrierKernel
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) : ℝ → ℂ :=
  CarrierTheta.dilationKernel
    (ArithmeticFunction.dirichletInverse
      (CarrierTheta.coefficientArithmetic (cpsDualSatakeCoeff r α τ))
      (cpsDualCoefficientOneInvertible r α τ))
    (CriticalLinePhasor.StrandExchange.completedLogThetaDual
      twistedSymmetricPowerExchangeCarrier 1)

/-- The primal all-place CPS bank assembled as radius, phase, and multiplicative height. -/
noncomputable def cpsPrimal3DBankReadout
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsPrimalSatakeCoeff r α τ) n x) *
      cpsPrimalCarrierKernel r α τ
        (multiplicativeHeight (coefficientFiber (cpsPrimalSatakeCoeff r α τ) n x))

/-- The contragredient all-place anti-helix bank in the same three coordinates. -/
noncomputable def cpsDual3DBankReadout
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor (coefficientFiber (cpsDualSatakeCoeff r α τ) n x) *
      cpsDualCarrierKernel r α τ
        (multiplicativeHeight (coefficientFiber (cpsDualSatakeCoeff r α τ) n x))

/-- Projection of the primal 3D bank is its coefficient theta. -/
theorem cpsPrimal3DBankReadout_eq_theta
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) {x : ℝ} (hx : 0 < x) :
    cpsPrimal3DBankReadout r α τ x =
      CarrierTheta.theta (cpsPrimalSatakeCoeff r α τ) (cpsPrimalCarrierKernel r α τ) x := by
  unfold cpsPrimal3DBankReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsPrimalSatakeCoeff r α τ) n hx]

/-- Projection of the dual 3D bank is its contragredient coefficient theta. -/
theorem cpsDual3DBankReadout_eq_theta
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) {x : ℝ} (hx : 0 < x) :
    cpsDual3DBankReadout r α τ x =
      CarrierTheta.theta (cpsDualSatakeCoeff r α τ) (cpsDualCarrierKernel r α τ) x := by
  unfold cpsDual3DBankReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber (cpsDualSatakeCoeff r α τ) n hx]

/-- The strong pair for the non-self-dual CPS twist and its contragredient, synthesized only after
both all-place 3D coefficient sources have been assembled. -/
noncomputable def cpsDualPairStrongFEPair
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) : StrongFEPair ℂ :=
  CarrierTheta.automaticCoefficientThetaStrongFEPair
    twistedSymmetricPowerExchangeCarrier
    twistedSymmetricPowerExchangeCarrier_continuous
    1 one_ne_zero twistedSymmetricPowerExchangeCarrier_exchange
    1 zero_lt_one 0 twistedSymmetricPowerExchangeCarrier_logTheta_isBigO
    (cpsPrimalSatakeCoeff r α τ)
    (cpsDualSatakeCoeff r α τ)
    (cpsPrimalCoefficientOneInvertible r α τ)
    (cpsDualCoefficientOneInvertible r α τ)
    (Fintype.card (Fin (r + 1) × κ))
    (Fintype.card (Fin (r + 1) × κ))
    1 1 zero_le_one zero_le_one
    (cpsPrimalCoefficientArithmetic_norm_le r α τ)
    (cpsDualCoefficientArithmetic_norm_le r α τ)

/-- The primal function of the strong pair is the projection of the primal 3D bank. -/
theorem cpsDualPairStrongFEPair_f_eq_3DBankReadout
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) {x : ℝ} (hx : 0 < x) :
    (cpsDualPairStrongFEPair r α τ).f x = cpsPrimal3DBankReadout r α τ x := by
  rw [cpsPrimal3DBankReadout_eq_theta r α τ hx]
  rfl

/-- The dual function of the strong pair is the projection of the contragredient 3D bank. -/
theorem cpsDualPairStrongFEPair_g_eq_3DBankReadout
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) {x : ℝ} (hx : 0 < x) :
    (cpsDualPairStrongFEPair r α τ).g x = cpsDual3DBankReadout r α τ x := by
  rw [cpsDual3DBankReadout_eq_theta r α τ hx]
  rfl

/-- Exact global reflection of the primal and contragredient all-place 3D banks. -/
theorem cpsDualPair3D_globalHelixReflection
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) {x : ℝ} (hx : 0 < x) :
    cpsPrimal3DBankReadout r α τ (1 / x) =
      (x : ℂ) * cpsDual3DBankReadout r α τ x := by
  let P := cpsDualPairStrongFEPair r α τ
  have hfe := P.h_feq x hx
  have hkP : P.k = 1 := rfl
  have hεP : P.ε = 1 := by
    simp [P, cpsDualPairStrongFEPair,
      CarrierTheta.automaticCoefficientThetaStrongFEPair,
      CarrierTheta.coefficientThetaStrongFEPair]
  rw [hkP, hεP] at hfe
  rw [← cpsDualPairStrongFEPair_f_eq_3DBankReadout
        r α τ (one_div_pos.mpr hx),
      ← cpsDualPairStrongFEPair_g_eq_3DBankReadout r α τ hx]
  simpa using hfe

/-- Entirety, vertical-strip boundedness, and the primal/contragredient functional equation for a
general CPS twist. -/
theorem cpsDualPair_twistedNiceness
    {κ : Type*} [Fintype κ] (r : ℕ) (α : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) :
    let P := cpsDualPairStrongFEPair r α τ
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := cpsDualPairStrongFEPair r α τ
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip P u v,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip P.symm u v,
    P.functional_equation⟩

/-- The complete CPS twist range `1 ≤ m < r` is nice, including non-self-dual twists. -/
theorem cpsAllTwists_twistedNiceness
    (r : ℕ) (α : UnitaryPrimePhase) :
    ∀ m : ℕ, 1 ≤ m → m < r → ∀ τ : UnitarySatakeFamily (Fin m),
      let P := cpsDualPairStrongFEPair r α τ
      Differentiable ℂ P.Λ ∧
      Differentiable ℂ P.symm.Λ ∧
      (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
        u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
      (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
        u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
      (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  intro m _ _ τ
  exact cpsDualPair_twistedNiceness r α τ

/-- The complete CPS range has exact primal/contragredient reflection at the 3D-bank level. -/
theorem cpsAllTwists_3D_globalHelixReflection
    (r : ℕ) (α : UnitaryPrimePhase) :
    ∀ m : ℕ, 1 ≤ m → m < r → ∀ τ : UnitarySatakeFamily (Fin m),
      ∀ x : ℝ, 0 < x →
        cpsPrimal3DBankReadout r α τ (1 / x) =
          (x : ℂ) * cpsDual3DBankReadout r α τ x := by
  intro m _ _ τ x hx
  exact cpsDualPair3D_globalHelixReflection r α τ hx

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.norm_radialLocalEulerCoeff_le_add_one_pow
#print axioms CriticalLinePhasor.GlobalHelix.radialGlobalSatakeCoeff_norm_le
#print axioms CriticalLinePhasor.GlobalHelix.cpsDualPairStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.cpsDualPair3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.cpsDualPair_twistedNiceness
#print axioms CriticalLinePhasor.GlobalHelix.cpsAllTwists_twistedNiceness
#print axioms CriticalLinePhasor.GlobalHelix.cpsAllTwists_3D_globalHelixReflection
