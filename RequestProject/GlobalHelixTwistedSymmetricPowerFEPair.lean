import RequestProject.GlobalHelixFiniteTensorEulerZeroMode
import RequestProject.GlobalHelixFixedBankReflection
import RequestProject.GlobalHelixLocalEulerBounds
import RequestProject.CarrierThetaAutomaticNiceness
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Twisted symmetric-power Satake banks as strong 3D carrier pairs

The source is constructed in three dimensions before any scalar Mellin readout is taken.  At each
selected place, `Sym^r` is tensored with the twist fiber.  Its Euler coefficients are placed at
their native multiplicative heights as `(radius, phase, log-height)` helix fibers.  The global
involution and reciprocal-height shear build the anti-helix bank.  Projection of those two 3D banks
then supplies Mathlib's `StrongFEPair`.

Searches used before construction:
* `rg -n -i "WeakFEPair|StrongFEPair|weak_fe_pair|strong_fe_pair" RequestProject`
* `rg -n -i "Satake|sym.*twist|tensor.*symmetric|localFactor|localPoly" RequestProject`
* the same searches in `.lake/packages/mathlib/Mathlib`.

Two decomposition starts were checked:
* specialize `finiteTensorEulerZeroModeStrongFEPair` to `tensorFiber (symFiber r) Wτ`;
* assemble a fixed-completion coefficient theta through `coefficientThetaStrongFEPair`.
The first route preserves the native 3D Euler source and is used here.
-/

open Real Complex

namespace CriticalLinePhasor.GlobalHelix

/-- The local Rankin--Selberg fiber `Sym^r ⊗ τ` at one Satake place. -/
noncomputable def twistedSymmetricPowerFiber
    { κ : Type* } [Fintype κ]
    (r : ℕ) (alpha : ℂ) (halpha : ‖alpha‖ = 1) (Wtau : FiniteWeightFiber κ) :
    FiniteWeightFiber (Fin (r + 1) × κ) :=
  FiniteWeightFiber.tensorFiber (FiniteWeightFiber.symFiber r alpha halpha) Wtau

/-- The finite selected-place family of twisted symmetric-power fibers. -/
noncomputable def twistedSymmetricPowerFiberFamily
    {V κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) :
    V → FiniteWeightFiber (Fin (r + 1) × κ) :=
  fun v => twistedSymmetricPowerFiber r (alpha v) (halpha v) (Wtau v)

/-- The original twisted symmetric-power Euler seed in a finite symmetric exponent box. -/
noncomputable def finiteTwistedSymmetricPowerSeedAmplitude
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (N : ℕ) :
    FiniteExponentBox S N → ℂ :=
  finiteTensorEulerSeedAmplitude S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) N

/-- The primal twisted symmetric-power 3D helix bank. -/
noncomputable def finiteTwistedSymmetricPower3DBankReadout
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (q : V → ℝ)
    (N : ℕ) (c x : ℝ) : ℂ :=
  finiteTensorEulerZeroMode3DBankReadout S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) q N c x

/-- The transformed anti-helix bank, built by the global involution and height shear. -/
noncomputable def finiteTwistedSymmetricPower3DTransformedReadout
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (q : V → ℝ)
    (N : ℕ) (c x : ℝ) : ℂ :=
  finiteTensorEulerZeroMode3DTransformedReadout S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) q N c x

/-- Exact 3D reflection of every finite twisted symmetric-power Satake bank. -/
theorem finiteTwistedSymmetricPower3D_globalHelixReflection
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    finiteTwistedSymmetricPower3DBankReadout S r alpha halpha Wtau q N c x =
      ((1 / x ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        finiteTwistedSymmetricPower3DTransformedReadout
          S r alpha halpha Wtau q N c x := by
  exact finiteTensorEulerZeroMode3D_globalHelixReflection S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) q N hq hc hx

/-- A concrete `StrongFEPair` constructed from the finite twisted symmetric-power Satake bank. -/
noncomputable def finiteTwistedSymmetricPowerStrongFEPair
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) (hc : 0 < c) : StrongFEPair ℂ :=
  finiteTensorEulerZeroModeStrongFEPair S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) q N hq c hc

/-- The actual finite twisted symmetric-power coefficient-height Dirichlet readout. -/
noncomputable def finiteTwistedSymmetricPowerTruncatedDirichletReadout
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (q : V → ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  finiteTensorEulerTruncatedDirichletReadout S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) q N s

/-- The completed Mellin readout is the actual truncated twisted symmetric-power Euler readout
times the fixed zero-mode completion multiplier. -/
theorem finiteTwistedSymmetricPower_initialIdentification
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) (hc : 0 < c) (s : ℂ) :
    let P := finiteTwistedSymmetricPowerStrongFEPair
      S r alpha halpha Wtau q N hq c hc
    P.Λ s = finiteTwistedSymmetricPowerTruncatedDirichletReadout
      S r alpha halpha Wtau q N s * mellin (zeroModeGaussianKernel c) s := by
  exact finiteTensorEulerZeroMode_initialIdentification S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) q N hq c hc s

/-- Entirety, vertical-strip boundedness, and the functional equation for every finite twisted
symmetric-power Satake bank. -/
theorem finiteTwistedSymmetricPower_twistedNiceness
    {V κ : Type*} [Fintype κ]
    (S : Finset V) (r : ℕ) (alpha : V → ℂ) (halpha : ∀ v, ‖alpha v‖ = 1)
    (Wtau : V → FiniteWeightFiber κ) (q : V → ℝ) (N : ℕ)
    (hq : ∀ v ∈ S, 0 < q v) (c : ℝ) (hc : 0 < c) :
    let P := finiteTwistedSymmetricPowerStrongFEPair
      S r alpha halpha Wtau q N hq c hc
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  exact finiteTensorEulerZeroMode_twistedNiceness S
    (twistedSymmetricPowerFiberFamily r alpha halpha Wtau) q N hq c hc

/-! ## All-place fixed-completion bank -/

/-- The actual global coefficient at the positive integer `n + 1`, assembled only over its finite
prime support.  Each local factor is the `Sym^r ⊗ τ` Satake fiber at that prime. -/
noncomputable def twistedSymmetricPowerSatakeCoeff
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (n : ℕ) : ℂ :=
  ∏ p : ↑(n + 1).primeFactors,
    localEulerCoeff
      (twistedSymmetricPowerFiber r
        (alpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
        (halpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
        (Wtau (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)))
      ((n + 1).factorization p.1)

/-- The all-place coefficient has a uniform polynomial bound determined by the local tensor rank. -/
theorem twistedSymmetricPowerSatakeCoeff_norm_le
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (n : ℕ) :
    ‖twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau n‖ ≤
      (((n + 1 : ℕ) : ℝ) ^ (Fintype.card (Fin (r + 1) × κ) : ℕ)) := by
  classical
  let m : ℕ := n + 1
  let d : ℕ := Fintype.card (Fin (r + 1) × κ)
  have hm : m ≠ 0 := by
    dsimp [m]
    omega
  have hlocal : ∀ p : ↑m.primeFactors,
      ‖localEulerCoeff
        (twistedSymmetricPowerFiber r
          (alpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
          (halpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
          (Wtau (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)))
        (m.factorization p.1)‖ ≤
        (((m.factorization p.1 + 1 : ℕ) : ℝ) ^ d) := by
    intro p
    simpa [d, Nat.cast_pow] using
      norm_localEulerCoeff_le_add_one_pow
        (twistedSymmetricPowerFiber r
          (alpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
          (halpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
          (Wtau (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)))
        (m.factorization p.1)
  change ‖∏ p : ↑m.primeFactors, _‖ ≤ (m : ℝ) ^ d
  rw [norm_prod]
  calc
    ∏ p : ↑m.primeFactors, ‖localEulerCoeff
          (twistedSymmetricPowerFiber r
            (alpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
            (halpha (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes))
            (Wtau (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)))
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

/-- The all-place Satake product is normalized to coefficient one at integer height one. -/
theorem twistedSymmetricPowerSatakeCoeff_zero
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) :
    twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau 0 = 1 := by
  unfold twistedSymmetricPowerSatakeCoeff
  letI : IsEmpty ↥(Nat.primeFactors 1) :=
    ⟨fun p => by simpa using p.property⟩
  exact Fintype.prod_empty _

/-- The shifted positive arithmetic function is normalized and therefore invertible at one. -/
@[reducible] noncomputable def twistedSymmetricPowerCoefficientOneInvertible
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) :
    Invertible
      ((CarrierTheta.coefficientArithmetic
        (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)) 1) := by
  rw [CarrierTheta.coefficientArithmetic]
  simp [twistedSymmetricPowerSatakeCoeff_zero]
  exact invertibleOne

/-- Polynomial growth in the positive-integer indexing used by Dirichlet convolution. -/
theorem twistedSymmetricPowerCoefficientArithmetic_norm_le
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (n : ℕ) :
    ‖(CarrierTheta.coefficientArithmetic
      (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)) n‖ ≤
      (1 : ℝ) * (n : ℝ) ^ (Fintype.card (Fin (r + 1) × κ) : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simp [CarrierTheta.coefficientArithmetic]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hbound := twistedSymmetricPowerSatakeCoeff_norm_le
      r alpha halpha Wtau (n - 1)
    rw [Nat.sub_add_cancel hn1] at hbound
    simpa [CarrierTheta.coefficientArithmetic, hn] using hbound

/-! ## Infinite 3D exchange bank and strong functional-equation pair -/

/-- A nonzero self-dual carrier clock used to complete the all-place spatial bank. -/
noncomputable def twistedSymmetricPowerExchangeCarrier (z : ℂ) : ℂ :=
  CriticalLinePhasor.ChiralityHB.symClock (-1) 0 z

theorem twistedSymmetricPowerExchangeCarrier_continuous :
    Continuous twistedSymmetricPowerExchangeCarrier := by
  unfold twistedSymmetricPowerExchangeCarrier CriticalLinePhasor.ChiralityHB.symClock
  fun_prop

theorem twistedSymmetricPowerExchangeCarrier_exchange (z : ℂ) :
    (starRingEnd ℂ) (twistedSymmetricPowerExchangeCarrier ((starRingEnd ℂ) z)) =
      1 * twistedSymmetricPowerExchangeCarrier z := by
  simpa [twistedSymmetricPowerExchangeCarrier] using
    (CriticalLinePhasor.ChiralityHB.symClock_star
      (α := (-1 : ℂ)) (by norm_num) 0 z)

theorem twistedSymmetricPowerExchangeCarrier_logTheta_isBigO :
    CriticalLinePhasor.StrandExchange.logTheta twistedSymmetricPowerExchangeCarrier
      =O[Filter.atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
  change CriticalLinePhasor.StrandExchange.logTheta
      (CriticalLinePhasor.ChiralityHB.symClock (-1) 0)
        =O[Filter.atTop] (fun x : ℝ => x ^ (0 : ℝ))
  simpa using
    (CriticalLinePhasor.StrandExchange.symClock_logTheta_isBigO (-1 : ℂ) 0)

/-- The coefficient-dependent completion kernel synthesized from the actual Satake bank. -/
noncomputable def twistedSymmetricPowerCarrierKernel
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) : ℝ → ℂ :=
  CarrierTheta.dilationKernel
    (ArithmeticFunction.dirichletInverse
      (CarrierTheta.coefficientArithmetic
        (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau))
      (twistedSymmetricPowerCoefficientOneInvertible r alpha halpha Wtau))
    (CriticalLinePhasor.StrandExchange.completedLogTheta
      twistedSymmetricPowerExchangeCarrier 1)

/-- The anti-helix completion kernel synthesized from the same Satake bank. -/
noncomputable def twistedSymmetricPowerCarrierDualKernel
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) : ℝ → ℂ :=
  CarrierTheta.dilationKernel
    (ArithmeticFunction.dirichletInverse
      (CarrierTheta.coefficientArithmetic
        (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau))
      (twistedSymmetricPowerCoefficientOneInvertible r alpha halpha Wtau))
    (CriticalLinePhasor.StrandExchange.completedLogThetaDual
      twistedSymmetricPowerExchangeCarrier 1)

/-- The infinite 3D Satake bank: coefficient radius and phase remain transverse coordinates, and
the synthesized kernel is read only from multiplicative height. -/
noncomputable def twistedSymmetricPowerCarrier3DBankReadout
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
      (coefficientFiber (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) n x) *
    twistedSymmetricPowerCarrierKernel r alpha halpha Wtau
      (multiplicativeHeight
        (coefficientFiber (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) n x))

/-- Only after assembling the infinite 3D bank do we project it to the coefficient theta. -/
theorem twistedSymmetricPowerCarrier3DBankReadout_eq_theta
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) {x : ℝ} (hx : 0 < x) :
    twistedSymmetricPowerCarrier3DBankReadout r alpha halpha Wtau x =
      CarrierTheta.theta (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
        (twistedSymmetricPowerCarrierKernel r alpha halpha Wtau) x := by
  unfold twistedSymmetricPowerCarrier3DBankReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber
      (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) n hx]

/-- The infinite anti-helix bank before its final scalar projection. -/
noncomputable def twistedSymmetricPowerCarrier3DDualBankReadout
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (x : ℝ) : ℂ :=
  ∑' n : ℕ,
    fiberPhasor
      (coefficientFiber (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) n x) *
    twistedSymmetricPowerCarrierDualKernel r alpha halpha Wtau
      (multiplicativeHeight
        (coefficientFiber (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) n x))

theorem twistedSymmetricPowerCarrier3DDualBankReadout_eq_theta
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) {x : ℝ} (hx : 0 < x) :
    twistedSymmetricPowerCarrier3DDualBankReadout r alpha halpha Wtau x =
      CarrierTheta.theta (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
        (twistedSymmetricPowerCarrierDualKernel r alpha halpha Wtau) x := by
  unfold twistedSymmetricPowerCarrier3DDualBankReadout CarrierTheta.theta
  apply tsum_congr
  intro n
  rw [fiberPhasor_coefficientFiber,
    multiplicativeHeight_coefficientFiber
      (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) n hx]

/-- A `StrongFEPair` constructed with no analytic-pair hypothesis from the general all-place
twisted symmetric-power Satake bank. -/
noncomputable def twistedSymmetricPowerCarrierStrongFEPair
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) : StrongFEPair ℂ :=
  CarrierTheta.automaticCoefficientThetaStrongFEPair
    twistedSymmetricPowerExchangeCarrier
    twistedSymmetricPowerExchangeCarrier_continuous
    1 one_ne_zero twistedSymmetricPowerExchangeCarrier_exchange
    1 zero_lt_one 0 twistedSymmetricPowerExchangeCarrier_logTheta_isBigO
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
    (twistedSymmetricPowerCoefficientOneInvertible r alpha halpha Wtau)
    (twistedSymmetricPowerCoefficientOneInvertible r alpha halpha Wtau)
    (Fintype.card (Fin (r + 1) × κ))
    (Fintype.card (Fin (r + 1) × κ))
    1 1 zero_le_one zero_le_one
    (twistedSymmetricPowerCoefficientArithmetic_norm_le r alpha halpha Wtau)
    (twistedSymmetricPowerCoefficientArithmetic_norm_le r alpha halpha Wtau)

/-- The corresponding explicit weak interface, obtained from the constructed strong pair. -/
noncomputable def twistedSymmetricPowerCarrierWeakFEPair
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) : WeakFEPair ℂ :=
  (twistedSymmetricPowerCarrierStrongFEPair r alpha halpha Wtau).toWeakFEPair

/-- The primal function of the constructed pair is exactly the 1D projection of the actual
all-place 3D Satake bank with its synthesized completion kernel. -/
theorem twistedSymmetricPowerCarrierStrongFEPair_f_eq_3DBankReadout
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) {x : ℝ} (hx : 0 < x) :
    (twistedSymmetricPowerCarrierStrongFEPair r alpha halpha Wtau).f x =
      twistedSymmetricPowerCarrier3DBankReadout r alpha halpha Wtau x := by
  rw [twistedSymmetricPowerCarrier3DBankReadout_eq_theta r alpha halpha Wtau hx]
  rfl

theorem twistedSymmetricPowerCarrierStrongFEPair_g_eq_3DDualBankReadout
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) {x : ℝ} (hx : 0 < x) :
    (twistedSymmetricPowerCarrierStrongFEPair r alpha halpha Wtau).g x =
      twistedSymmetricPowerCarrier3DDualBankReadout r alpha halpha Wtau x := by
  rw [twistedSymmetricPowerCarrier3DDualBankReadout_eq_theta r alpha halpha Wtau hx]
  rfl

/-- Exact global reflection of the infinite primal and anti-helix 3D banks. -/
theorem twistedSymmetricPowerCarrier3D_globalHelixReflection
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) {x : ℝ} (hx : 0 < x) :
    twistedSymmetricPowerCarrier3DBankReadout r alpha halpha Wtau (1 / x) =
      (x : ℂ) * twistedSymmetricPowerCarrier3DDualBankReadout
        r alpha halpha Wtau x := by
  let P := twistedSymmetricPowerCarrierStrongFEPair r alpha halpha Wtau
  have hfe := P.h_feq x hx
  have hkP : P.k = 1 := rfl
  have hεP : P.ε = 1 := by
    simp [P, twistedSymmetricPowerCarrierStrongFEPair,
      CarrierTheta.automaticCoefficientThetaStrongFEPair,
      CarrierTheta.coefficientThetaStrongFEPair]
  rw [hkP, hεP] at hfe
  rw [← twistedSymmetricPowerCarrierStrongFEPair_f_eq_3DBankReadout
        r alpha halpha Wtau (one_div_pos.mpr hx),
      ← twistedSymmetricPowerCarrierStrongFEPair_g_eq_3DDualBankReadout
        r alpha halpha Wtau hx]
  simpa using hfe

/-- Entirety, vertical-strip boundedness, and the functional equation of the all-place pair. -/
theorem twistedSymmetricPowerCarrier_twistedNiceness
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) :
    let P := twistedSymmetricPowerCarrierStrongFEPair r alpha halpha Wtau
    Differentiable ℂ P.Λ ∧
    Differentiable ℂ P.symm.Λ ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B) ∧
    (∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ,
      u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B) ∧
    (∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s) := by
  dsimp only
  let P := twistedSymmetricPowerCarrierStrongFEPair r alpha halpha Wtau
  exact ⟨P.differentiable_Λ, P.symm.differentiable_Λ,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip P u v,
    fun u v =>
      CriticalLinePhasor.CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip P.symm u v,
    P.functional_equation⟩

/-- On its initial half-plane the constructed entire Mellin readout is the actual all-place
Satake Dirichlet series times the Mellin transform of the synthesized completion kernel. -/
theorem twistedSymmetricPowerCarrier_initialIdentification
    {κ : Type*} [Fintype κ]
    (r : ℕ) (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (s : ℂ)
    (hkernel : MellinConvergent
      (twistedSymmetricPowerCarrierKernel r alpha halpha Wtau) s)
    (hs : (Fintype.card (Fin (r + 1) × κ) : ℝ) + 1 < s.re) :
    (twistedSymmetricPowerCarrierStrongFEPair r alpha halpha Wtau).Λ s =
      CarrierTheta.dirichlet (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) s *
        mellin (twistedSymmetricPowerCarrierKernel r alpha halpha Wtau) s := by
  change mellin
      (CarrierTheta.theta (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
        (twistedSymmetricPowerCarrierKernel r alpha halpha Wtau)) s = _
  exact (CarrierTheta.theta_hasMellin_of_polynomial
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
    (twistedSymmetricPowerCarrierKernel r alpha halpha Wtau) s
    1 (Fintype.card (Fin (r + 1) × κ) : ℝ) hkernel
    (fun n => by
      change ‖twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau n‖ ≤
        1 * Real.rpow (((n + 1 : ℕ) : ℝ))
          ((Fintype.card (Fin (r + 1) × κ) : ℕ) : ℝ)
      rw [one_mul]
      exact (twistedSymmetricPowerSatakeCoeff_norm_le r alpha halpha Wtau n).trans_eq
        (Real.rpow_natCast _ _).symm) hs).2

/-- The primary all-place 3D helix bank with the coefficient-independent completion kernel. -/
noncomputable def twistedSymmetricPowerFixed3DBankReadout
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (x : ℝ) : ℂ :=
  fixedPrimalBankReadout mu
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) x

/-- Projection of the all-place 3D source is exactly the fixed-completion coefficient theta. -/
theorem twistedSymmetricPowerFixed3DBankReadout_eq_theta
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) {x : ℝ} (hx : 0 < x) :
    twistedSymmetricPowerFixed3DBankReadout mu r alpha halpha Wtau x =
      CarrierTheta.theta (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
        (completionKernel mu) x := by
  exact fixedPrimalBankReadout_eq_theta mu
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) hx

/-- The fixed-completion anti-helix bank obtained by conjugating the Satake ledger, applying the
global involution, and performing the reciprocal-height shear. -/
noncomputable def twistedSymmetricPowerFixed3DTransformedReadout
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (x : ℝ) : ℂ :=
  fixedTransformedDualBankReadout mu
    (fun n => (starRingEnd ℂ)
      (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau n)) x

/-- The transformed fixed-completion 3D bank projects to the same Satake theta at reciprocal
external height. -/
theorem twistedSymmetricPowerFixed3DTransformedReadout_eq_theta_one_div
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) {x : ℝ} (hx : 0 < x) :
    twistedSymmetricPowerFixed3DTransformedReadout mu r alpha halpha Wtau x =
      CarrierTheta.theta (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
        (completionKernel mu) (1 / x) := by
  exact fixedTransformedConjugateDualBankReadout_eq_theta_one_div mu
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) hx

/-- The fixed-completion odd spatial channel specialized to the all-place twisted symmetric-power
Satake bank. -/
noncomputable def twistedSymmetricPowerFixedBankOddChannel
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ)
    (eta : ℂ) (weight x : ℝ) : ℂ :=
  fixedBankOddChannel mu
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) eta weight x

/-- Exact off-weld specification: vanishing of the specialized 3D odd channel is equivalent to
the fixed-completion theta reflection. -/
theorem twistedSymmetricPowerFixedBankOddChannel_eq_zero_iff_theta_reflection
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ)
    (eta : ℂ) (weight : ℝ) {x : ℝ} (hx : 0 < x) :
    twistedSymmetricPowerFixedBankOddChannel
        mu r alpha halpha Wtau eta weight x = 0 ↔
      CarrierTheta.theta (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
          (completionKernel mu) x =
        (eta * (x ^ weight : ℝ)) •
          CarrierTheta.theta (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau)
            (completionKernel mu) (1 / x) := by
  exact fixedBankOddChannel_eq_zero_iff_theta_reflection mu
    (twistedSymmetricPowerSatakeCoeff r alpha halpha Wtau) eta weight hx

/-- At the three-dimensional weld `x = 1`, the primal fixed-completion bank and the transformed
anti-helix bank coincide exactly. -/
theorem twistedSymmetricPowerFixed3D_weldReflection
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) :
    twistedSymmetricPowerFixed3DBankReadout mu r alpha halpha Wtau 1 =
      twistedSymmetricPowerFixed3DTransformedReadout mu r alpha halpha Wtau 1 := by
  rw [twistedSymmetricPowerFixed3DBankReadout_eq_theta mu r alpha halpha Wtau one_pos,
    twistedSymmetricPowerFixed3DTransformedReadout_eq_theta_one_div
      mu r alpha halpha Wtau one_pos]
  norm_num

/-- The fixed-completion odd channel vanishes at the 3D weld for unit exchange and every weight. -/
theorem twistedSymmetricPowerFixedBankOddChannel_weld_zero
    {κ : Type*} [Fintype κ]
    (mu : List ℂ) (r : ℕ)
    (alpha : Nat.Primes → ℂ) (halpha : ∀ p, ‖alpha p‖ = 1)
    (Wtau : Nat.Primes → FiniteWeightFiber κ) (weight : ℝ) :
    twistedSymmetricPowerFixedBankOddChannel
      mu r alpha halpha Wtau 1 weight 1 = 0 := by
  apply (twistedSymmetricPowerFixedBankOddChannel_eq_zero_iff_theta_reflection
    mu r alpha halpha Wtau 1 weight one_pos).2
  norm_num

end CriticalLinePhasor.GlobalHelix

#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerFiber
#print axioms CriticalLinePhasor.GlobalHelix.finiteTwistedSymmetricPower3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.finiteTwistedSymmetricPowerStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.finiteTwistedSymmetricPower_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.finiteTwistedSymmetricPower_twistedNiceness
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerSatakeCoeff_norm_le
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerFixed3DBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerSatakeCoeff_zero
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCoefficientArithmetic_norm_le
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrier3DBankReadout_eq_theta
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrierStrongFEPair
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrierWeakFEPair
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrierStrongFEPair_f_eq_3DBankReadout
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrierStrongFEPair_g_eq_3DDualBankReadout
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrier3D_globalHelixReflection
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrier_twistedNiceness
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerCarrier_initialIdentification
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerFixed3DTransformedReadout_eq_theta_one_div
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerFixedBankOddChannel_eq_zero_iff_theta_reflection
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerFixed3D_weldReflection
#print axioms CriticalLinePhasor.GlobalHelix.twistedSymmetricPowerFixedBankOddChannel_weld_zero
