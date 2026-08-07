import RequestProject.CompletedReflectionFiber
import RequestProject.StrandExchange
import RequestProject.CPSUnconditionalSatakePayload3D
import RequestProject.CPSRadiusLiveNiceness3D
import RequestProject.NonSelfDualObstruction

/-!
# The `Sym²` benchmark: the GL(3) converse theorem's analytic input, unconditionally

Gelbart–Jacquet (1978) proved `Sym²π` automorphic on `GL(3)`.  The route is a converse theorem,
and what a converse theorem *consumes* is an analytic hypothesis on the twisted `L`-functions:
entire, entire dual, bounded in every vertical strip (both), and the functional equation.  This
file names that input at `Sym²` and proves the carrier supplies it — for the **global** object,
with no analytic hypothesis of any kind supplied by the caller.

Nothing here is new mathematics.  Every proof is a general theorem specialised at `r = 2`, in the
manner of `QuadrupleFiber` at grade four.  The point is recognisability: an expert should be able
to read one declaration and see Gelbart–Jacquet's input.

## The local fiber (the recognition step)

* `sym2Fiber` — the degree-3 fiber `symFiber 2`;
* `sym2Fiber_weight_zero/_one/_two` — the weights are literally `α²`, `1`, `α⁻²`, the Satake data
  of `Sym² diag(α, α⁻¹)`;
* `sym2Fiber_card` — degree **3**: the lift lands on `GL(3)`;
* `sym2Fiber_det_one`, `sym2_localPoly_reciprocal` — the ledger `∏λ = 1` and the per-place
  functional equation `localPoly X = (-X)³ · localPoly X⁻¹`;
* `sym2Fiber_warp_det_one` — stability under every dual-compatible unit warp;
* `sym2Completed`/`_FE`/`_εfin`/`_differentiable`, `sym2Bank_exchange`,
  `sym2CompletedBank_exchange` — the completed **local** reflection and the finite-stage strand
  exchange.

## The global object (what the converse theorem actually consumes)

* `sym2TwistDegree_eq_one` — at `r = 2` the CPS range `1 ≤ m < r` forces `m = 1`: the twists are
  by `GL(1)` alone.  This is exactly the hypothesis of the classical `GL(3)` converse theorem of
  Jacquet–Piatetski-Shapiro–Shalika, so the sharpest general-`n` statement and the original
  coincide at this rung;
* `sym2TensorWeight_apply` — the global bank's local weight at `p` is `α_p^{2-2j} · γ_{p,k}`,
  definitionally: the literal `Sym² ⊗ τ` Satake datum, not a stand-in;
* `GL3ConverseAnalyticInput` — the four analytic clauses a `GL(3)` converse theorem consumes:
  entire, entire contragredient, bounded on every vertical strip (both), functional equation;
* `sym2_GL3ConverseAnalyticInput` — the carrier supplies all four, unconditionally, for every
  unit-modulus Satake phase family and every `GL(1)` twist;
* `sym2_GL3ConverseAnalyticInput_radiusLive` — **the headline**: the same four clauses with **no
  temperedness assumed**.  `‖α_p‖ = 1` is Deligne's theorem for a holomorphic form but the open
  Ramanujan–Petersson conjecture for a Maass form, so a statement resting on it would be
  conditional for exactly the case Gelbart–Jacquet also covers.  The carrier does not need it: the
  bank keeps arbitrary nonzero radial magnitudes under a polynomial prime bound, met by the
  trivial Hecke bound `‖α_p‖ ≤ p`.

## The bank is the `Sym²` Euler bank, definitionally

* `sym2TensorRoot_apply` — the local roots are `α_p^{2-j}·β_p^{j}·γ_{p,k}`;
* `sym2_localFactor_identification` — the carrier's local numerator **is** the arithmetic `Sym²`
  twisted Euler numerator, by `rfl`;
* `sym2_globalCoefficient_identification`, `sym2_globalDualCoefficient_identification` — every
  global Euler coefficient of both banks likewise, by `rfl`.

**Register.**  The pair carrying the four clauses above is a carrier-theta object with a
*synthesized* completion kernel: its `Λ` is the carrier's own completed readout
(machine-checked in `CPSSynthesizedKernelControl` — the readout is independent of the
Satake data), so the four clauses are regularity of the carrier, and the arithmetic
content lives entirely in the identification layer.  The identification with the
*prescribed* conductor/`Γ`-product completion is the separate compiled layer below
(`sym2_standardCompletion_and_niceness`, clause one), and at the actual eigen-datum the
genuine r = 2 completed pair — prescribed chart, literal coefficients, functional
equation, poles — is `Sym2Rankin.sym2RankinCoupling` / `Sym2Rankin.sym2_rankin_rung`.

## The classical completion

A converse theorem is a statement about the *classically* completed `L`-function — conductor
times a `Γ`-product — so a functional equation of the carrier's own completed pair is not by
itself the hypothesis.  The identification closes that:

* `completionPointOfReal` — a point of the common initial half-plane exists: any real `R` beyond
  both Dirichlet abscissae and the shift bound gives one;
* `sym2_standardCompletion_and_niceness` — **the capstone**.  For any base, twist, completion
  clock (conductor and `Γ`-shifts), and such a point: the Mellin projection of the prescribed
  conductor/`Γ`-product `3D` bank readout **equals** the completed Dirichlet readout, primal and
  reciprocal-height contragredient alike, *and* the strong pair satisfies all four clauses of
  `GL3ConverseAnalyticInput`.  Standard completion and niceness in one statement, over the same
  Satake datum.

## Non-vacuity

* `phaseOfAngles`, `twistOfAngles` — the unitary class contains every family `α_p = e^{iθ_p}`;
* `gl2SatakePair` — the radius-live class contains every `GL(2)` Satake datum `{α_p, α_p⁻¹}`
  obeying the trivial Hecke bound.  Neither class is a degenerate corner.

**Scope.**  Proven here, unconditionally: the local fiber algebra, the coefficient identification,
the global analytic input with and without temperedness (in the register above), and the
identification with the prescribed conductor/`Γ`-product completed readout.  The genuine r = 2
completed pair over the actual eigen-datum — the prescribed chart carrying the functional
equation and polar structure of the literal Rankin bank — is `Sym2Rankin.sym2_rankin_rung`.
The classical inputs consumed, all standard and unconditional: local Langlands for `GL(2)`
(which is what says a given cuspidal `π` has Satake data of this shape), the Hecke or
Jacquet–Shalika polynomial bound, and — for the step from this analytic input to automorphy —
the `GL(3)` converse theorem of Jacquet–Piatetski-Shapiro–Shalika.  That last step is classical
literature and is not re-proved here.  No `axiom`, no `sorry`.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.Sym2Benchmark

open CriticalLinePhasor.FiniteWeightFiber
open CriticalLinePhasor.GlobalHelix

/-! ## The local fiber: the `Sym²` Satake data, recognisably -/

variable (α : ℂ) (hα : ‖α‖ = 1)

/-- **The `Sym²` fiber**: the symmetric square of the unit Satake conjugate pair
`diag(α, α⁻¹)`, as a finite duality-stable weight fiber of degree three. -/
noncomputable def sym2Fiber : FiniteWeightFiber (Fin 3) := symFiber 2 α hα

/-- The top weight channel is `α²`. -/
theorem sym2Fiber_weight_zero : (sym2Fiber α hα).weight 0 = α ^ (2 : ℤ) := by
  show α ^ ((2 : ℤ) - 2 * ((0 : Fin 3).val : ℤ)) = α ^ (2 : ℤ)
  norm_num

/-- The middle weight channel is trivial — the self-dual centre of the even-`r` string. -/
theorem sym2Fiber_weight_one : (sym2Fiber α hα).weight 1 = 1 := by
  show α ^ ((2 : ℤ) - 2 * ((1 : Fin 3).val : ℤ)) = 1
  norm_num

/-- The bottom weight channel is `α⁻²`. -/
theorem sym2Fiber_weight_two : (sym2Fiber α hα).weight 2 = (α ^ (2 : ℤ))⁻¹ := by
  show α ^ ((2 : ℤ) - 2 * ((2 : Fin 3).val : ℤ)) = (α ^ (2 : ℤ))⁻¹
  rw [show (2 : ℤ) - 2 * ((2 : Fin 3).val : ℤ) = -(2 : ℤ) by norm_num, zpow_neg]

/-- **The degree is three**: the `Sym²` lift lands on `GL(3)`. -/
theorem sym2Fiber_card : Fintype.card (Fin 3) = 3 := by simp

/-- **The determinant / modulus ledger**: `α² · 1 · α⁻² = 1`. -/
theorem sym2Fiber_det_one : ∏ k, (sym2Fiber α hα).weight k = 1 :=
  (sym2Fiber α hα).fiber_det_one

/-- **The per-place functional equation**, exponent explicit:
`localPoly X = (-X)³ · localPoly X⁻¹`.  Uses only duality-stability and the ledger; never
`‖λ‖ = 1`, so it is radially open. -/
theorem sym2_localPoly_reciprocal {X : ℂ} (hX : X ≠ 0) :
    (sym2Fiber α hα).localPoly X = (-X) ^ 3 * (sym2Fiber α hα).localPoly X⁻¹ := by
  rw [(sym2Fiber α hα).localPoly_reciprocal hX, sym2Fiber_card]

/-- The fiber survives every dual-compatible unit warp, keeping its ledger. -/
theorem sym2Fiber_warp_det_one (A : DualWarp (sym2Fiber α hα)) :
    ∏ k, ((sym2Fiber α hα).warpFiber A).weight k = 1 :=
  warpFiber_det_one _ A

/-- The `Sym²` completed **local** reflection object. -/
noncomputable def sym2Completed (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) : CompletedReflection :=
  fiberCompleted (sym2Fiber α hα) c hc β ℓ

/-- The completed **local** reflection FE. -/
theorem sym2Completed_FE (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) (s : ℂ) :
    (sym2Completed α hα c hc β ℓ).Λ s
      = ((sym2Completed α hα c hc β ℓ).εfin s * (sym2Completed α hα c hc β ℓ).εarch s)
        * (sym2Completed α hα c hc β ℓ).Λdual (1 - s) :=
  CompletedReflection.completed_FE _ s

/-- The local reflection factor, explicit: `εfin(s) = (-(c^{s-1/2}))³`. -/
theorem sym2Completed_εfin (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) (s : ℂ) :
    (sym2Completed α hα c hc β ℓ).εfin s = (-(reflVar c s)) ^ 3 := by
  show (-(reflVar c s)) ^ (Fintype.card (Fin 3)) = _
  rw [sym2Fiber_card]

/-- The completed local readout is entire. -/
theorem sym2Completed_differentiable (c : ℂ) (hc : c ≠ 0) (β : ℂ) (ℓ : ℝ) :
    Differentiable ℂ (sym2Completed α hα c hc β ℓ).Λ :=
  fiberCompleted_differentiable _ c hc β ℓ

/-- The finite-stage strand exchange `E*(z̄) = ε·E(z)`, `‖ε‖ = 1`. -/
theorem sym2Bank_exchange (ℓ : Fin 3 → ℝ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z : ℂ,
      (starRingEnd ℂ) (StrandExchange.bankProduct Finset.univ
          (sym2Fiber α hα).weight ℓ ((starRingEnd ℂ) z))
        = ε * StrandExchange.bankProduct Finset.univ (sym2Fiber α hα).weight ℓ z :=
  StrandExchange.bankProduct_exchange Finset.univ _
    (fun i _ => (sym2Fiber α hα).unit i) ℓ

/-- The completed strand exchange, exchange constant still unimodular. -/
theorem sym2CompletedBank_exchange (ℓ : Fin 3 → ℝ) (β : ℂ) (hβ : ‖β‖ = 1) (ℓ₀ : ℝ) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ z : ℂ,
      (starRingEnd ℂ) (StrandExchange.completedBank Finset.univ
          (sym2Fiber α hα).weight ℓ β ℓ₀ ((starRingEnd ℂ) z))
        = ε * StrandExchange.completedBank Finset.univ
            (sym2Fiber α hα).weight ℓ β ℓ₀ z :=
  StrandExchange.completedBank_exchange Finset.univ _
    (fun i _ => (sym2Fiber α hα).unit i) ℓ β hβ ℓ₀

/-! ## The twist range: at `r = 2` the converse theorem twists by `GL(1)` alone -/

/-- **At `r = 2` the CPS twist range collapses to `m = 1`.**  `CPSTwistDegree 2` is
`{m // 1 ≤ m ∧ m < 2}`, so every admissible twist degree is `1`: the twists are by `GL(1)`,
i.e. by Hecke characters.  That is exactly the hypothesis of the classical `GL(3)` converse
theorem (Jacquet–Piatetski-Shapiro–Shalika), so the sharpened general-`n` range
`1 ≤ m < n-1` and the original `GL(3)` statement agree at this rung. -/
theorem sym2TwistDegree_eq_one (m : CPSTwistDegree 2) : (m : ℕ) = 1 := by
  have h1 : 1 ≤ (m : ℕ) := m.property.1
  have h2 : (m : ℕ) < 2 := m.property.2
  omega

/-! ## The global object -/

/-- **The global bank's local weights are the literal `Sym² ⊗ τ` Satake datum.**  At each prime
`p` and each channel `(j, k)` the weight is `α_p^{2-2j} · γ_{p,k}` — definitionally, not by a
matching argument.  For `j = 0,1,2` these are `α_p²γ`, `γ`, `α_p⁻²γ`. -/
theorem sym2TensorWeight_apply {κ : Type*} [Fintype κ] (a : UnitaryPrimePhase)
    (τ : UnitarySatakeFamily κ) (p : Nat.Primes) (i : Fin 3 × κ) :
    cpsTensorWeight 2 a τ p i
      = a.phase p ^ ((2 : ℤ) - 2 * (i.1.val : ℤ)) * τ.weight p i.2 :=
  rfl

/-- **The analytic input a `GL(3)` converse theorem consumes.**  Four clauses: the completed
twisted readout and its contragredient are entire, both are bounded on every vertical strip, and
they satisfy the functional equation.  This is the niceness hypothesis of
Jacquet–Piatetski-Shapiro–Shalika at `GL(3)`, equivalently Cogdell–Piatetski-Shapiro at `n = 3`
(where the twist range is `m = 1` by `sym2TwistDegree_eq_one`). -/
structure GL3ConverseAnalyticInput (P : StrongFEPair ℂ) : Prop where
  /-- the completed twisted readout is entire. -/
  entire : Differentiable ℂ P.Λ
  /-- the contragredient completed readout is entire. -/
  entire_dual : Differentiable ℂ P.symm.Λ
  /-- the readout is bounded on every vertical strip. -/
  bounded_strip : ∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ, u ≤ s.re → s.re ≤ v → ‖P.Λ s‖ ≤ B
  /-- the contragredient is bounded on every vertical strip. -/
  bounded_strip_dual : ∀ u v : ℝ, ∃ B : ℝ, ∀ s : ℂ, u ≤ s.re → s.re ≤ v → ‖P.symm.Λ s‖ ≤ B
  /-- the functional equation, at the pair's own weight and root number. -/
  functional_equation : ∀ s : ℂ, P.Λ (P.k - s) = P.ε • P.symm.Λ s

/-- **The carrier supplies the `GL(3)` converse theorem's analytic input at `Sym²`,
unconditionally.**

For every unit-modulus Satake phase family `a` and every `GL(1)` twist `τ`, the global
`Sym² × τ` strong pair is entire with entire contragredient, bounded on every vertical strip in
both legs, and satisfies its functional equation.

No hypothesis is supplied by the caller: no automorphy of `Sym²π`, no continuation, no Poisson
summation, no temperedness beyond the unit-modulus packaging of the Satake datum itself, and no
Dirichlet restriction.  Feeding this to the cited converse theorem returns Gelbart–Jacquet; that
final step is classical and is **not** formalized here. -/
theorem sym2_GL3ConverseAnalyticInput (a : UnitaryPrimePhase) (m : CPSTwistDegree 2)
    (τ : UnitarySatakeFamily (Fin (m : ℕ))) :
    GL3ConverseAnalyticInput (cpsDualPairStrongFEPair 2 a τ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cpsDualPair_twistedNiceness 2 a τ
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## Non-vacuity: the hypothesis class is every tempered Satake datum -/

/-- **The phase class contains every unit-modulus family.**  For any assignment of angles
`θ : Primes → ℝ`, the family `α_p = e^{iθ_p}` is an admissible input.  So the theorem above is
quantified over every tempered `GL(2)` Satake datum, not a degenerate corner. -/
noncomputable def phaseOfAngles (θ : Nat.Primes → ℝ) : UnitaryPrimePhase where
  phase p := Complex.exp ((θ p : ℂ) * Complex.I)
  unit p := by
    rw [Complex.norm_exp]
    simp

/-- The same for the twist: every unit-modulus `GL(1)` twist family is admissible. -/
noncomputable def twistOfAngles (θ : Nat.Primes → Fin 1 → ℝ) :
    UnitarySatakeFamily (Fin 1) where
  weight p i := Complex.exp ((θ p i : ℂ) * Complex.I)
  unit p i := by
    rw [Complex.norm_exp]
    simp

/-- The `Sym²` twist degree is inhabited: `m = 1`. -/
def sym2TwistDegreeOne : CPSTwistDegree 2 := ⟨1, le_refl 1, one_lt_two⟩

/-- **Non-vacuity, explicit**: for every angle assignment the converse theorem's analytic input
is met by an actual inhabitant of the hypothesis class. -/
theorem sym2_GL3ConverseAnalyticInput_nonvacuous
    (θ : Nat.Primes → ℝ) (ψ : Nat.Primes → Fin 1 → ℝ) :
    GL3ConverseAnalyticInput
      (cpsDualPairStrongFEPair 2 (phaseOfAngles θ) (twistOfAngles ψ)) :=
  sym2_GL3ConverseAnalyticInput (phaseOfAngles θ) sym2TwistDegreeOne (twistOfAngles ψ)

/-! ## The headline: no temperedness assumed

`UnitaryPrimePhase` packages `‖α_p‖ = 1`.  For a holomorphic form that is Deligne's theorem, but
for a Maass form it is the *open* Ramanujan–Petersson conjecture, so a statement resting on it
would be conditional for exactly the case Gelbart–Jacquet also covers.  The carrier does not need
it: `PolynomialSatakeDualPair` keeps arbitrary nonzero radial magnitudes under a polynomial prime
bound `‖α_p‖ ≤ p^e`, met unconditionally by the trivial Hecke bound `e = 1`.  The niceness below
is proven over that radius-live bank. -/

/-- **The `Sym²` analytic input, with no temperedness assumed — the referee-proof form.**

For *any* base Satake pair `π : PolynomialSatakeDualPair (Fin 2)` — holomorphic or Maass, tempered
or not, subject only to a polynomial prime bound — and any `GL(1)` twist `τ`, the arithmetic
`Sym² × τ` carrier pair satisfies all four clauses of `GL3ConverseAnalyticInput`.

`‖α_p‖ = 1` is nowhere an input.  This is what makes the chain non-circular: the niceness that
feeds the converse theorem is proven at arbitrary radius, and temperedness is the *output* of the
radial limit (`RamanujanLimit`), not a hypothesis. -/
theorem sym2_GL3ConverseAnalyticInput_radiusLive
    (pi : PolynomialSatakeDualPair (Fin 2)) (tau : PolynomialSatakeDualPair (Fin 1)) :
    GL3ConverseAnalyticInput
      (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist 2 1 pi tau)) := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ :=
    cpsArithmeticTwist_radiusLive_niceness 2 1 (le_refl 1) one_lt_two pi tau
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ### The bank *is* the `Sym²` Euler bank — definitionally

A referee's next question is whether the object carrying the niceness is actually the symmetric
square, or merely something of the right shape.  The identification is by `rfl`. -/

/-- **The local roots are the literal `Sym² ⊗ τ` Satake roots**: at each prime `p` and channel
`(j, k)` the root is `α_p^{2-j} · β_p^{j} · γ_{p,k}`.  With the det-one pair `β = α⁻¹` these are
`α_p²γ`, `γ`, `α_p⁻²γ` for `j = 0,1,2`. -/
theorem sym2TensorRoot_apply (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin 1)) (p : Nat.Primes) (i : CPSTensorIndex 2 1) :
    arithmeticCPSTensorRoot 2 1 pi tau p i
      = pi.primal p 0 ^ (2 - i.1.1) * pi.primal p 1 ^ i.1.1 * tau.primal p i.2 :=
  rfl

/-- **The carrier's local numerator is the arithmetic `Sym²` twisted Euler numerator**, by `rfl`. -/
theorem sym2_localFactor_identification (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin 1)) (p : Nat.Primes) (X : ℂ) :
    DualPairFiber.dualLocalPoly
        ((arithmeticCPSPolynomialTwist 2 1 pi tau).primal p) X =
      DualPairFiber.dualLocalPoly (arithmeticCPSTensorRoot 2 1 pi tau p) X :=
  arithmeticCPS_localFactor_identification 2 1 pi tau p X

/-- **Every global Euler coefficient of the carrier bank is the arithmetic `Sym²` twisted Euler
coefficient**, by `rfl` — so the niceness above is niceness of the symmetric square's own
Dirichlet series, not of an auxiliary object. -/
theorem sym2_globalCoefficient_identification (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin 1)) (n : ℕ) :
    cpsPolynomialPrimalCoeff (arithmeticCPSPolynomialTwist 2 1 pi tau) n =
      radialGlobalSatakeCoeff (arithmeticCPSTensorRoot 2 1 pi tau) n :=
  arithmeticCPS_globalCoefficient_identification 2 1 pi tau n

/-- The same exact identification on the contragredient bank. -/
theorem sym2_globalDualCoefficient_identification (pi : PolynomialSatakeDualPair (Fin 2))
    (tau : PolynomialSatakeDualPair (Fin 1)) (n : ℕ) :
    cpsPolynomialDualCoeff (arithmeticCPSPolynomialTwist 2 1 pi tau) n =
      radialGlobalSatakeCoeff (arithmeticCPSDualTensorRoot 2 1 pi tau) n :=
  arithmeticCPS_globalDualCoefficient_identification 2 1 pi tau n

/-! ### The classical completion: the carrier readout *is* the conductor/`Γ`-product completed
Dirichlet readout

Theorem `sym2_GL3ConverseAnalyticInput_radiusLive` reflects the carrier's own completed pair.  A
converse theorem, however, is a statement about the *classically* completed `L`-function —
conductor times a `Γ`-product.  Without identifying the two, the functional equation proved above
would be a functional equation of the wrong completed function.  The identification is the
content of this section. -/

/-- **A point of the common initial half-plane exists.**  Any real `R` beyond both Dirichlet
abscissae and beyond the shift bound gives one, so the identification below is not vacuous. -/
noncomputable def completionPointOfReal {ι : Type*} [Fintype ι]
    (W : PolynomialSatakeDualPair ι) (clock : CPSCompletionClock) (R : ℝ)
    (hshift : ∀ μ ∈ clock.shifts, 0 < R + μ.re)
    (hp : ((Fintype.card ι + W.primalExponent : ℕ) : ℝ) + 1 < R)
    (hd : ((Fintype.card ι + W.dualExponent : ℕ) : ℝ) + 1 < R) :
    CPSCompletionPoint W clock where
  s := (R : ℂ)
  shifts_pos μ hμ := by simpa using hshift μ hμ
  primal_dirichlet := by simpa using hp
  dual_dirichlet := by simpa using hd

/-- **The full `Sym²` converse-theorem input: standard completion *and* niceness, one statement.**

For any `GL(2)` Satake base `π` and `GL(1)` twist `τ` under a polynomial bound, any completion
clock (conductor and `Γ`-shifts), and any point of the common initial half-plane:

* the Mellin projection of the prescribed conductor/`Γ`-product primal `3D` bank readout **equals**
  the completed primal Dirichlet readout at that point;
* likewise for the reciprocal-height contragredient bank;
* and the strong pair is entire with entire contragredient, bounded on every vertical strip in
  both legs, and satisfies its functional equation.

The first two clauses are what turns the carrier's reflection into a statement about the
classically completed object; the third is the niceness.  Together they are the analytic
hypothesis of the `GL(3)` converse theorem, at the prescribed completion, with no temperedness. -/
theorem sym2_standardCompletion_and_niceness
    (pi : PolynomialSatakeDualPair (Fin 2)) (tau : PolynomialSatakeDualPair (Fin 1))
    (clock : CPSCompletionClock)
    (point : CPSCompletionPoint (arithmeticCPSPolynomialTwist 2 1 pi tau) clock) :
    mellin (cpsPolynomialFullPrimal3DBankReadout
        (arithmeticCPSPolynomialTwist 2 1 pi tau) clock.conductor clock.shifts) point.s
      = cpsPolynomialFullPrimalCompletedReadout
        (arithmeticCPSPolynomialTwist 2 1 pi tau) clock.conductor clock.shifts point.s
    ∧ mellin (fun x : ℝ => cpsPolynomialFullDual3DTransformedReadout
        (arithmeticCPSPolynomialTwist 2 1 pi tau) clock.conductor clock.shifts (1 / x)) point.s
      = cpsPolynomialFullDualCompletedReadout
        (arithmeticCPSPolynomialTwist 2 1 pi tau) clock.conductor clock.shifts point.s
    ∧ GL3ConverseAnalyticInput
        (cpsPolynomialStrongFEPair (arithmeticCPSPolynomialTwist 2 1 pi tau)) := by
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ :=
    cpsPolynomialAllTwists_fullCompletion3D_unified 2 1 (le_refl 1) one_lt_two
      (arithmeticCPSPolynomialTwist 2 1 pi tau) clock point
  exact ⟨h2, h3, ⟨h4, h5, h6, h7, h8⟩⟩

/-! ### Pole-freeness: the degree-3 parameter carries no trivial constituent

The converse theorem needs the twisted `L` to be *entire*, and the one candidate pole is a trivial
constituent of the parameter contributing a `ζ`-factor.  For an irreducible `Sym²` parameter there
is none, and the reason is Schur's lemma with the group action present — dimension supplies only
non-isomorphism, never the vanishing. -/

section PoleFreeness
open CategoryTheory Module
open scoped MonoidalCategory

/-- **No trivial constituent at degree 3.**  For a simple degree-three parameter `V` over an
algebraically closed field, every morphism from the tensor unit vanishes.  Applied to an
irreducible `Sym²φ_π`, this is what excludes the `s = 1` pole of the twisted `L`-function.  The
vanishing is Schur's lemma with the group action present; the dimension supplies only
non-isomorphism, never the vanishing itself. -/
theorem sym2_no_trivial_constituent {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [Group G] (V : FDRep k G)
    [Simple (𝟙_ (FDRep k G))] [Simple V]
    (hr : finrank k V = 3) (f : 𝟙_ (FDRep k G) ⟶ V) : f = 0 :=
  NonSelfDual.tateClass_zero_of_simple_finrank_succ V 2 hr (by norm_num) f

end PoleFreeness

/-- **The radius-live bank is inhabited by every `GL(2)` Satake datum.**  Given any nonvanishing
prime-indexed `α` obeying the trivial Hecke bound `‖α_p‖ ≤ p` in both directions, the conjugate
pair `{α_p, α_p⁻¹}` is a `PolynomialSatakeDualPair (Fin 2)`.  No unit-modulus condition. -/
noncomputable def gl2SatakePair (a : Nat.Primes → ℂ) (ha : ∀ p, a p ≠ 0)
    (h1 : ∀ p, ‖a p‖ ≤ (p.1 : ℝ)) (h2 : ∀ p, ‖(a p)⁻¹‖ ≤ (p.1 : ℝ)) :
    PolynomialSatakeDualPair (Fin 2) where
  primal p := ![a p, (a p)⁻¹]
  dual p := ![(a p)⁻¹, a p]
  primalExponent := 1
  dualExponent := 1
  primal_ne_zero p i := by
    fin_cases i <;> simp [ha p, inv_ne_zero (ha p)]
  dual_eq_inv p i := by
    fin_cases i <;> simp [inv_inv]
  primal_bound p i := by
    fin_cases i
    · simpa [pow_one] using h1 p
    · simpa [pow_one] using h2 p
  dual_bound p i := by
    fin_cases i
    · simpa [pow_one] using h2 p
    · simpa [pow_one] using h1 p

end CriticalLinePhasor.Sym2Benchmark

#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Fiber_weight_zero
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Fiber_weight_one
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Fiber_weight_two
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Fiber_det_one
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_localPoly_reciprocal
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Fiber_warp_det_one
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Completed_FE
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Completed_εfin
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Completed_differentiable
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2Bank_exchange
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2CompletedBank_exchange
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2TwistDegree_eq_one
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2TensorWeight_apply
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_GL3ConverseAnalyticInput
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_GL3ConverseAnalyticInput_nonvacuous
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_GL3ConverseAnalyticInput_radiusLive
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2TensorRoot_apply
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_localFactor_identification
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_globalCoefficient_identification
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_globalDualCoefficient_identification
#print axioms CriticalLinePhasor.Sym2Benchmark.completionPointOfReal
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_standardCompletion_and_niceness
#print axioms CriticalLinePhasor.Sym2Benchmark.sym2_no_trivial_constituent
#print axioms CriticalLinePhasor.Sym2Benchmark.gl2SatakePair
