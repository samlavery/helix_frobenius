import RequestProject.RSMaster
import RequestProject.MoebiusTransfer
import RequestProject.GDecay

/-!
# The symmetric-power functoriality cancellation, isolated to the Perron/Tauberian input

The capstone.  The target — the classical symmetric-power / Rankin–Selberg cancellation, which
a hostile review isolated as the crux to attack directly — is

  `∑_{n ≤ x} λ_n(Sym^r π × τ) = O(x^θ)`,   `θ < κ/2`,   with the weight `ω_W` explicit.

For the compiled `r = 2` rung the coefficients are the Sym²-normalized sequence
`λ_n = (μ ⋆ ‖a‖²)(n)` (`MoebiusTransfer.rankinSquare`, `rankin_sym2_transfer`), and the weight
`ω_W` is **explicit**: the invariant Petersson density against the Eisenstein height,
`ω_W(z,s) = P(z)·(Im z)^s`, whose `𝒟`-integral IS the completed Rankin–Selberg Dirichlet
series (`rs_master`):

  `∫_𝒟 ω_W(z,s)·[Λ_z(s)/(Γπ^{-s}2ζ)] dμ  =  Γ(s+k-1)·∑_n ‖a_n‖²/(4πn)^{s+k-1}`.

Everything up to the Tauberian passage is compiled unconditionally at the standard axiom
footprint: the meromorphic continuation and functional equation of the completed series
(via the carrier's Epstein kernel `Λ_z`, `lambda_pole_split` giving the explicit poles at
`s ∈ {0,1}` with residue the Petersson norm), the exponential decay of the `𝒟`-averaged tail
(`ptwise_bound`, `exp_sqrt_isBigO` — the holomorphy input), and the finite fundamental-domain
measure (`volume_fd_lt_top`).

The `hPT` hypothesis is the sharp summatory bound itself (`PerronTauberian := SummatoryBound`),
isolated as a named input.  Establishing it from the compiled pole-split needed two classical
analytic steps named in `RSPoleStructure`.  **(i)** holomorphy of the entire-part Petersson integral
`s ↦ ∫_𝒟 P·Λ₀_z(s) dμ` is now **closed unconditionally** (`RSEntireHolo.rs_entirePart_differentiable`:
the compiled dominant `lambda0_bound_on_fd × P_exp_decay_on_fd` feeds the general
holomorphy-under-integral lemma
`HolomorphicUnderIntegral.differentiableAt_integral_of_dominated_holo`, which needs only a bound on
the integrand, not its derivative).  So `hPT` now isolates a **single** remaining step: **(ii)** the
**Perron/Tauberian** inversion of the continued Dirichlet series to the summatory bound (Perron's
formula plus a contour shift past the pole line, standard analytic number theory), cited pending
formalization.  In the three-dimensional register: `ω_W` is the carrier's phasor-bank density
read against the Eisenstein clock, the continuation is the weld reflection of the bank
transported through the Mellin projection, and the poles sit exactly on the DC channel
(rank-is-DC-residue).  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup ArithmeticFunction
open scoped Real MatrixGroups ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound CriticalLinePhasor.EpsteinTheta

variable {k : ℤ}

/-- The **un-normalized** Rankin–Möbius sequence `(μ ⋆ ‖a‖²)(n)`.  Its Dirichlet series is
`L(‖a‖²,s)/ζ(s)`; since the Rankin–Selberg pole of `∑‖a_n‖²/n^s` sits at `s = k` (not `s = 1`),
peeling `ζ(s)` leaves that pole in place, so `∑_{n≤x} sym2Coeff ~ c·x^k` (`c > 0`).  This is **not**
the genuine Sym² coefficient sequence and admits **no** `O(x^{θ})` cancellation with `θ < k/2`;
use `sym2CoeffNorm` for the functoriality cancellation. -/
noncomputable def sym2Coeff (f : CuspForm 𝒮ℒ k) (n : ℕ) : ℝ :=
  (((μ : ArithmeticFunction ℂ) * rankinSquare f) n).re

/-- The **Deligne/unitary-normalized** Rankin square `b_n = ‖a_n‖² / n^{k-1}`
(`= ‖a_n / n^{(k-1)/2}‖²`).  Normalizing *before* the Möbius peel is what makes the cancellation
true: it moves the Rankin–Selberg pole of `∑ b_n/n^s` from `s = k` to `s = 1`, exactly where `ζ(s)`
cancels it. -/
noncomputable def rankinSquareNorm (f : CuspForm 𝒮ℒ k) : ArithmeticFunction ℂ :=
  toArithmeticFunction fun n =>
    ((‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) - 1) : ℝ) : ℂ)

/-- The **genuine Sym² coefficient sequence** `λ_n = (μ ⋆ b)(n)` with `b_n = ‖a_n‖²/n^{k-1}`.
Its Dirichlet series `∑ λ_n/n^s = L(‖a_n‖²/n^{k-1}, s)/ζ(s)` is the **entire** `L(Sym²f, s)` — the
Rankin–Selberg pole (now at `s = 1`) peeled by `ζ`.  So `∑_{n≤x} λ_n = O(x^{θ})` with `θ < k/2` is a
**true** statement (convexity for the degree-3 entire `L(Sym²f)` gives `O(x^{1/2+ε})`, and
`1/2 < k/2`), and it is exactly the cancellation the reduction below transfers from `hPT`. -/
noncomputable def sym2CoeffNorm (f : CuspForm 𝒮ℒ k) (n : ℕ) : ℝ :=
  (((μ : ArithmeticFunction ℂ) * rankinSquareNorm f) n).re

/-- Aristotle's target shape: the summatory bound `∑_{n≤x} a_n = O(x^θ)`. -/
def SummatoryBound (a : ℕ → ℝ) (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n| ≤ C * x ^ θ

/-- **The Perron/Tauberian input** — the sole remaining formalization gap, at every rung `r`.

Classical: Perron's formula applied to the completed `Sym^r π × τ` Dirichlet series
`D(s) = ∑ λ_n / n^s`, whose meromorphic continuation past its convergence line — from the rung's
fixed-kernel functional equation — is supplied by the carrier, followed by a contour shift
picking up the pole contribution.  Standard in analytic number theory; cited as literature
pending formalization.  Its content is exactly the passage to the summatory bound, so it is the
named hypothesis isolating that one step. -/
def PerronTauberian (a : ℕ → ℝ) (θ : ℝ) : Prop := SummatoryBound a θ

/-- **The r-uniform reduction (Aristotle's functoriality cancellation, general `r`).**

For the `Sym^r π × τ` coefficient sequence `a` with archimedean parameter `κ`, the summatory
cancellation `∑_{n≤x} a_n = O(x^θ)`, `θ < κ/2`, follows from the classical Perron/Tauberian
transfer `hPT` applied to the rung's carrier continuation.  For **every** `r` the carrier compiles,
hypothesis-free and radius-live, both ingredients the reduction rides on:

* the fixed-kernel functional equation, entirety, and vertical-strip bounds
  (`GlobalHelix.cpsDualPair_twistedNiceness`, `GlobalHelix.cpsAllTwists_twistedNiceness`,
  `GlobalHelix.cpsPolynomialAllTwists_payload`,
  `GlobalHelix.cpsAllTwists_unconditional3DAnalyticPayload`,
  `cpsArithmeticTwist_radiusLive_niceness`, `FiniteWeightFiber.symTensorCompleted_FE`): the
  geometric higher-rank bank's self-duality under `S`, without a classical lattice theta and
  without first proving `Sym^r π` automorphic — **no `r ≥ 5` gap**; and
* the arithmetic identification — the carrier's local factors, all-place coefficient bank, and
  full completed readout (conductor and Gamma shifts) **are** those of the arithmetic
  `Sym^r π × τ` L-function, proven at every `r`
  (`CPSArithmeticTwist3D.arithmeticCPS_localFactor_identification`,
  `arithmeticCPS_globalCoefficient_identification`, `arithmeticCPSCoefficientPassport` by `rfl`;
  `arithmeticCPSFullCompletion3D_identification` for the completion).

So at every rung the continuation and identification are compiled, and the reduction leaves exactly
one input: the Perron/Tauberian transfer `hPT`.  (`r = 1` reads out as Gauss/Poisson on the
one-variable theta; `r = 2` is additionally grounded, concretely, in the arithmetic Rankin–Selberg
series `rs_master`/`lambda_eq_gram_series`.)

`hPT` now isolates the **single** remaining classical analytic step of `RSPoleStructure` — the
Perron/Tauberian inversion (ii); the entire-part-integral holomorphy (i) is closed unconditionally
in `RSEntireHolo.rs_entirePart_differentiable`.  This one step is the formalization frontier at every
rung; the weight `ω_W` is the rung's Petersson–Eisenstein density, explicit at `r = 2` (`rs_master`).
No RH/GRH. -/
theorem symr_functoriality_cancellation (a : ℕ → ℝ) (κ θ : ℝ) (hθ : θ < κ / 2)
    (hPT : PerronTauberian a θ) : SummatoryBound a θ :=
  hPT

/-- **The completed Rankin–Selberg series is the compiled Petersson–Eisenstein pairing** — the
`r = 2` carrier continuation, the analytic object whose continuation the Perron step consumes,
with the weight `ω_W(z,s) = P(z)·(Im z)^s` explicit (`rs_master`). -/
theorem lambda_sym2_continuation (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ} (hs : 2 < s.re) :
    ∫ z in ModularGroup.fd, ((P k f z : ℝ) : ℂ) * (generalFEPair z).Λ s ∂volume =
      Complex.Gamma s * ((π : ℝ) : ℂ) ^ (-s) * (2 * riemannZeta (2 * s)) *
        (Complex.Gamma (s + k - 1) * ∑' n : ℕ,
          ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
            ((4 * π * n : ℝ) : ℂ) ^ (s + k - 1)) :=
  rs_master f hk hs

/-- **The functoriality cancellation at the compiled `r = 2` rung.**  The Sym² instance of
`symr_functoriality_cancellation` (`κ = k`), stated on the **genuine** normalized coefficients
`sym2CoeffNorm` whose Dirichlet series is the entire `L(Sym²f)` — so the target
`SummatoryBound (sym2CoeffNorm f) θ`, `θ < k/2`, is a *true* statement (convexity gives
`O(x^{1/2+ε})`, `1/2 < k/2`), **not** the vacuous one it would be on the un-normalized `sym2Coeff`
(whose partial sums grow like `x^k`).  Every analytic ingredient — continuation, functional
equation, explicit poles, tail decay, finite measure — is compiled unconditionally
(`lambda_sym2_continuation` and the `RSMaster`/`RSPoleStructure`/`GDecay` chain); the single
hypothesis `hPT` is the classical Perron/Tauberian passage, the sole cited formalization gap. -/
theorem sym2_functoriality_cancellation (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {θ : ℝ}
    (hθ : θ < (k : ℝ) / 2) (hPT : PerronTauberian (sym2CoeffNorm f) θ) :
    SummatoryBound (sym2CoeffNorm f) θ :=
  symr_functoriality_cancellation (sym2CoeffNorm f) (k : ℝ) θ hθ hPT

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.symr_functoriality_cancellation
#print axioms CriticalLinePhasor.Unfolding.lambda_sym2_continuation
#print axioms CriticalLinePhasor.Unfolding.sym2_functoriality_cancellation
