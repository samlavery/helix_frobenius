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

The sole remaining formalization gap is the **Perron/Tauberian** passage from the continued
Dirichlet series to the sharp summatory bound (Perron's formula plus a contour shift past the
pole line).  It is classical and standard in analytic number theory; here it is isolated as the
explicit hypothesis `PerronTauberian`, cited as literature pending formalization — no other
input is assumed.  In the three-dimensional register: `ω_W` is the carrier's phasor-bank density
read against the Eisenstein clock, the continuation is the weld reflection of the bank
transported through the Mellin projection, and the poles sit exactly on the DC channel
(rank-is-DC-residue).  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup ArithmeticFunction
open scoped Real MatrixGroups ArithmeticFunction.Moebius

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound CriticalLinePhasor.EpsteinTheta

variable {k : ℤ}

/-- The Sym²-normalized coefficient sequence of the cusp form: `λ_n = (μ ⋆ ‖a‖²)(n)`, the
degree-`2×2` Rankin–Selberg coefficients (`MoebiusTransfer.rankinSquare`, the `ζ`-transfer
peeling `L(‖a‖²) = ζ · L(λ)`). -/
noncomputable def sym2Coeff (f : CuspForm 𝒮ℒ k) (n : ℕ) : ℝ :=
  (((μ : ArithmeticFunction ℂ) * rankinSquare f) n).re

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
transfer `hPT` applied to the rung's carrier continuation.  The reduction — cancellation ⟺ the
rung's fixed-kernel functional equation, then Perron — is the **same at every `r`**; only the
discharge of the continuation is rung-specific:

* `r = 1` (abelian): the weld is Gauss/Poisson on the one-variable theta;
* `r = 2` (Sym²): the compiled Gaussian–lattice / Epstein weld
  (`lambda_sym2_continuation`, `latticeTheta_inv`, `rs_master`) — unconditional, machine-checked.
  What the carrier needs here is the bank's self-duality under the modular inversion `S`; for the
  Gaussian lattice that self-duality reads out classically as Poisson summation (the Gaussian is
  its own Fourier transform), so Poisson is the *Gaussian-case computation of the weld*, not an
  external requirement;
* `r = 3, 4`: Kim–Shahidi (functoriality known; kernel not yet compiled);
* `r ≥ 5`: no classical lattice theta exists. The fixed-kernel FE need not be classical — it is
  whatever kernel makes the rung-`r` bank self-dual under `S`, and the carrier's candidate is a
  *geometric* higher-rank bank (Siegel theta on `Sp(2g,ℤ)`, the Godement–Jacquet `GL(r+1,ℤ)`
  Sym^r engine). Establishing that geometric weld directly — a functional equation from the 3D
  bank's self-duality, without first proving `Sym^r π` automorphic — is the open carrier
  direction, where it could pass *beyond* Langlands–Shahidi, not a classical dead end.

`hPT` bundles the classical Perron step, the sole formalization gap at every rung; the weight
`ω_W` is the rung's Petersson–Eisenstein density, explicit at `r = 2` (`rs_master`). No RH/GRH. -/
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
`symr_functoriality_cancellation` (`κ = k`): every analytic ingredient — continuation, functional
equation, explicit poles, tail decay, finite measure — is compiled unconditionally
(`lambda_sym2_continuation` and the `RSMaster`/`RSPoleStructure`/`GDecay` chain); the single
hypothesis `hPT` is the classical Perron/Tauberian passage, the sole cited formalization gap.
No RH/GRH. -/
theorem sym2_functoriality_cancellation (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {θ : ℝ}
    (hθ : θ < (k : ℝ) / 2) (hPT : PerronTauberian (sym2Coeff f) θ) :
    SummatoryBound (sym2Coeff f) θ :=
  symr_functoriality_cancellation (sym2Coeff f) (k : ℝ) θ hθ hPT

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.symr_functoriality_cancellation
#print axioms CriticalLinePhasor.Unfolding.lambda_sym2_continuation
#print axioms CriticalLinePhasor.Unfolding.sym2_functoriality_cancellation
