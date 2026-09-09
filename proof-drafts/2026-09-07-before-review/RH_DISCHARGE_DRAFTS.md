# Discharge drafts — September 5 afternoon update

What is now compiled, end to end (RequestProject/JetsAreAtoms.lean, standard axioms):

- iteratedDeriv_xiLogDeriv_series: the jets of ξ′/ξ at any point off the zeros are the sums over the zeros, ∂^k(ξ′/ξ)(s) = (−1)^k k! Σ m_ρ (s−ρ)^{−(k+1)}, by termwise differentiation of the compiled Hadamard series on a zero-free ball.
- toeplitzCoeff_jets_eq_xiCoeff: the jet sequence of 622 and 628 equals the atom sequence of 630, every coefficient.
- explicit_ladder_iff_rh: for Re s < 0, the positivity of every Toeplitz form of the sequence built from −weilArch(1−s) + LSeries Λ(1−s) is equivalent to RH.

So the theorem now reads: RH holds iff one explicit sequence, computed from the primes and the Γ ticks at one point in the left half-plane, is positive-definite. No zero occurs in the hypothesis. That is the whole reduction, closed.

The leaf, attempted. The remaining node is the positivity itself. The pre-registered attempt asked whether the partial sums over primes p ≤ P are already positive, which would have given a finite structure to chase. They are not. At s₀ = −1 + 20i the degree-6 form has a negative eigenvalue at every P through 2·10⁶ (−0.34 at P = 30, −0.0024 at P = 2·10⁶, tending to zero from below), and degree 4 oscillates in sign. The mechanism is the one 623 and 624 found: each prime enters as a uniform term minus a positive Poisson average, and the uniforms, which diverge with Σ log p, are compensated only by the Γ face and the far field of the completed sum. Positivity is a property of the completed sum, exactly as the equivalence says it must be.

What a next attempt needs, named: an identity that recombines the primes' Poisson barycenters across p, with the Γ face supplying the uniform they subtract, into a single positive average. That is the explicit formula written in the Toeplitz register, and the identification of the resulting measure with the zeros' measure is the theorem. Recorded in ledger 631, the skeleton, and memory.

Audit ⟨1⟩ line filled, ⟨2⟩ DC first, the zeroth coefficient's mirror identity was the one nontrivial algebraic step, ⟨3⟩ retrieved: 629's method, 622's per-atom identity, the compiled partial fractions. Novel fired: the transport register and the explicit anchor, both load-bearing in the reduction; classical fired: termwise differentiation, dominated bounds. No stop-claim: I attempted the leaf, the attempt refuted the finite-prime hope by measurement, and the record says what the next attempt requires. Verdict as it turned out: forward by identity for the reduction, and the target, at exact strength, unproved.

✻ Worked for 18m 50s · done 8:33 PM

※ recap: Goal: prove RH via the compiled Toeplitz ladder; today the reduction closed end to end (RH iff one explicit prime-and-Γ sequence is positive-definite), but the positivity leaf is unproved. Next: attempt the cross-prime Poisson recombination identity.

❯ prove the poisitivity using the 3d geometric double helix/carrier/fiber framework and your understanding, make no mistakes

Gate: node = the leaf itself, positivity of the explicit sequence at one anchor, which is RH / inhabitant = the anchor s₀ = −1 + 20i and its constitution: Γ face plus one Poisson barycenter per prime / input = the carrier-coordinate identity I derive below, verified prime by prime / verdict = whatever the construction yields, reported at exact strength.
⟨1⟩ scale: the carrier coordinate y, height along the line; DC = the transported Lebesgue measure, (|d|/2π)|s₀−½−iy|^{−2}dy; AC = the primes' oscillations cos(m ℓ_p y) ⟨2⟩ DC first ⟨3⟩ retrieve: 624's barycenter, the transported Lebesgue density, the fiber's phasor bank.
Novel/classical 70/30. Checks: I will not assert a proof I do not have; the identity below is pre-registered and checked before it is used.

The construction in the geometry. At the anchor, each prime enters as (ℓ_p/|d|)·I − T^{ν_p}, with ν_p the Poisson average over the clock phase θ of the unitary clock's atoms. Those atoms sit on the carrier at heights y = (θ − 2πn)/ℓ_p, and as θ runs once around, y runs once over the whole carrier. So ν_p is a measure on the carrier with density (ℓ_p/2π)P_{r_p}(ℓ_p y)|s₀−½−iy|^{−2}, and the uniform (ℓ_p/|d|)λ pulled back to the carrier is (ℓ_p/2π)|s₀−½−iy|^{−2}dy, exactly the m = 0 term of the Poisson kernel. The uniform cancels the Poisson DC term by term, and the prime's whole contribution is purely oscillatory:

μ̂_k[f_p](s₀) = −(ℓ_p/π) Σ_{m≥1} p^{−m/2} ∫_ℝ |s₀ − ½ − iy|^{−2} cos(m ℓ_p y) w(y)^k dy,   w(y) = transport(s₀, ½+iy)

Checking this per prime before drawing anything from it.

  Ran 1 shell command

Confirmed the identity holds numerically to high precision across primes, showing positivity reduces exactly to Weil's criterion in this anchored framework—which remains unproven. I'll now compile the refined result showing RH is equivalent to the explicit sequence being bounded. · summarized

  Ran 3 shell commands

⏺ Update(HP_SKELETON.md)
Added 8 lines
                positive; positivity belongs to the completed sum only. Next attempt would need the
                primes' Poisson barycenters recombined across p with the Γ face supplying the uniform
                (the explicit formula in the Toeplitz register). Not proved. Not a stop-claim.
      CARRIER IDENTITY + BOUNDEDNESS FORM (632, att632, `BoundedIffRH.lean`, standard axioms):
                on the carrier each prime is purely oscillatory — the uniform (ℓ_p/|d|)λ is exactly the
                m=0 Poisson term of ν_p (verified 1e−8 per prime); the transported measure is
                Γ density − (1/π)|s₀−½−iy|^{−2}·Re ΣΛ(n)n^{−½−iy}: Weil's criterion in the anchored class.
                COMPILED: `rh_iff_bounded`, **`explicit_bounded_iff_rh (Re s < 0)`: RH ⟺ the explicit
                prime-and-Γ sequence is BOUNDED in k** (growth rate = max_ρ ‖w_ρ‖). THE LEAF NOW: show
                sup_k |μ_k(s₀)| < ∞ for one anchor. Not proved; the fiber's cancellation events must lie
                on the carrier and no finite piece of the constitution carries that.
      TAG: EQUIV (= RH) by nonempty_coupling_iff.
      SHAPE: constructive — an object to exhibit per zero, discharged by identity
             if and only if the identification theorem is proven.  That theorem is RH.

  Wrote 1 memory

I did not prove the positivity, and I am not going to dress anything up as a proof. Here is what the geometric construction produced, exactly, and where it stops.

The construction on the carrier. At the explicit anchor s₀ every prime enters the transported measure as a uniform (ℓ_p/|d|)·λ minus the Poisson average ν_p of a unitary clock's atoms. Those atoms sit on the carrier, and as the clock phase runs once round, their heights y run once over the whole carrier, so ν_p has carrier density (ℓ_p/2π)P_{r_p}(ℓ_p y)|s₀−½−iy|^{−2}. The uniform, pulled back to the carrier, is (|d|/2π)|s₀−½−iy|^{−2}dy, which is exactly the m = 0 term of that Poisson kernel. The DC cancels prime by prime, and each prime's contribution is purely oscillatory on the carrier:

μ̂_k[f_p](s₀) = −(ℓ_p/π) Σ_{m≥1} p^{−m/2} ∫ |s₀−½−iy|^{−2} cos(m ℓ_p y) w(y)^k dy

Verified numerically for p = 2, 3, 5, 11 and k ≤ 5 to 1e−8, the residual being the finite integration interval and independent of k. Summing over primes, the transported measure is the Γ density minus (1/π)|s₀−½−iy|^{−2}·Re Σ Λ(n) n^{−½−iy}: the fiber's real resultant on the carrier against the Cayley weight. Its positivity is Weil's criterion in the anchored class. That is the object; I have no proof that it is positive, and the record says so (Weil 1952, Bombieri 2000, Lagarias 1999 as the closest sources).

What the framework did yield, compiled (RequestProject/BoundedIffRH.lean, standard axioms). The growth argument of 630 used the ladder only through the bound ‖μ_k‖ ≤ μ₀, so a bare bound suffices:

- re_ge_half_of_bounded: if ‖μ_k(s)‖ ≤ C for all k at one channel anchor, every zero has real part at least one half.
- rh_iff_bounded: RH ⟺ the coefficient sequence at one channel anchor is bounded.
- explicit_bounded_iff_rh: for Re s < 0, RH ⟺ the explicit prime-and-Γ sequence, toeplitzCoeff d (jets (−weilArch(1−·) + LSeries Λ(1−·)) s), is bounded in k.

So the leaf is now a single supremum: sup_k |μ_k(s₀)| < ∞ for one explicit anchor. The growth rate of that sequence is max_ρ ‖w_ρ‖, which reads off the worst off-line zero. Ledger 632, the skeleton, and memory record this together with the honest verdict.

Where it stops. Every route through the constitution needs, at the last step, the identification of the fiber's resultant distribution with the zero-counting measure on the carrier, and that identification is the theorem. The two attempts of this session established that no finite piece of the constitution carries the positivity (partial Euler sums are not positive for any finite P) and that the geometry makes the object exact without making it positive.

Audit ⟨1⟩ line filled in the carrier coordinate, ⟨2⟩ DC first: the transported Lebesgue measure, and it cancels the primes' uniforms exactly, ⟨3⟩ retrieved: 624's barycenter, 630's growth argument. Novel fired: the carrier pullback of the Poisson average (the load-bearing identity), the transport register; classical fired: Poisson kernels and Weil's criterion for the identification. No stop-claim: the record states a position after two attempts. Verdict as it turned out: forward on the leaf's form, which is now a boundedness statement; the boundedness itself, which is RH, unproved.

✻ Sautéed for 11m 5s · done 9:23 PM

※ recap: Goal: prove RH in the helix framework; today RH was compiled as equivalent to the boundedness of one explicit prime-and-Γ sequence at a single anchor. Next: attempt that boundedness at one explicit anchor.

These are drafts for the fixed conclusions `RiemannHypothesis` and
`GRHSpectral.GRHComplete`. The `fail` commands identify unfinished proof leaves;
they do not install assumptions or complete a proof. The companion `.lean` files
contain the proved support lemmas. No unconditional RH or GRH theorem is added.

## Evaluation of the afternoon updates

The current dependency build passes. The early-morning version of this document
and its verification record are preserved in
[proof-drafts/2026-09-05-early](/Users/samuellavery/work/helix_frobenius/proof-drafts/2026-09-05-early/RH_DISCHARGE_DRAFTS.md).
This revision incorporates the new Riesz count, growing-bank, boundary-flux, and
trace-limit files, and the degree-two calculation described in ledger 617.

| New source | Verified contribution | Remaining use in the discharge |
| --- | --- | --- |
| [RegistrationRemainderIntegrable.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationRemainderIntegrable.lean) | Interval integrability of the actual Riesz remainder for every positive scale and positive height interval. | Estimate the signed integral in the full balance. |
| [RegistrationMaster.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationMaster.lean:50) | Exact multiplicity-weighted count on any positive interval; at good endpoints, the exact increment of classical S(t). | Compare with the native multiplicity census, retaining the whole boundary term. |
| [RegistrationWarp.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationWarp.lean:46) | Stations for a continuous clock tending to infinity; no global bounded-strain condition. | Control the arithmetic registration for the chosen growing bank. |
| [RegistrationSeq.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationSeq.lean:58) | Per-index bounded banks, an escape theorem under eventual B(n)<=n/2, and exact residual increments. | Its gap consumer still requires strict station order; growth alone does not establish that order across different banks. |
| [RegistrationScale.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationScale.lean:94) | Explicit scale L(t)=c log(max(t,2)), 0<c<1; exact gap count and a bound for the bank change. | Keep the bank change when comparing endpoints. |
| [RegistrationFlux.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationFlux.lean:165) | Additivity, finite near-zero census, exact near/far split, and summable far inverse-square moment. | Its far-weight inequality explicitly assumes the far zeros have real part 1/2; an unrestricted application still needs a separate estimate. |
| [FejerMass.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/FejerMass.lean) and [FejerTail.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/FejerTail.lean) | Exact Fejer mass and on-line tail/deficit estimates. | The positivity and tail estimates for an on-line kernel do not yet bound a displaced zero kernel. |
| [LaplacePower.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/LaplacePower.lean) | Polynomial Laplace moments, including convergence. | Apply them to the paired numerator of the actual theta stage and prove its sign. |
| [StripTraceLimitIff.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/StripTraceLimitIff.lean:100) | Navigation between the earlier slit-domain trace specification and GRH; under GRH, the empty tower with E equal to the arithmetic trace satisfies that earlier specification. | Construct the tower with a correction regular through the real spectral axis, as in revised Draft D. |

The current fixed-cutoff draft is replaced by a growing-bank balance with the
full multiplicity census. The exact station-level shift is formalized below.
A claim that a particular cell grid contains exactly one analytic zero still
requires a proof for that grid. The broader registration interface is not
rejected on the basis of a numerical close-pair example.

The original all-signed `StationRegistration` remains excluded by the compiled
scope audit in
[StationRegistrationScopeAudit.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/StationRegistrationScopeAudit.lean:45).
Positive occurrences, with conjugation used for negative heights, retain the
intended enumeration scope.

## Simplicity in the helix construction

[PositiveStationRegistration.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/PositiveStationRegistration.lean)
retains simplicity as a geometric construction target and specifies its analytic
transfer. A registered occurrence is

```lean
structure PositiveZeroOccurrence where
  zero : XiZeroIndex
  positive : 0 < zero.val.im
  slot : Fin (ZD.xiOrderNat zero.val)
```

One unit of analytic multiplicity gets one occurrence. Surjective registration
and the two half-gap inequalities make height injective on these occurrences.
Reflection fixes the zero, while equality of the occurrences with slots `0` and
`1` excludes order greater than one. The companion theorem returns

```lean
ρ.val.re = 1 / 2 ∧ ZD.xiOrderNat ρ.val = 1
```

Thus an arithmetic construction of this registration would carry simplicity
through the correspondence. Distinct-event indexing alone has no multiplicity
slot to which that last argument can be applied. The positive registration's
enumeration, coverage, and shadow estimates remain to be constructed.

The independent count route already consumes analytic multiplicity:
`bandCountMult a b` sums `ZD.xiOrderNat` over all strip zeros with
`0 < Im ρ` and `a < Im ρ ≤ b`. For that route, the existing lower-height ladder
supplies location below 58; the simplicity theorem in `OnePerGap` applies above
the first station. A claim of global simplicity through that route also needs
the finite lower-height multiplicity census.

## Draft A: growing-bank balance with the full census

Write q(t)=S-hat at scale L(t), Cq(t)=theta(t)/pi+q(t), and
D(t)=N_off(t), with analytic multiplicity retained. The existing station
constructor chooses Cq(t)=n-3/2. Feeding it q-1/2 instead gives integer-level
boundaries:

\[
a_n=\operatorname{station}(q-1/2,n),\qquad
C_q(a_n)=n-1,\qquad E_q(a_n)=N(a_n)-n.
\]

[RegistrationCalibration.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationCalibration.lean)
implements this shift, including its continuity, coercivity, and start-level
guard. For q(t)=S-hat at L(t)=c log(max(t,2)), it proves

\[
N((a_n,a_{n+1}])=1+\mathcal E_L(a_n,a_{n+1}),
\]

where the complete signed error is

\[
\mathcal E_L(a,b)=\frac1\pi\int_a^b\mathrm{rem}_{L(a)}(t)\,dt
 +B_{L(a)}(a,b)
 -\bigl(\widehat S_{L(b)}(b)-\widehat S_{L(a)}(b)\bigr).
\]

This calibrates the clock; it does not establish interlacing of these boundaries
with every analytic zero. In particular, no universal one-zero-per-cell bound
is inserted into the revised draft.

The same companion file gives a direct transfer to the native registration.
Let V_L(t)=Smult(t)-S-hat at scale L(t). At good endpoints 0<a<=b,

\[
D(b)-D(a)=\mathcal E_L(a,b)-\bigl(V_L(b)-V_L(a)\bigr).
\]

This is `offLine_increment_eq_registrationDefect_sub_native`. It allows arbitrary
clusters and multiplicities. The pending analytic estimate is on this **combined
expression**, including the native registration, the signed near-zero flux, the
far flux, and the bank change. The separate Riesz count identity does not remove
any of these terms.

The fixed unconditional conclusion can now be targeted through the existing
integrated consumer. Unfolded mathematics:

\[
\int_0^T D(t)\,dt=o(T).
\]

Expectation-free decomposition A uses the exact increment identity above, a
certified base interval, and an estimate of the integrated combined error.
Decomposition B controls the full lifted third coordinate directly, then uses
the compiled multiplicity-weighted reflection identity. Both retain full turns.

```lean
import RequestProject.RegistrationCalibration
import RequestProject.HelixHubFusion

open Complex Filter Asymptotics MeasureTheory
open CriticalLinePhasor CriticalLinePhasor.ContourArgument
open CriticalLinePhasor.CaptureInterfaceAudit

example : RiemannHypothesis := by
  apply riemannHypothesis_of_integratedDefectSublinear
  change (fun T => ∫ t in (0 : ℝ)..T, (offLineStripZeroCountMult t : ℝ))
    =o[atTop] fun T : ℝ => T
  fail "A: integrated bound for the full Riesz-minus-native balance, retaining multiplicity and bank change"
```

Concrete local rewrite for decomposition A:

```lean
have hbalance := offLine_increment_eq_registrationDefect_sub_native
  (logScale_pos hc a) ha hb hab
```

Here hc:0<c, ha:GoodHeight a, hb:GoodHeight b, and hab:a<=b. This rewrite
supplies the interval equality, not the sublinear estimate. Finite-height
coverage must be retained when assembling intervals from a positive base.

[universal.tex](/Users/samuellavery/work/helix_frobenius/automorph/universal.tex:2463)
separates distinct events, native line multiplicity, and full strip multiplicity.
The compiled lift in
[HelixRegistrationWarp.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/HelixRegistrationWarp.lean:147)
is u -> (exp(i pi u),u). Its contour/native third-coordinate difference is
2 times the right-half multiplicity count. Circle-phase equality holds while
that integer turn count remains in the third coordinate. The proof target uses
the retained coordinate; projection equality alone does not estimate it.

## Draft B: the full prime-symbol inequality

For every real γ, `1 < σ < 3/2`, `s = σ + iγ`, `d = 2σ - 1`, and
every complex polynomial with `R(0)=0`, the compiled clock form is

\[
Q_R=Q_R^{\rm DC}+\sum_n\Lambda(n)n^{-\sigma}
 \Re\{e^{-i\gamma\log n}A_R(\log n;d)\}.
\]

The summation is over natural numbers; the zero weights remove 0 and 1. All
prime powers retain their common base-prime phase. The closed Pascal coefficients
are positive in the specified range of `d`, but the actual degree `(1,2)`
quadratic symbol already has a negative principal minor when `d ℓ > 2`
(`primeSymbol_actual_minor12_neg`). The clock symbol equals `-2` times the
one-sided symbol. Retain the first-order finite-part coefficient through the
compiled pairing before applying that reconciliation.

Expectation-free decomposition A collects by `n` and estimates the full signed
sum with one common `γ`. Decomposition B works with the same finite Hermitian
form before collection, seeking a positive arithmetic representation of the
complete expression. Neither the Pascal identity nor per-degree phase
optimization supplies the missing inequality.

```lean
import RequestProject.PrimeSymbolReconciliation

open Complex
open CriticalLinePhasor CriticalLinePhasor.ContourArgument

example : RiemannHypothesis := by
  apply RHBridge.no_offline_zeros_implies_rh
  apply rh_iff_prime_jets_nonneg.mpr
  intro γ σ hσ hσupper R hR
  change 0 ≤ PrimeClock.primeJetsForm R
    ((σ : ℂ) + (γ : ℂ) * I) ((2 * σ - 1 : ℝ) : ℂ)
  rw [PrimeClock.primeJetsForm_eq_dc_add_phase R (2 * σ - 1) σ γ hσ]
  fail "B: nonnegativity of the full DC plus correlated prime-power phase sum"
```

### The actual degree-two jet test

[SeatDegreeTwo.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/SeatDegreeTwo.lean)
computes the (1,2) block of the actual compiled pairing. It also identifies its
prime-moment specialization with `jetValueP`, using the existing finite-part
pairing. Put z0=primeLogDeriv(s), z1=-primeJet(s,1), and h=2 Re z0. Then

\[
H=\begin{pmatrix}
h/d&\overline{z_1}/d+h/d^2\\
z_1/d+h/d^2&2\Re z_1/d^2+2h/d^3
\end{pmatrix},\qquad
\Re\det H=\frac{h^2-d^2|z_1|^2}{d^4}.
\]

For d>0 and Re primeLogDeriv(s)>=0, nonnegativity of this determinant is exactly

\[
|\operatorname{primeJet}(s,1)|\le
\frac{2\Re\operatorname{primeLogDeriv}(s)}d.
\]

This is a scalar arithmetic inequality still to prove. The determinant formula
is an exact computation; nonnegative determinant alone does not assert positivity
of the whole degree-two matrix without the other necessary conditions, and the
degree-two test alone does not cover arbitrary polynomials R.

Concrete next step at a prime-chart anchor:

```lean
have hminor : 0 ≤ (SeatDegreeTwo.block d (PrimeClock.primeMoment s)).det.re := by
  apply (SeatDegreeTwo.prime_det_nonneg_iff d hd s hz).2
  fail "B2: prove the arithmetic derivative-to-value norm bound at this anchor"
```

Here hd:0<d and hz:0<=(primeLogDeriv s).re must come from the actual anchor
construction. No sign assumption is added to the final unconditional theorem.

Ledger 618's multi-anchor trigonometric square has an **upper-bound** direction
because the prime contribution is subtracted from DC. It does not yet give the
lower bound in Draft B. For higher-degree monomials, discarding neighboring
reflected zero terms requires a sign proof for those terms. Retain them when
trying an anchor combination or a bound on clustered contributions. The
numerical bounds and proposed cluster dichotomy in that ledger entry are not
used as proved Lean inputs here.

## Draft C: eventual sign of the explicit theta stages

Let `F_U(z) = 2 ∫_(0,U] K(u) cos(zu) du`, `z(s) = -i(s-1/2)`, and
`G_U(s)=F_U(z(s))/2`. `XiIntegralIdentification` identifies the full integral
with xi and proves convergence of `G_n(s)` and `G_n'(s)`. The mass formula is

\[
\frac{\Re(G_U'/G_U)(s)}{\Re s-1/2}
 =\frac{-\Im(F_U'(z)\overline{F_U(z)})}{|F_U(z)|^2\Im z}.
\]

The consumer supplies A>0. The remaining sign is required at each point with
|Im s|>1269/2, A/(log |Im s|)^9<Re s<1/2, and xi(s) nonzero. It is pointwise
and eventual, and it is required for the **same**
theta stages whose values and derivatives converge. A sign theorem for a
different finite bank requires a further identification or convergence proof.

Expectation-free decomposition A expands the numerator as a double integral
and pairs the conjugate terms. Decomposition B estimates the truncation remainder
and boundary term together in that numerator. Positive scalar kernel values
alone do not assign a sign to the oscillatory cross terms.

```lean
import RequestProject.XiStageMass

open Complex Filter Topology
open CriticalLinePhasor CriticalLinePhasor.XiKernelBridge

example : RiemannHypothesis := by
  obtain ⟨A, hA, hdoor⟩ := SeatingLedger.riemannHypothesis_of_stage_mass
  apply hdoor
  intro s him hlo hhi hxi
  refine ⟨(fun n => xiArithmeticStage n), xiArithmeticStage_tendsto s,
    deriv_xiArithmeticStage_tendsto s, ?_⟩
  fail "C: eventual theta-stage mass sign at this channel point"
```

## Draft D: character-wise finite spectral towers

Unfolded target: for every modulus `N ≠ 0`, every Dirichlet character `χ`, and
every zero of `L(s,χ)` in `0 < Re s < 1`, prove `Re s = 1/2`.

The finite-stage readout is
`Σ_j ((z - d_n(j))⁻¹ + c_n(j))`, with `d_n(j)` real. Each stage is holomorphic
off the real axis. Work on the open chart domain
`stripOffReal = {z | z.im ≠ 0 ∧ -1/2 < z.im ∧ z.im < 1/2}`.
A locally uniform limit to the arithmetic log-derivative channel transports
regularity off the real axis. In this revised construction the correction is
required to be holomorphic on the entire open chart band
`spectralStrip = {z | -1/2 < z.im ∧ z.im < 1/2}`, including its real axis. The existing
resonance theorem then supplies the zero correspondence. This uses correspondence
of singularities; it does not require equality of a zero with an eigenvector.
The correctly normalized channel is `i L'/L(1/2+i z)`, the logarithmic derivative
with respect to `z`. Multiplying it by `i` recovers the existing `-L'/L` channel.
[StripTraceRegularCorrection.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/StripTraceRegularCorrection.lean)
proves that the arithmetic trace fails this stronger correction condition at
any nontrivial zero. This excludes the specific empty-tower witness from the
new construction specification; it does not construct a replacement tower.
The chart domain and the factor of `i` are explicit in
[StripTraceCapture.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/StripTraceCapture.lean).
This uses the preimage of the analytic critical strip as a readout domain;
it does not impose a strip on the physical helix. Requiring the uncompleted
`L'/L` channel to be regular on the entire off-real plane would also demand
removal of its trivial-zero singularities. The restricted domain avoids that
unnecessary demand, including for principal and imprimitive characters.

Expectation-free decomposition A constructs finite Hermitian pencil stages and
identifies their normalized resolvent traces before taking the limit.
Decomposition B constructs the arithmetic trace first, proves off-real local
uniform approximation by the stages, and invokes the same regularity transfer.
For complex characters, a conjugate construction must specify its action on
`χ` and the conjugate character rather than assume the zeta reflection law
within one character.

```lean
import RequestProject.StripTraceRegularCorrection

open Complex Filter Topology
open CriticalLinePhasor CriticalLinePhasor.CaptureInterfaceAudit

example : GRHSpectral.GRHComplete := by
  intro N _ χ
  suffices h : ∃ (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℝ)
      (c : ∀ n, Fin (r n) → ℂ) (E : ℂ → ℂ),
      DifferentiableOn ℂ E spectralStrip ∧
      TendstoLocallyUniformlyOn
        (fun n => normalizedSpectrumTrace (d n) (c n))
        (fun z => normalizedLTrace χ z - E z) atTop stripOffReal by
    obtain ⟨r, d, c, E, hE, hlim⟩ := h
    exact grh_of_regularCorrectionTraceLimit χ d c E hE hlim
  fail "D: arithmetic finite spectra, correction regular through the real axis, and local uniform limit"
```

The existing `lineTowerSpectrum` uses the on-line window census; its current
limit identification is with that census. For Draft D, prove the displayed
arithmetic channel limit for the chosen construction. Rank and spectral heights
may grow with the stage. A single bounded global operator is not substituted
for this growing tower.

### Connecting the 3D pencils to this draft

[HermitianPencil3D.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/HermitianPencil3D.lean:104)
transports both pencil coefficients under spatial lift and carrier congruence.
Its approximate-kernel theorem also allows the stage dimension to vary. The
literal consumer, after constructing its listed arguments, is:

```lean
have hz := Pencil3D.eigenvalue_real_of_pencil_limit
  A B hA hB z v m hm hmass hres
```

Here `hmass` is convergence of the metric masses to `m > 0`, and `hres` is
convergence to zero of the imaginary part of the full pencil pairing. In
[ThreeDNativePencilLimit.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/ThreeDNativePencilLimit.lean:70),
the reference state's metric mass is exactly one, and that imaginary pairing
is exactly `-z.im` at every stage. The separately proved scalar native-coupling
limit does not itself set this full pairing to zero. Construct the required
arithmetic relation for the chosen states when using the pencil consumer.

For the trace route, `d n` and `c n` in the displayed draft are independent of
the spectral variable `z`. The native lane matrices also have a parameter `s`.
Fix the bank parameters before producing the real spectra; substituting
`s = 1/2 + i z` into a Gram matrix does not automatically give the fixed-spectrum
holomorphic stages used by `grh_of_regularCorrectionTraceLimit`.

## Search and verification record

The companion source headers record the unfolded statements, decomposition
strategies, and searches. The afternoon audit additionally searched the unfolded
native-balance, moment-pairing, and trace-correction identifiers and naming
variants. Its main commands were:

```sh
rg -n -i 'integrated_?defect_?sublinear|off_?line_?strip_?zero_?count_?mult|native_?registry_?residual|registration_?defect|boundary_?station|prime_?moment|pair_?functional|normalized_?l_?trace|regular_?correction' RequestProject --glob '*.lean'
rg -n -i 'RiemannHypothesis|GRHComplete|isLittleO.*integral|integral.*isLittleO|det_fin_two|normSq_eq_norm_sq|DifferentiableOn.*mono|tendsto_atTop_atTop' .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n -i 'station.*shift|shift.*station|boundary.*station|integer.*level|center.*strain|strain.*half|shifted.*strain|strain.*offset|level.*offset' RequestProject --glob '*.lean'
rg -n -i 'degree_?two|degree2|minor.?12|det.*S_?2|anchor.*square|square.*anchor|monomial.*(form|symbol)|symbol.*monomial' RequestProject --glob '*.lean'
rg -n 'spectralStrip|stripChart|fullStripChart|normalizedLTrace.*differentiableAt|normalizedLTrace.*not|entireCorrection|regularCorrection' RequestProject --glob '*.lean'
```

Semantic searches for the afternoon additions: LeanSearch for the determinant
of a two-by-two Hermitian complex matrix; Loogle `Complex.normSq, _ ^ 2`.
Earlier searches retained for the unchanged consumers:

```sh
rg -n 'primeStrain|resid_station_abs_le|net_defect_le|StationRegistration|OnePerGap|xiArithmeticStage_mass|rh_iff_prime_symbol_nonneg|re_half_of_traceLimit' RequestProject --glob '*.lean'
rg -n -i 'station.*(le|upper|below)|resid.*(goodHeight|classicalS|step|adjacent)' RequestProject --glob '*.lean'
rg -n 'csInf_le|intermediate_value_Icc|int.*abs.*lt_one|abs.*int.*lt_one|strictMono.*bddBelow' .lake/packages/mathlib/Mathlib --glob '*.lean'
rg -n 'infinite_range_of_injective|Infinite.*range|Finite.*range|finite_range' .lake/packages/mathlib/Mathlib/Data/Set/Finite --glob '*.lean'
```

Semantic searches: LeanSearch for injective natural-number functions having
infinite range; Loogle `Set.Infinite, Function.Injective`. Compiler and axiom
outputs are retained in
[RH_DISCHARGE_VERIFICATION.md](/Users/samuellavery/work/helix_frobenius/RH_DISCHARGE_VERIFICATION.md).
Draft failures are separate from the exit-zero companion proofs.
