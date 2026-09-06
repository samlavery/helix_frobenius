# Discharge drafts against the September 5 Lean updates

These are drafts for the fixed conclusions `RiemannHypothesis` and
`GRHSpectral.GRHComplete`. The `fail` commands identify unfinished proof leaves;
they do not install assumptions or complete a proof. The companion `.lean` files
contain the proved support lemmas. No unconditional RH or GRH theorem is added.

## What the current constructions deliver

| Source | Current conclusion | Next construction or estimate |
| --- | --- | --- |
| [RegistrationStations.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationStations.lean:103) | Continuous bounded strain gives first crossings, strict station order, and escape to infinity above the start level. | A bound on the actual strip-count residual at those crossings. |
| [PrimeStrain.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/PrimeStrain.lean:50) | An explicit finite prime-power sine sum supplies such a strain. | Match the chosen strain to the fiber model used in the arithmetic estimate. |
| [RegistrationDC.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationDC.lean:58) | A logarithmic magnitude envelope for station residuals and cumulative count discrepancy. | Control adjacent increments strictly below one; the magnitude envelope alone does not give that bound. |
| [OnePerGap.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/OnePerGap.lean:92) | Multiplicity-weighted gap count one gives the critical real part and analytic order one above the first station. | Establish the gap count from the constructed fiber. |
| [HelixHeightDischarge.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/HelixHeightDischarge.lean:99) | Kernel descent, Green transport, or ledger symmetry supplies full intertwining when that respective input is supplied. | Construct one of those inputs for the arithmetic correspondence, retaining the computed reflected-mode defect. |
| [XiStageMass.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/XiStageMass.lean:40) | An explicit theta-stage mass formula, with value, derivative, and mass convergence. | The eventual sign for these same stages. |
| [PrimeSymbolReconciliation.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/PrimeSymbolReconciliation.lean:42) | Reconciles the two prime-symbol normalizations, including their factor of `-2`. | Nonnegativity of the complete DC plus correlated-phase expression. |

The original all-signed `StationRegistration` has a scope error. Its natural-number
ordering and half-gap bounds imply a lower bound on every zero ordinate.
Conjugation then gives an upper bound. The finite strip census contradicts the
injection of all natural-number indices. This is proved in
[StationRegistrationScopeAudit.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/StationRegistrationScopeAudit.lean:45).
The drafts below use positive heights and recover negative heights by conjugation.

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

## Draft A: adjacent registration residuals

Unfolded mathematics, for strain `q`:

\[
C_q(t)=\vartheta(t)/\pi+q(t),\quad
t_n=\inf\{t\ge10:C_q(t)=n-3/2\},\quad
E_q(t)=N_{\rm strip}^{\rm mult}(t)-1-C_q(t).
\]

At admissible stations, `E_q(t_n) = N(t_n) - n + 1/2`. Consequently

\[
E_q(t_{n+1})-E_q(t_n)=N((t_n,t_{n+1}])-1.
\]

[RegistrationResidualSupport.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/RegistrationResidualSupport.lean)
proves this identity and closes the integer step from an adjacent bound. It also
reduces `t_n ≤ 58` to the explicit crossing inequality
`stationLevel n ≤ regClock q 58`. No station monotonicity of the clock is needed
for this upper bound; the intermediate value theorem supplies an upper crossing.

Expectation-free decomposition A uses the integer count increment directly.
Decomposition B expands the residual as `S_classical(T) - q(T)` at good heights
and estimates the exact difference, including jumps if endpoints are zeros.
Both algebraic expansions are supplied by the companion file.

```lean
import RequestProject.RegistrationResidualSupport

open Complex
open CriticalLinePhasor CriticalLinePhasor.ContourArgument

example : RiemannHypothesis := by
  suffices h : ∃ X n₀ : ℕ,
      regClock (primeStrain X) 10 < stationLevel n₀ ∧
      stationLevel n₀ ≤ regClock (primeStrain X) 58 ∧
      (∀ n, n₀ ≤ n →
        |resid (primeStrain X) (primeStation X (n + 1)) -
          resid (primeStrain X) (primeStation X n)| < 1) by
    obtain ⟨X, n₀, hn₀, hupper, hstep⟩ := h
    have H := onePerGap_of_adjacent_resid
      (primeStrain_continuous X) (abs_primeStrain_le X) hn₀ hstep
    apply RHBridge.no_offline_zeros_implies_rh
    apply nontrivialZeros_online_of_onePerGap_of_le_58 H
    simpa only [Nat.add_zero, primeStation] using
      primeStation_le_58_of_level_le X hn₀ hupper
  fail "A: construct the cutoff, start index, and strict adjacent residual estimate"
```

This tests the exact **fixed finite cutoff** currently defined in Lean.
[HP_PROGRAM.md](/Users/samuellavery/work/helix_frobenius/HP_PROGRAM.md:20)
also describes neighbor corrections, arithmetic lane modes, and height-matched
banks. Those are not terms in `primeStrain X`. A proof about that enhanced model
must first define its strain and prove its station properties; measurements for
that model do not establish the displayed fixed-cutoff estimate.

The logarithmic estimates in `RegistrationDC` start at `exp 6 + 1` and carry a
strict station-level guard. Retain both conditions. A local argument starting
there needs separate coverage between the certified lower range and that start.

## The S(t) warp and the retained third coordinate

[universal.tex](/Users/samuellavery/work/helix_frobenius/automorph/universal.tex:2463)
distinguishes the distinct event census, the line census with multiplicity, and
the strip census with multiplicity. Its exact decomposition is

\[
S_{\rm classical}=S_{\rm event}
 +(N_{\rm line}^{\rm mult}-N_{\rm event})+N_{\rm off}^{\rm mult}.
\]

The registration residual in Draft A uses the last, full strip census.
[HelixRegistrationWarp.lean](/Users/samuellavery/work/helix_frobenius/RequestProject/HelixRegistrationWarp.lean:147)
retains the lift `(exp(i π u), u)`: the third-coordinate gap between classical
and multiplicity-weighted native registration is twice the right-half count.
Phase equality survives this integer number of full turns. Use the third-coordinate
estimate, or the exact adjacent count, when transporting the warp.

Concrete alternative next step, using the existing compiled gap lemma:

```lean
have hgap : classicalSContour hT - ResidueJump.Smult T < 2 := by
  -- Derive a strict bound on the lifted third-coordinate difference.
  fail "W: arithmetic bound on the lifted registration, with the turn count retained"
```

Here `Smult` is the multiplicity ledger used by
`registration_identification_of_gap_lt_two`; this short pointer is not one of the
four elaboration probes below.

## Draft B: the full prime-symbol inequality

For `s = σ + iγ`, `d = 2σ - 1`, and `R(0)=0`, the compiled clock form is

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

## Draft C: eventual sign of the explicit theta stages

Let `F_U(z) = 2 ∫_(0,U] K(u) cos(zu) du`, `z(s) = -i(s-1/2)`, and
`G_U(s)=F_U(z(s))/2`. `XiIntegralIdentification` identifies the full integral
with xi and proves convergence of `G_n(s)` and `G_n'(s)`. The mass formula is

\[
\frac{\Re(G_U'/G_U)(s)}{\Re s-1/2}
 =\frac{-\Im(F_U'(z)\overline{F_U(z)})}{|F_U(z)|^2\Im z}.
\]

The remaining sign is pointwise and eventual. It is required for the **same**
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
A locally uniform limit to the arithmetic log-derivative channel, up to a
correction holomorphic on this domain, transports this regularity. The existing
resonance theorem then supplies the zero correspondence. This uses correspondence
of singularities; it does not require equality of a zero with an eigenvector.
The correctly normalized channel is `i L'/L(1/2+i z)`, the logarithmic derivative
with respect to `z`. Multiplying it by `i` recovers the existing `-L'/L` channel.
Both the domain and the factor of `i` are explicit in
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
import RequestProject.StripTraceCapture

open Complex Filter Topology
open CriticalLinePhasor CriticalLinePhasor.CaptureInterfaceAudit

example : GRHSpectral.GRHComplete := by
  intro N _ χ
  suffices h : ∃ (r : ℕ → ℕ) (d : ∀ n, Fin (r n) → ℝ)
      (c : ∀ n, Fin (r n) → ℂ) (E : ℂ → ℂ),
      DifferentiableOn ℂ E stripOffReal ∧
      TendstoLocallyUniformlyOn
        (fun n => normalizedSpectrumTrace (d n) (c n))
        (fun z => normalizedLTrace χ z - E z) atTop stripOffReal by
    obtain ⟨r, d, c, E, hE, hlim⟩ := h
    exact grh_of_stripTraceLimit χ d c E hE hlim
  fail "D: arithmetic finite spectra, normalization, strip-holomorphic correction, and local uniform limit"
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
holomorphic stages used by `grh_of_stripTraceLimit`.

## Search and verification record

The companion source headers record the unfolded statements, decomposition
strategies, and searches. Additional searches used for this evaluation:

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
