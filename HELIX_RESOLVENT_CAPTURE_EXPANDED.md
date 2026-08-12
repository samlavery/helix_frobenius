# Helix Resolvent-Capture — expanded theorem catalog

Every theorem in `RequestProject/HelixResolventCapture.lean` and its two evidence dossiers, each
with **what it proves** (calibrated to the Lean, never stronger) and **why it matters**. Companion
to the concise index in `HELIX_RESOLVENT_CAPTURE_THEOREMS.md`.

## The claim in one paragraph

RH follows from GRH for the trivial character, unconditionally (`RH_of_GRH_Trivial_Char`) — the mod-1
L-function *is* `ζ`, so one character's GRH is RH. Self-adjointness is **proven, not assumed**
(`vonNeumannOp_isSymmetric`), so it is never a hypothesis. The only open input is a **reading
hypothesis**, of which there are two: `ThreeD_crossings_are_real_zeros` (`3D-ZERO-REAL`, strong
Hilbert–Pólya) and `OneD_zeta_zero_correlated` (`1D-ZERO-EXCLUSIVE-REAL`, weak Hilbert–Pólya). The
two are **logically equivalent** (each holds `⟺ Re ρ = ½` for every nontrivial zero), so they differ
in *interpretation* — which zero is treated as primary — not in truth-value. Both evidence dossiers
(16 and 18 facts) are proven unconditionally at `{propext, Classical.choice, Quot.sound}`, no
`sorry`/`axiom`. Nothing here asserts RH or GRH: what is proven is the reductions and the supporting
facts; the one open link is exactly the truth of RH for `χ₁`.

---

## The capstone theorems

### `RH_of_GRH_Trivial_Char` — line 528 · *proven*
**Proves.** GRH for the mod-1 character `χ₁` ⟹ Mathlib's `RiemannHypothesis`. The mod-1 L-function
equals `riemannZeta`, so the hypothesis handles the strip; Mathlib handles the rest (no zeros for
`Re s ≥ 1`; the negative-real trivial zeros via the completed-ζ functional equation).

**Why it matters.** Reduces the entire target to GRH for one character — establish that and RH is a
corollary. It is the bridge from the spectral framework back to the classical statement.

### `ThreeD_crossings_are_real_zeros` — line 608 · *hypothesis, not proven*
**Proves.** Nothing — a named hypothesis (`3D-ZERO-REAL`, strong HP): every nontrivial zero `ρ` is
an eigenvalue of the self-adjoint fibre operator — a real height `γ` with
`specOp (vonNeumannOp γ) ρ ψ = 0` for some `ψ ≠ 0` (equivalently, the resolvent `1/specBchan`
blows up at `ρ`).

**Why it matters.** If true, GRH for `χ₁` is immediate — the operator is self-adjoint (real
spectrum), so the crossing forces `Re ρ = ½`. One of the two open inputs; equivalent to RH for `χ₁`.

### `OneD_zeta_zero_correlated` — line 625 · *hypothesis, not proven*
**Proves.** Nothing — a named hypothesis (`1D-ZERO-EXCLUSIVE-REAL`, weak HP), a per-zero
**disjunction**: either a crossing at *some* real height (3D-primary), or a crossing at the zero's
own 1D ordinate `γ = ρ.im` (1D-primary), the latter carrying the eigenstate↔ordinate correspondence.

**Why it matters.** The agnostic reading — it routes through whichever zero is chosen primary, and in
the 1D branch it proves the crossing height equals the ordinate the chart reports. Logically
equivalent to the strong hypothesis (both `⟺` RH for `χ₁`); the two differ in interpretation, not
truth-value.

### `grh_of_resolvant_trace_3D_real` — line 639 · *proven implication*
**Proves.** From `ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ₁`, GRH for `χ₁`. Each zero's
crossing plus von Neumann reality (`spectral_cancellation_on_real_axis`, resting on the unconditional
`vonNeumannOp_isSymmetric`) gives `Re = ½`.

**Why it matters.** The identity reading's GRH, and it isolates the open step cleanly: proven
evidence on one side, the single hypothesis on the other, self-adjointness discharged internally.

### `grh_of_resolvant_trace_1D_correlation` — line 652 · *proven implication*
**Proves.** From `OneDCorrelationEvidence ∧ OneD_zeta_zero_correlated χ₁`, GRH for `χ₁`, by a
case-split on the primary choice; both branches close by the same von Neumann reality.

**Why it matters.** The correlation reading's GRH — it shows the weak reading needs nothing stronger
than the strong one: the same unconditional self-adjoint mechanism closes both branches.

### `RH_of_resolvant_trace_3D_real` — line 662 · *proven*
**Proves.** `ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ₁ ⟹ RiemannHypothesis` — the 3D
GRH composed with `rh_from_grh`.

**Why it matters.** The identity reading stated in classical language, operator to
`RiemannHypothesis`.

### `RH_of_resolvant_trace_1D_correlation` — line 669 · *proven*
**Proves.** `OneDCorrelationEvidence ∧ OneD_zeta_zero_correlated χ₁ ⟹ RiemannHypothesis`.

**Why it matters.** The correlation reading in classical language. With the 3D route it realizes "RH
if either reading's hypothesis holds" — one truth condition wearing two interpretations.

### `threeDRealEvidence` — line 746 · *proven*
**Proves.** Unconditionally inhabits `ThreeDRealEvidence`, the 16-fold conjunction of the identity
reading's supporting facts (below) — certifying each is a theorem.

**Why it matters.** The evidence *for* the identity reading: the pile of unconditional facts that
make "the 3D crossings are the real zeros" a serious reading. Evidence, not a proof of RH.

### `oneDCorrelationEvidence` — line 771 · *proven*
**Proves.** Unconditionally inhabits `OneDCorrelationEvidence`, the 18-fold conjunction of the
correlation reading's supporting facts (below).

**Why it matters.** The evidence *for* the correlation reading, centered on the S(t) registration
mechanics (jump = multiplicity = residue; `dim = 1 + θ/π + S`; the loss-ledger). Evidence, not a
proof of RH.

### `threeD_real_case` — line 801 · *proven*
**Proves.** The pair: `threeDRealEvidence` (proven) and the conjunction-GRH proof
`∀ χ₁, ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ₁ → GRH χ₁`.

**Why it matters.** Packages the identity reading as one auditable object — settled evidence, plus
exactly what GRH additionally needs.

### `oneD_correlation_case` — line 813 · *proven*
**Proves.** The pair: `oneDCorrelationEvidence` (proven) and
`∀ χ₁, OneDCorrelationEvidence ∧ OneD_zeta_zero_correlated χ₁ → GRH χ₁`.

**Why it matters.** The correlation reading as one auditable object. The two `*_case` theorems side
by side are the whole claim: two proven evidence piles, two isolated hypotheses, one shared GRH→RH
bridge.

---

## 3D-real (identity) reading — evidence dossier

### `vonNeumannOp_isSymmetric` — `RequestProject/ClosedForm.lean:1688`
**Proves.** `vonNeumannOp γ = (γ : ℂ) • id` — multiplication by the real `γ` on the one-dimensional
fibre `ℂ` — is symmetric, hence self-adjoint, with real spectrum `{γ}`.

**Why it matters.** The linchpin: in classical Hilbert–Pólya self-adjointness is *assumed*; here it
is a theorem. Each crossing height is the real eigenvalue of a genuinely self-adjoint operator, so
"the eigenvalue is real" is structural — the mechanism that puts a crossing on the line.

### `threeD_exhaustive` — `RequestProject/SourceHolonomy.lean:778`
**Proves.** For every `E : ℂ → ℂ` and every real height `y`, if `E (y : ℂ) = 0` then `(y : ℂ)` is a
source (`E z = 0 ∧ conj z = z`) — automatic, since reals are conjugation-fixed.

**Why it matters.** The "nowhere else for a zero in 3D" content: the 3D event space is the real
height ray, the fixed locus of conjugation, so every zero event there is self-conjugate/sourced.
Supplies the 3D side of exhaustion unconditionally.

### `threeD_metric_no_zeros` — `RequestProject/SourceHolonomy.lean:784`
**Proves.** The 3D cup form is definite: `Cup F F = 0 ↔ F = 0` for finitely-supported states `F`.

**Why it matters.** Vanishing is a property of readings, not states — no nonzero 3D state is null, so
a zero must be a readout event on the height ray (where it is sourced). It forbids hiding a zero as a
degenerate state.

### `windFromPrimes_mul` — `RequestProject/Origination.lean:137`
**Proves.** The winding is multiplicative over factorization:
`windFromPrimes (m·n) = windFromPrimes m · windFromPrimes n` (from `Nat.factorization_mul`), with no
`Real.log`.

**Why it matters.** The fundamental theorem of arithmetic realized as a homomorphism into the circle
— the helix carries no information beyond the prime factorization. Grounds the 3D carrier and the 1D
L-function as two prime-built readings of one arithmetic.

### `fiber_accumulates_to_L` — `RequestProject/Faithfulness.lean:147`
**Proves.** For `χ ≠ 1` and `Re s > 0`, the partial sums `Σ χ(n)·n^{-s}` converge to `L(s,χ)` across
the whole strip — not just the absolute-convergence region `Re s > 1`.

**Why it matters.** Makes the phasor bank and the L-function the same object on the critical line, so
a bank crossing at height `γ` *is* `L(½+iγ) = 0`. It answers the "`Re s > 1`" chart artifact: the
bank accumulates straight through the strip.

### `heights_distinct` — `RequestProject/NoDoubleCancellation.lean:56`
**Proves.** `logGen n = log(n+1)` is injective — distinct sites carry distinct eigen-heights.

**Why it matters.** Unique factorization as a spectral fact: the generator's spectrum is strictly
monotone and non-degenerate, so eigenspaces don't pile up. The precondition for no split focus.

### `cancellation_modes_subsingleton` — `RequestProject/NoDoubleCancellation.lean:94`
**Proves.** At any spectral parameter `s`, at most one standard basis mode lies in the kernel of
`specOp Aχ s` (a mode cancels iff its height matches `specHeight s`, and heights are distinct).

**Why it matters.** "No split focus": a cancellation concentrates on one mode, so a crossing marks a
single zero ordinate rather than a superposition of two.

### `localPoly_reciprocal` — `RequestProject/FiniteWeightFiber.lean:87`
**Proves.** The local numerator is self-reciprocal: `localPoly X = (−X)^{|ι|}·localPoly X⁻¹` for
`X ≠ 0` (from weight-inversion closure and `∏λ = 1`).

**Why it matters.** The per-place functional equation (`s ↦ 1−s`) realized at each prime. The global
functional equation assembled from these has fixed axis `Re s = ½` — the distinguished line the
crossings sit on.

### `frobeniusBlock_det_one` — `RequestProject/FrobeniusSimilitude.lean:167`
**Proves.** The chiral block `diag(z, z̄)` with `z = e^{−iy·log n}` has `det = |z|² = 1`.

**Why it matters.** The Frobenius similitude is a pure rotation (unitary), no dilation — the Satake
weights stay on the unit circle, which keeps the eigenphases real.

### `fiber_det_one` — `RequestProject/FiniteWeightFiber.lean:62`
**Proves.** `∏ᵢ W.weight i = 1`, by pairing each channel with its dual (`λ·λ⁻¹ = 1`) and forcing a
trivial self-dual center.

**Why it matters.** The modulus ledger under the involution `λ ↦ λ⁻¹` — the `s ↦ 1−s` symmetry at
the weight level that `localPoly_reciprocal` consumes.

### `hpOperator_isHermitian` — `RequestProject/HilbertPolya.lean:54`
**Proves.** The ledger diagonal `hpOperator T = diagonal (p ↦ (p.1.1 : ℂ))` is Hermitian — real
ordinate entries.

**Why it matters.** Reality by type: the operator meant to register the zeros has real eigenvalues by
construction. With `eigenheight_is_exact_vanishing` and `finrank_modeSpace`, it is the identity
reading realized on a finite window.

### `finrank_modeSpace` — `RequestProject/GradedModeDictionary.lean:99`
**Proves.** `finrank ℂ (ModeSpace γ) = eventOrder γ`, where
`ModeSpace γ = ℂ[X]/((X − line γ)^{eventOrder γ})`; dimension `0` off events.

**Why it matters.** A genuine graded local algebra whose dimension equals the vanishing order (= the
`S`-jump = the log-derivative residue). It matches the operator's spectral multiplicity to the
analytic order — a double zero is a 2-dimensional crossing.

### `focal_residual_zero_iff_L_zero` — `RequestProject/FocalResidualVanishes.lean:67`
**Proves.** `Dcell χ Z = 0 ↔ L (reprPoint χ Z) = 0` with `reprPoint = ½ + i·log Z`, via the
factorization `Dcell = Vχ·Φχ` with `Vχ ≠ 0` and `Φχ = (π/3)·L`.

**Why it matters.** Exact harmonic cancellation — the π/3 claim: the cell channel vanishes iff the
L-value does, with no leftover residue (`Vχ` never vanishes). The sharpest local form of "the
crossing is the zero," at the exact π/3 amplitude.

### `eigenheight_is_exact_vanishing` — `RequestProject/HilbertPolya.lean:71`
**Proves.** Every window index `p` has `riemannZeta (line p.1.1) = 0` — `ζ(½+iγ) = 0` exactly (the
window is indexed by the genuine zero-events in `(0, T]`).

**Why it matters.** The operator's spectrum is the exact zero ordinates, not a smooth approximation.
With Hermiticity, a self-adjoint operator whose real eigenvalues are zeta zeros.

### `gradedResolventTrace_eq_residue_sum` — `RequestProject/GradedModeDictionary.lean:326`
**Proves.** For `w` off the window ordinates,
`gradedResolventTrace w T = ∑_{γ} r γ · ((γ:ℂ) − w)⁻¹`, with `r γ` the residue of `ζ′/ζ` at the
event `line γ`.

**Why it matters.** The 3D-mode resolvent trace computes the explicit-formula object directly — zero
order = event weight = spectral multiplicity. The identity reading at the analytic level: the trace
formulas coincide, not just the locations.

### `limit_dominance` — `RequestProject/LimitDominance.lean:38`
**Proves.** A Hurwitz-type principle: if holomorphic `Fₙ → f` locally uniformly, `f(z₀) = 0`, and `f`
is not identically zero near `z₀`, then for every `ε > 0` the stages eventually have a zero within
`ε` of `z₀`.

**Why it matters.** Shannon projection dominance: the limit cannot manufacture a zero the stages
lack. Every chart zero is sourced by finite-stage features — the limiting process adds no spurious
zeros.

---

## 1D-correlation (coincidence) reading — evidence dossier

### `carrier_scale_compensation_S` — `RequestProject/CarrierScaleCompensation.lean:979`
**Proves.** `N_{π/3}(e^t) − N_1(e^t) = S(t)`, where `S(t) := zeroEventCount(t) − 1 − θ(t)/π`; the two
sides are the native-scale event count and the unit-scale `1 + θ/π`.

**Why it matters.** Exhibits `S(t)` not as a mysterious analytic remainder but as the gap between two
registrations of one arithmetic procession — the chart's smooth term and the carrier's event count,
one dataset read at two scales.

### `hpDimension_eq_registration` — `RequestProject/HilbertPolya.lean:124`
**Proves.** `card (WindowIndex T) = 1 + θ(T)/π + S_mult(T)` — the HP operator's dimension read off
the chart's own count formula.

**Why it matters.** The registration identity: the eigenstate count and the chart's zero-count are
the same number because the ledger says so. It binds approximate 1D data, with multiplicity, to the
exact 3D spectral cardinality.

### `no_radial_drift_on_helix` — `RequestProject/SourceHolonomy.lean:1163`
**Proves.** `‖exp(−c(½+y₁i))‖ = ‖exp(−c(½+y₂i))‖` for all `c, y₁, y₂` — the Euler-factor phasor's
radius depends only on `Re = ½`, not on height.

**Why it matters.** A frozen radius makes the height→circle map a faithful re-coordinatization, not a
lossy squash — all distinguishing information lives in the phase, which the ledger keeps.

### `midpoint_entry_on_circle` — `RequestProject/SourceHolonomy.lean:1171`
**Proves.** `‖1 − (½+yi)⁻¹‖ = 1` for all `y` — the Cayley ledger entry lands on the unit circle
(equivalently, the source has real part `½`).

**Why it matters.** Every helix height charts to an on-circle entry, so the ledger records
line-events as circle-points — the placement behind the projection's injectivity and Li-positivity.

### `record_bijective` — `RequestProject/RoundTrip.lean:156`
**Proves.** `record f = (height, (radial, phase))` is a bijection `Fiber → ℝ × (ℝ×ℝ)`, with the
explicit inverse `reconstruct`.

**Why it matters.** The loss ledger made literal: the projection drops phase and radius, but once
they are booked in the ledger the fiber reconstructs exactly — the collapse never counterfeits.

### `pipeline_midpoint_iff` — `RequestProject/RoundTrip.lean:307`
**Proves.** `pipeline x = ½ ↔ x = ½`, for the end-to-end 3D→height→encode→1D map
`pipeline = log ∘ exp ∘ project ∘ coneFiber`.

**Why it matters.** Riemann's Fold: the readout is `½` exactly when the retained 3D coordinate is —
the critical-line address survives projection intact, and only the midpoint maps there.

### `faithful_projection_zeta` — `RequestProject/Faithfulness.lean:159`
**Proves.** For all `γ`: `(completedRiemannZeta (½+γi)).im = 0`, and
`Feta γ = 0 ↔ riemannZeta (½+γi) = 0`.

**Why it matters.** The projected fiber vanishes exactly at, and only at, the genuine on-line zeros —
the collapse neither hides a zero nor manufactures one on the line.

### `chartZero_iff_eigenheight` — `RequestProject/HilbertPolya.lean:78`
**Proves.** For `0 < γ ≤ T`, `riemannZeta (line γ) = 0 ↔ ∃ p : WindowIndex T, p.1.1 = γ`.

**Why it matters.** The one-for-one coincidence: window by window, the chart's zero-readings and the
operator's eigenheights are in exact bijection — a proven correspondence, not an asserted identity.

### `residue_eq_Smult_jump` — `RequestProject/ResidueJump.lean:735`
**Proves.** For `γ > 0`: `(s − line γ)·(ζ′/ζ)(s) → eventOrder γ` as `s → line γ`, and
`HasJump S_mult γ (eventOrder γ)` — no simplicity hypothesis.

**Why it matters.** residue = order = ledger-jump, with multiplicity. The registration's
discontinuities carry the exact multiplicities the log-derivative residues do — chart and carrier
counts agree number-for-number.

### `euler_maclaurin_dirichlet` — `RequestProject/EulerMaclaurinDirichlet.lean:1018`
**Proves.** For `0 < Re s < 1`, `s ≠ 1`: `‖S(s,N) − ζ(s) − N^{1−s}/(1−s)‖ ≤ C·N^{−Re s}` for all
`N ≥ 2`, with `C` independent of `N`.

**Why it matters.** A finite Dirichlet-sum computation plus the boundary correction approximates `ζ`
in the strip with error uniform in the truncation — the quantitative backbone of the chart readout.

### `transfer_tendsto` — `RequestProject/TransferContinuation.lean:73`
**Proves.** If `‖Σ_{k<n} a k‖ ≤ C·n^θ` (`θ ≥ 0`), then `Σ a n·(n+1)^{−s}` converges for `Re s > θ`
(summation by parts).

**Why it matters.** A polynomial bound on the primitive continues the Dirichlet series past the
trivial abscissa — the existence of the readout limit from a growth estimate alone, with no appeal to
zero locations.

### `limit_zero_of_stage_accumulation` — `RequestProject/ExportAdapter.lean:33`
**Proves.** For a `MidpointCascade`, if stage zeros accumulate at `z` then `xiSection z = 0` (where
`xiSection z = riemannXi(½ + iz)`).

**Why it matters.** The Shannon-cascade converse: a zero accumulating across the finite stages is a
zero of the limit — the collapse does not counterfeit features.

### `S_jump_detects_event` — `RequestProject/ResidueJump.lean:486`
**Proves.** For `γ > 0`, `HasJump S γ 1 ↔ riemannZeta (line γ) = 0`.

**Why it matters.** `S(t)` is a crossing detector: its unit jumps are exactly the on-line zeros —
detecting a zero and detecting an `S`-jump are the same act.

### `count_hasJump_iff_S_hasJump` — `RequestProject/ResidueJump.lean:129`
**Proves.** `HasJump (zeroEventCount) γ j ↔ HasJump S γ j` — the difference `S − count = −1 − θ/π` is
continuous, so it contributes no jumps.

**Why it matters.** All discontinuity lives in `S`, none in the smooth clock `θ/π` — `S` is the exact
jump-carrier of the zero-count.

### `radial_lost` — `RequestProject/RoundTrip.lean:242`
**Proves.** There exist fibers `f₁, f₂` with `radial f₁ ≠ radial f₂` and `realize f₁ ≠ realize f₂`
but `geomProj f₁ = geomProj f₂`.

**Why it matters.** The ledger's necessity: without booking the radial channel the geometric
projection is non-injective — proof that the ledger does real work, so the faithfulness results are
non-trivial.

### `projection_bijective_loss_ledger` — `RequestProject/SourceHolonomy.lean:1203`
**Proves.** `y ↦ 1 − (½+yi)⁻¹` is injective on `ℝ`.

**Why it matters.** The chart chain height → midpoint → Cayley entry loses and invents nothing —
distinct helix events write distinct ledger entries; the data-processing inequality made literal for
the projection.

### `native_identification'` — `RequestProject/CarrierScaleCompensation.lean:935`
**Proves.** `N_{π/3}(e^t) = (zeroEventCount t : ℝ)` — the π/3-native count equals the number of
on-line zero ordinates in `(0, t]`.

**Why it matters.** Pins the native registration's event channel to the true zero count — one zero
per completed π/3 cell — so `S(t)` computed from `N_{π/3}` tracks the genuine procession of zeros.

### `windowedDiffResolvent_tendsto` — `RequestProject/DifferencedResolvent.lean:298`
**Proves.** For every `w`, the windowed differenced-resolvent trace
`T ↦ ∑_{γ ≤ T} m_γ·((γ−w)⁻¹ − γ⁻¹)` converges as `T → ∞` to the absolutely-convergent
`diffResolvent w`.

**Why it matters.** The chart-side resolvent limit exists as an honest `T → ∞` object — the analytic
device through which the absorption/resonance-at-the-zeros picture is realized, unconditionally.
