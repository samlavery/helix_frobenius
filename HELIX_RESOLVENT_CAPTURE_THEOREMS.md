# Helix Resolvent-Capture — theorem catalog

This document catalogs the Riemann/GRH **capstone** formalized in
`RequestProject/HelixResolventCapture.lean` (a Hilbert–Pólya-style resolvent-trace
construction), together with the two **evidence dossiers** that support it. It is written
for a mathematician who wants to check each English claim against the Lean it describes.
Every plain-English line below is calibrated to be **no stronger** than the Lean statement
it names.

## What is and is not proved here

Read the structure carefully — it is an **honest conditional** with two independent readings,
not a claim that RH or GRH is proved outright.

- **RH follows from GRH, unconditionally.** `RH_of_GRH_Trivial_Char`
  (`RequestProject/HelixResolventCapture.lean:528`) proves: GRH for the trivial (mod-1)
  Dirichlet character implies Mathlib's `RiemannHypothesis`. The proof is unconditional — it
  identifies the mod-1 L-function with `riemannZeta` via Mathlib's `LFunction_modOne_eq` and
  uses Mathlib's out-of-strip facts (`Re ≥ 1` non-vanishing; the completed-ζ functional
  equation for the trivial zeros). This is the "`rh_from_grh`" hinge.
- **Self-adjointness is discharged unconditionally.** It is **not** one of the hypotheses. The
  von Neumann operator's symmetry rides on the compiled theorem
  `UnconditionalFrobenius.vonNeumannOp_isSymmetric`, and von Neumann reality
  (`spectral_cancellation_on_real_axis`) places every 3D crossing on the critical line with no
  hypothesis about where the zeros lie.
- **The only conditional inputs are two named "reading" hypotheses**, one per Hilbert–Pólya
  reading. Neither is proved; each is stated once and asserted by no one, left for the
  community to adjudicate. The two are **genuinely distinct propositions**, differing by which
  zero is treated as *primary*:
  - `ThreeD_crossings_are_real_zeros` — **`3D-ZERO-REAL`** (strong HP, identity): the 3D zero is
    primary; every nontrivial zero is a von Neumann crossing at *some* real height `γ` — the
    resolvent `1/specBchan γ ρ` resonates at the 3D zero. `HelixResolventCapture.lean:608`.
  - `OneD_zeta_zero_correlated` — **`1D-ZERO-EXCLUSIVE-REAL`** (weak HP, correlation): agnostic
    about the primary — a per-zero **disjunction**, *3D-primary* (resonance at the 3D zero) **or**
    *1D-primary* (resonance at the 1D ordinate, carrying the eigenstate↔ordinate correspondence
    `γ = ρ.im`). `HelixResolventCapture.lean:625`.
  They are logically equivalent (each `⟺ Re ρ = ½`, since a `specBchan` kernel exists only at
  `γ = Im ρ` with `Re ρ = ½`) but **not the same statement**: the weak reading routes through
  whichever zero is chosen as realest and *proves* the correspondence in its 1D branch.
- **Each reading's GRH depends on a conjunction `(unconditional evidence ∧ that one
  conditional)`.** The evidence half is a theorem; the conditional half is the open hypothesis.
- **The two evidence dossiers are each proved unconditionally** — `threeDRealEvidence`
  (`:723`) and `oneDCorrelationEvidence` (`:748`) inhabit big conjunctions of already-compiled
  supporting facts. Their inhabitation certifies each conjunct is a theorem, not a hypothesis;
  they are evidence *for* a reading, never a proof *of* it.
- **Axiom footprint.** Every named theorem below has axiom footprint exactly
  `{propext, Classical.choice, Quot.sound}` (Lean/Mathlib standard) — no `sorry`, no extra
  axioms (the file ends with `#print axioms` checks on the capstone declarations).

Nothing in this file claims RH or GRH is proved. What is proved is: (a) RH-given-GRH-for-the-
trivial-character, unconditionally; (b) the self-adjoint spectral machinery, unconditionally;
(c) the two evidence dossiers, unconditionally; and (d) that, *given* one reading-hypothesis,
its dossier's conjunction yields GRH and hence RH.

---

## The capstone theorems

All in `RequestProject/HelixResolventCapture.lean`. `χ₁` denotes a Dirichlet character mod 1
(the trivial character, whose L-function is `riemannZeta`).

| Theorem | Location | What it proves |
|---|---|---|
| `RH_of_GRH_Trivial_Char` | `RequestProject/HelixResolventCapture.lean:528` | **Unconditional `rh_from_grh`.** For the mod-1 character `χ₁`, `GRHSpectral.GRH χ₁` (every nontrivial-strip zero of its L-function has `Re = ½`) implies Mathlib's `RiemannHypothesis`. Uses `LFunction_modOne_eq` (= ζ) and Mathlib's out-of-strip non-vanishing + functional equation. No operator, no reading-hypothesis. |
| `ThreeD_crossings_are_real_zeros` | `RequestProject/HelixResolventCapture.lean:608` | **A named hypothesis (`def`), the `3D-ZERO-REAL` / strong-HP reading — NOT proved.** The 3D zero is primary: for every nontrivial zero `ρ` there is a real height `γ` and nonzero `ψ` with `specOp (vonNeumannOp γ) ρ ψ = 0` — `ρ` sits in the kernel of the self-adjoint generator at *some* real height (equivalently the resolvent `1/specBchan γ ρ` resonates at the 3D zero). |
| `OneD_zeta_zero_correlated` | `RequestProject/HelixResolventCapture.lean:625` | **A named hypothesis (`def`), the `1D-ZERO-EXCLUSIVE-REAL` / weak-HP reading — NOT proved.** A per-zero **disjunction** over the primary choice: *3D-primary* (`∃ γ ψ≠0, specOp (vonNeumannOp γ) ρ ψ = 0`) **or** *1D-primary* (`∃ γ ψ≠0, specOp (vonNeumannOp γ) ρ ψ = 0 ∧ γ = ρ.im`), the 1D branch carrying the eigenstate↔ordinate correspondence `γ = ρ.im`. Genuinely distinct from (though logically equivalent to) the strong reading. |
| `grh_of_resolvant_trace_3D_real` | `RequestProject/HelixResolventCapture.lean:639` | From the conjunction `ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ₁`, deduces `GRHSpectral.GRH χ₁`. Self-adjointness is discharged internally (`vonNeumannOp_isSymmetric` + von Neumann reality); the only real input is the reading-hypothesis conjunct. |
| `grh_of_resolvant_trace_1D_correlation` | `RequestProject/HelixResolventCapture.lean:652` | From `OneDCorrelationEvidence ∧ OneD_zeta_zero_correlated χ₁`, deduces `GRHSpectral.GRH χ₁`. Case-splits on the primary choice: the 3D-primary branch resonates at the 3D zero, the 1D-primary branch at the 1D ordinate (`γ = ρ.im`); both close by the same unconditional von Neumann reality. |
| `RH_of_resolvant_trace_3D_real` | `RequestProject/HelixResolventCapture.lean:662` | Composition `RH_of_GRH_Trivial_Char ∘ grh_of_resolvant_trace_3D_real`: `ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ₁` ⟹ `RiemannHypothesis`. |
| `RH_of_resolvant_trace_1D_correlation` | `RequestProject/HelixResolventCapture.lean:669` | Composition for the correlation reading: `OneDCorrelationEvidence ∧ OneD_zeta_zero_correlated χ₁` ⟹ `RiemannHypothesis`. |
| `threeDRealEvidence` | `RequestProject/HelixResolventCapture.lean:746` | **Proves the 3D-real dossier unconditionally.** Inhabits `ThreeDRealEvidence`, the 16-fold conjunction of the identity-reading supporting facts (listed below). Evidence *for* the identity reading, not a proof of it. |
| `oneDCorrelationEvidence` | `RequestProject/HelixResolventCapture.lean:771` | **Proves the 1D-correlation dossier unconditionally.** Inhabits `OneDCorrelationEvidence`, the 18-fold conjunction of the correlation-reading supporting facts (listed below). |
| `threeD_real_case` | `RequestProject/HelixResolventCapture.lean:801` | Bundles the proven `threeDRealEvidence` with the conjunction-GRH proof `∀ χ₁, ThreeDRealEvidence ∧ ThreeD_crossings_are_real_zeros χ₁ → GRHSpectral.GRH χ₁`. The left half is a theorem; the right half's second conjunct is the open hypothesis. |
| `oneD_correlation_case` | `RequestProject/HelixResolventCapture.lean:813` | Bundles the proven `oneDCorrelationEvidence` with `∀ χ₁, OneDCorrelationEvidence ∧ OneD_zeta_zero_correlated χ₁ → GRHSpectral.GRH χ₁`. |

---

## 3D-real (identity) reading — evidence dossier

`ThreeDRealEvidence` (abbrev at `RequestProject/HelixResolventCapture.lean:67`) is the
conjunction of the 16 facts below, proved unconditionally by `threeDRealEvidence`
(`:723`), in this order. Each bullet gives the witnessing theorem, its source location, and a
calibrated reading of what it states.

- `vonNeumannOp_isSymmetric` — `RequestProject/ClosedForm.lean:1688` — **Self-adjointness, discharged unconditionally (called out specially).** For every real `γ`, the von Neumann operator `vonNeumannOp γ` is symmetric (`IsSymmetric`): multiplication by the real scalar `γ` is symmetric for the standard inner product, so its spectrum is real. This is the fact that makes self-adjointness a *theorem*, not a hypothesis of the capstone.
- `threeD_exhaustive` — `RequestProject/SourceHolonomy.lean:778` — For every function `E : ℂ → ℂ`, the predicate `ThreeDExhaustive E` holds: heights are weld-fixed, so every 3D zero event is a source — in 3D there is nowhere else for a zero to occur.
- `threeD_metric_no_zeros` — `RequestProject/SourceHolonomy.lean:784` — For every finitely-supported state `F : ℕ →₀ ℂ`, the cup norm `Cup F F = 0 ↔ F = 0`: the 3D metric vanishes only on the zero state; vanishing is a property of readings, never of states.
- `windFromPrimes_mul` — `RequestProject/Origination.lean:137` — FTA-multiplicativity of the winding: for `m, n ≠ 0`, `windFromPrimes (m*n) = windFromPrimes m * windFromPrimes n` (from `Nat.factorization_mul`). The helix carries no information beyond the prime factorization.
- `fiber_accumulates_to_L` — `RequestProject/Faithfulness.lean:147` — For a non-principal character `χ` (`χ ≠ 1`) and any `s` with `Re s > 0`, the partial sums of the carrier-riding phasors `finiteCarrier χ s` converge to `LFunction χ s` — across the entire critical strip, not just the `Re s > 1` absolute-convergence region. (The "phasor bank is summable"/Feynman's Quiver.)
- `heights_distinct` — `RequestProject/NoDoubleCancellation.lean:56` — Distinct sites carry distinct eigen-heights: for `m ≠ n`, `logGen m ≠ logGen n` (`logGen` injective) — the phasor-version of unique factorization.
- `cancellation_modes_subsingleton` — `RequestProject/NoDoubleCancellation.lean:94` — "No split focus": at any spectral parameter `s`, the set of basis modes in the kernel of `specOp Aχ s` is a subsingleton (at most one mode cancels).
- `localPoly_reciprocal` — `RequestProject/FiniteWeightFiber.lean:87` — Per-place functional equation: for a finite-weight fiber `W` and `X ≠ 0`, `W.localPoly X = (-X)^{|ι|} · W.localPoly X⁻¹` — the local numerator is self-reciprocal (weights closed under `λ ↦ λ⁻¹`, product 1). One of "Deligne's Pairs".
- `frobeniusBlock_det_one` — `RequestProject/FrobeniusSimilitude.lean:167` — For every real `y` and `n : ℕ`, `(frobeniusBlock y n).det = 1`: the chiral Frobenius block `diag(z, z̄)` has `det = |z|² = 1` (volume/orientation-preserving). Deligne's Pairs, Frobenius-conjugate `det = 1`.
- `fiber_det_one` — `RequestProject/FiniteWeightFiber.lean:62` — For every finite-weight fiber `W`, `∏ i, W.weight i = 1`: the weight/modulus ledger — the dual involution pairs `λᵢ·λ_{dual i} = 1`, purity at the finite places.
- `hpOperator_isHermitian` — `RequestProject/HilbertPolya.lean:54` — For every `T : ℝ`, the Hilbert–Pólya operator `hpOperator T` is Hermitian (`IsHermitian`): the ledger diagonal has real ordinates. Self-adjointness by construction.
- `finrank_modeSpace` — `RequestProject/GradedModeDictionary.lean:99` — For every `γ : ℝ`, `Module.finrank ℂ (ModeSpace γ) = eventOrder γ`: the graded mode space's dimension equals the event's multiplicity (0 at a non-event).
- `focal_residual_zero_iff_L_zero` — `RequestProject/FocalResidualVanishes.lean:67` — For a Dirichlet character `χ` and `Z : ℝ`, the normalized cell focal residual `Dcell χ Z = 0 ↔ LFunction χ (reprPoint χ Z) = 0`: exact harmonic vanishing — the focal residual vanishes exactly when the represented L-value does.
- `eigenheight_is_exact_vanishing` — `RequestProject/HilbertPolya.lean:71` — For any window index `p : WindowIndex T`, `riemannZeta (line p.1.1) = 0`: each eigenheight marks a genuine, *exact* carrier event (`ζ(½+iγ) = 0` on the nose, no approximation).
- `gradedResolventTrace_eq_residue_sum` — `RequestProject/GradedModeDictionary.lean:326` — Under a residue assignment `r` of `ζ′/ζ` at the events of the window (each `(s−line γ)·logDeriv ζ → r γ`), and `w` off the event set, `gradedResolventTrace w T = ∑_{γ ∈ eventWindow T} r γ · (γ − w)⁻¹`: the operator resolvent trace on the graded 3D modes equals the log-derivative residue sum.
- `limit_dominance` — `RequestProject/LimitDominance.lean:38` — Existence form of limit dominance: if holomorphic `Fₙ → f` locally uniformly on an open `U`, `f(z₀)=0`, and `f` is not identically zero near `z₀`, then for every `ε>0` the stages eventually have a zero within `ε` of `z₀` (zeros of the limit are limits of zeros). "Shannon Projection Dominance."

---

## 1D-correlation (coincidence) reading — evidence dossier

`OneDCorrelationEvidence` (abbrev at `RequestProject/HelixResolventCapture.lean:109`) is the
conjunction of the 18 facts below, proved unconditionally by `oneDCorrelationEvidence`
(`:748`), in this order.

- `carrier_scale_compensation_S` — `RequestProject/CarrierScaleCompensation.lean:979` — For every `t : ℝ`, `N_{π/3}(e^t) − N_1(e^t) = S(t)`: the π/3-native count minus the unit-scale count equals exactly the term the 1D chart calls `S(t)` — the unit chart's unavoidable correction for never re-synchronizing with the native π/3 registration. Independent of where any zero lies.
- `hpDimension_eq_registration` — `RequestProject/HilbertPolya.lean:124` — For every `T : ℝ`, `(card (WindowIndex T) : ℝ) = 1 + θ(T)/π + S_mult(T)`: the Hilbert–Pólya operator's dimension through height `T`, read off the 1D chart by the registration identity (deferent clock `θ/π` + multiplicity ledger `S_mult`). The S(t) binding.
- `no_radial_drift_on_helix` — `RequestProject/SourceHolonomy.lean:1163` — For all `c, y₁, y₂ : ℝ`, `‖exp(−c(½+y₁i))‖ = ‖exp(−c(½+y₂i))‖`: on the carrier every Euler-factor phasor has a frozen radius — no radial degree of freedom.
- `midpoint_entry_on_circle` — `RequestProject/SourceHolonomy.lean:1171` — For every `y : ℝ`, `‖1 − (½ + y·i)⁻¹‖ = 1`: every helix height charts to an on-circle ledger entry.
- `record_bijective` — `RequestProject/RoundTrip.lean:156` — `Function.Bijective ConeProjection.record`: the reconstruction/round-trip map is a bijection (the collapse never counterfeits — Shannon).
- `pipeline_midpoint_iff` — `RequestProject/RoundTrip.lean:307` — For every `x : ℝ`, `ConeProjection.pipeline x = ½ ↔ x = ½`: "Riemann's Fold" — the full faithful pipeline lands on the real axis exactly when its retained coordinate does; the real axis is preserved across the crossed dimensions.
- `faithful_projection_zeta` — `RequestProject/Faithfulness.lean:159` — For every `γ : ℝ`, `(completedRiemannZeta (½ + γ·i)).im = 0` **and** `EtaTrivial.Feta γ = 0 ↔ riemannZeta (½ + γ·i) = 0`: the completed object is real on the critical line and the projected fiber vanishes exactly at the actual zeros.
- `chartZero_iff_eigenheight` — `RequestProject/HilbertPolya.lean:78` — For `0 < γ ≤ T`, `riemannZeta (line γ) = 0 ↔ ∃ p : WindowIndex T, p.1.1 = γ`: within the window the 1D chart reads a zero at a height iff an eigenstate sits there — the one-for-one coincidence clause.
- `residue_eq_Smult_jump` — `RequestProject/ResidueJump.lean:735` — For `γ > 0`: `(s − line γ)·logDeriv ζ → (eventOrder γ : ℂ)` as `s → line γ`, **and** `HasJump Smult γ (eventOrder γ)`: the residue of `ζ′/ζ` equals the multiplicity equals the jump of `S_mult`, no simplicity hypothesis.
- `euler_maclaurin_dirichlet` — `RequestProject/EulerMaclaurinDirichlet.lean:1018` — For `s` with `0 < Re s < 1`, `s ≠ 1`, there is `C > 0` with `‖S(s,N) − ζ(s) − N^{1−s}/(1−s)‖ ≤ C·N^{−Re s}` for all `N ≥ 2`: the Euler–Maclaurin approximation of the Dirichlet partial sums, `C` independent of `N`. The 1D infinite-continuation approximation.
- `transfer_tendsto` — `RequestProject/TransferContinuation.lean:73` — For coefficients `a` with `‖∑_{k<n} a k‖ ≤ C·n^θ` (`θ ≥ 0`) and `Re s > θ`, the partial sums of `∑ a n · (n+1)^{−s}` converge: a polynomially-bounded primitive continues the Dirichlet series. Faithful transport (local correlation).
- `limit_zero_of_stage_accumulation` — `RequestProject/ExportAdapter.lean:33` — For a midpoint cascade `C`, if every neighborhood of `z` eventually contains a stage zero, then `xiSection z = 0`: the Shannon-cascade converse — an accumulation point of stage features is a feature of the limit.
- `S_jump_detects_event` — `RequestProject/ResidueJump.lean:486` — For `γ > 0`, `HasJump S γ 1 ↔ riemannZeta (line γ) = 0`: `S` jumps by one at `γ` exactly when `γ` is a zero ordinate — S(t) detects every crossing.
- `count_hasJump_iff_S_hasJump` — `RequestProject/ResidueJump.lean:129` — For all `γ, j : ℝ`, `HasJump (fun t => (zeroEventCount t : ℝ)) γ j ↔ HasJump S γ j`: the zero-count and `S` have exactly the same jumps (the smooth clock term is continuous, so every count-jump belongs entirely to `S`).
- `radial_lost` — `RequestProject/RoundTrip.lean:242` — There exist fibers `f₁, f₂` with `radial f₁ ≠ radial f₂`, `realize f₁ ≠ realize f₂`, yet `geomProj f₁ = geomProj f₂`: dropping the radius (without the ledger) collapses genuinely distinct realized points — the loss ledger.
- `projection_bijective_loss_ledger` — `RequestProject/SourceHolonomy.lean:1203` — `Function.Injective (fun y : ℝ => 1 − (½ + y·i)⁻¹)`: the chart chain height → midpoint → Cayley entry is injective — distinct helix events write distinct ledger entries; the projection loses and invents nothing.
- `native_identification'` — `RequestProject/CarrierScaleCompensation.lean:935` — For every `t : ℝ`, `N_{π/3}(e^t) = (zeroEventCount t : ℝ)`: the π/3-native count equals the zero-event count (functor form). *(Corrected location: the primed declaration is at line 935; line 645 holds the unprimed `native_identification`.)*
- `windowedDiffResolvent_tendsto` — `RequestProject/DifferencedResolvent.lean:298` — For every `w : ℂ`, the windowed trace `T ↦ windowedTrace (fun γ => (γ−w)⁻¹ − γ⁻¹) T` tends to `diffResolvent w` as `T → ∞`: the differenced resolvent-trace `T→∞` limit exists (the chart resolvent limit), unconditional.
