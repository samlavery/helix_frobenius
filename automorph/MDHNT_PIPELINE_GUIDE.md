# MDHNT — the operating guide

*What the infrastructure is, the order it runs in, why the order is legal, how it verifies itself,
and how it fails.*

Mined from the full corpus: `universal.tex` (8618 lines), `hodge_companion.tex` (4406),
`grh_companion.tex` (2130), `erdos377_partial.tex` (2154), the Erdős cluster, and 43 markdown
working notes. Every claim is tagged **[proven]**, **[measured]**, **[discipline]**,
**[borrowed]** or **[orphan]**.

> **Register warning.** Several things this program treated as house instruments are in the
> literature. They are marked **[borrowed]** and attributed in §12. The gate ran late; that is
> itself a lesson (§11.6).

---

## 0. The analogy, and where it stops

Langlands decrees a **common home**: lift everything to automorphic representations and
relationships become morphisms in one category. It is the great intermediate representation of
mathematics — but a *correspondence*, not a computation surface.

MDHNT's bet is a common home you can **run things on**.

| Langlands | MDHNT |
|---|---|
| lift to automorphic rep | lift to a phasor configuration on the carrier |
| functoriality | rail maps; transfer = a parallel-dimension clock |
| the correspondence | the defect ledger of an alignment |
| local–global | per-rail ledgers composing to a joint ledger |
| a correspondence | a computation with an exact error term |

**Where it stops.** Langlands is a web of conjectures with deep theorems attached. MDHNT is a
normalization system with a universal theorem attached and an application record that is honest
but modest. Across a nine-problem Erdős campaign it **closed none of them** (§13).

---

## 1. The order — and the correction

**User-facing (five stages)** — `mdhnt_for_dummies.tex:64`

1. **Lift (harmonize)** — homogenize onto the carrier as a phasor configuration: magnitude law,
   phase law, harmonic scale.
2. **Choose a geometry** — the carrier is a parameter, not a commitment.
3. **Load multiple rails** — as many objects as you want, on parallel rails.
4. **Align (register)** — the core primitive; read the integer-valued **defect ledger**.
5. **Extract** — project back with the loss ledger making extraction exact.

**Internal (seven stages)** — `universal.tex:3640`
```
lift → analyze → adapt → normalize → run → project → read
```
with adapter hierarchy `A_global → A_carrier → A_clock → A_fiber` (global first, fiber last, each
carrying its inverse into the ledger).

**Mapping:** *Lift* = lift. *Geometry + rails* = analyze + adapt + normalize. *Align* = run.
*Extract* = project + read.

### 1.1 CORRECTION — it is not one pipeline

An earlier version of this guide claimed a single pipeline. **That is false.** The Hodge side
runs the same spine but inserts **three stages with no main-pipeline counterpart**, and they are
typed objects, not prose (`hodge_companion.tex`). See §5.

---

## 2. Why the order is legal — the one condition

> **Every stage keeps a ledger, and ledgers compose.**

- The lift is a **bijection with its loss ledger** **[proven]**
- Alignment defects are **exact and integer-valued** **[proven]**
- Extraction is **invertible-with-ledger**; readout equality is never state equality **[proven]**
- Structural relations transport **functorially** **[proven]**

**The test for any new brick: if you cannot write the ledger for a stage, that stage is not legal.**

**The ledger's governing principle** (`universal.tex:469` glossary): *phase and radius may
decouple dynamically, but not informationally.* Channels evolve independently; the ledger books
both. That sentence is what makes "ledgers compose" mean something.

**Necessity witness** — prove your ledger does real work: `radial_lost` exhibits two fibers with
different radii but *identical geometric projection*, so without the radial channel the projection
is non-injective. **A loss ledger with no necessity witness is unfalsifiable.** **[proven]**

---

## 3. The five laws

1. **Structure determines the lift** — read the structural presentation, **never the 1D readout**.
   No finite structural presentation ⟹ no lift.
2. **Identity is preserved at every stage.** Adapters change realization, never the source.
3. **Run only at complete native cells, after harmonization.** Nothing measured mid-cell. *This is
   what makes closure exact rather than a cutoff limit.*
4. **Projection is always ledgered.**
5. **The loop closes through obstruction feedback.**

Law 1 is most often violated; law 3's violation is hardest to detect.

**Synthesis totality, not existential adapter** — state `∀W: Struct(W) ⟹ (C,ω,τ,L) = Synth(Struct(W))`,
not `∀W ∃A_W`. Finite structure is what makes `Synth` total, so simultaneous synchronization is
the **common refinement** of individually synthesized systems — constructed, not posited. **[proven]**

---

## 4. The ontology, and its formal counterpart

The glossary at `universal.tex:469` maps every term to a Lean declaration. **All ten mappings
verified to exist.**

- **carrier** — the layer between helix geometry and fiber; represents the 0→∞ number line, scaled
  for harmonic alignment. **Carrier unit scale = π/3** in 3D (1 in the chart).
- **fiber** — the function itself: local Satake/Weil–Deligne data. Formally
  `FiniteWeightFiber ι`: unit-modulus weights, an involution `dual` with
  `weight(dual i) = weight(i)⁻¹`, and `dual i = i → weight i = 1` (*balanced determinant ledger*).
  **⚠ Temperedness is an axiom of the structure, not a theorem about it** — every theorem over
  `FiniteWeightFiber` is conditional on inhabiting it, and the tower squeeze (§6) is the
  inhabitation argument.
- **bank** — the summed P/M/U phasors; 1D counterpart is the infinite L-series.
- **warp** — a *function*-based unit-modulus reparametrization. The reciprocal of a warp is a warp,
  so **there is no "inverse warp"**; removal is `WarpRemovalTransfer` (audited in
  `InverseWarpTransferAudit.lean`).
- **carrier scale** — a harmonic *constant*. Not a warp.
- **dwell** — the opposite of warp: packs multiple crossings into one carrier unit. **[borrowed]**
  — described in-file as the native form of Altuğ's Σ(); also the classical occupancy/extreme-value
  quantile.
- **clock** — four types: self-duality (μ₂), completion (two-clock), ramification,
  **vanishing-adjustment**. The fourth is called "the layer that turns Satake data into vanishing"
  and is an **[orphan]** — never invoked in any proof.
- **focal cancellation** — a zero: the **non-DC** bank balances to zero centroid. The DC mode is
  explicitly excluded.
- **weld** — helix/anti-helix crossing at Re s = ½, det-one Frobenius similitude. *Vocabulary note:
  house rule bans "weld" in prose; say theta transformation law / Poisson summation.*

`CarrierState3D p r` is a point in ℝ³ plus an ordinate, constrained to lie on the helix curve
γ(p,r,·) — the constraint discharged by `rfl`.

---

## 5. The Hodge extension — three stages the main pipeline lacks

### X1 — The realization interface (between *lift* and *load*)
**`FaithfulRealization`**: a five-condition typed bridge from geometry into the bank — finite
support, distinct frequencies, correct rational structure, compatibility with extensions and
regulators, and **no kernel on the classes at issue**. Once one term is constructed, retention and
first-visible depth transport **automatically**. *"What is open per arithmetic landing" becomes a
single term, not a promise.* **[proven]**

**`PeriodRealization`** — the transcendental variant: replace rational amplitudes by rational
multiples of channel periods (rationality of *ratios*, not values). The misfit is itself a theorem:
if the height is irrational the rational-amplitude reading is **uninhabitable**. **[proven]**

### X2 — The rung ladder (a validation stage)
Climb rungs where the answer is **already a theorem**, consuming it as the recognition field:
ℚ[ℤ/n] → Artin motive of a cyclic field → Lefschetz H² → CM products → depth-one H¹ → NS(E×E) and
Shioda MW = E₈ → the period rung (Ceresa). *"What is new is the executed pipeline, one dimension
up."* So a failure is an **architecture** failure, not a mathematics failure. **[proven]**

Corollary move: **when the number-field version awaits a library, do the function-field version** —
on Shioda's extremal rational elliptic surface the height pairing *equals* the E₈ form exactly, no
analytic gap.

### X3 — The terminus factorization audit
Prove the factorization **exact** *and* each factor **independently necessary**. Retention ∧
Recognition ⟹ SourceExhaustion composes unconditionally; then recognition is *precisely* source
exhaustion on fired classes; then independence is witnessed by two dials — `phantomDial` (retention
fails) and `sourcelessDial` (recognition fails) — **which are the pre-registered falsifiers**, so
the register describes scenarios that genuinely exist. **[proven]**

**Type the circular route so it is inexpressible.** `ProjectorRecognition` carries the
correspondence's *algebraicity as a hypothesis field*, so a merely cohomological projector cannot
discharge it. **[proven]**

---

## 6. Instruments, by stage

### Lift
- **Harmonization** — read a projected function and let its nature name its settings.
  *Failure: unit-1 scale → FALSE NULL.* **[discipline]**
- **Dress an arbitrary step into a harmonic one with a fiber spin** — a spin μ = π/m − H converts
  any native spacing (log 7, √5, an irrational Satake angle) onto a closing harmonic carrier
  without touching the object. **[proven]**
- **Convert an irrational phase to a root-of-unity twist via Ω(n)** — pass to the completely
  additive prime-count winding Θ(n) = (π/3)Ω(n); the carrier phase becomes β^Ω(n), and the cell
  closes by the classical Σ β^Ω(n) = o(X). **[proven]**

### Geometry and rails
- **The double-ended carrier** — reflection manufactures the functional equation a model lacks.
- **Restore a symmetry by doubling instead of proving it** — if r is not self-dual, double onto
  r ⊕ rᵛ; the weight system is closed under negation *by construction*. **[proven]**
- **Multi-rail loading** — strictly stronger than the scalar readout. **Readout-injectivity test:**
  for the F₂₁ degree-three Artin representation the two Frobenius classes have Gauss-period traces
  with equal real part but η ≠ η′, so a real 1D readout **provably cannot** separate 7A from 7B.
  Categorical failure, not smearing. **[proven]**
- **Parameter count, not degree, is the scalar readout's wall** — a degree-3 *one-parameter* object
  reads faithfully; a degree-4 *two-parameter* object degrades and **no scalar de-chirp repairs it**.
  **[measured]**

### Align — the signature move
- **Registration / the defect ledger.** `(chart count) = (native count) + (defect)`, defect
  integer-valued, monotone, non-negative. One unabsorbed unit costs **linear** growth, so
  **sublinear defect is already zero defect**. No intermediate regime. **[proven, machine-checked]**
- **Registration gaps compose by a cocycle law** — `S_{H,L} = S_{H,K} + S_{K,L}`, so you can route
  a hard chart-to-chart gap through a convenient intermediate. **Sharpening: π/3 is *not*
  load-bearing** — the whole π/m family registers identically; π/3 is chosen as sharpest. **[proven]**
- **The event-arc criterion** — can this chart register the event at all? An event is a sign flip,
  its mark the half turn −1 = e^{iπ}; scale H registers it only via `eventArcs H = {k ≥ 1 : e^{ikH} = −1}`.
  At π/3 the arcs are k ≡ 3 (mod 6); at scale 1 the set is **empty**.
  *Trap: monodromy is necessary but NOT sufficient — 2π closes in one cell yet its arc set is empty.*
  **[proven]**
- **The clock chart** — integrate in carrier time `dθ/π`, not `dt`:
  ```
  L(t) = N(t) − θ(t)/π − 1,   cell m = [g_m,g_{m+1}),  θ(g_m) = mπ
  r_m = ∫ L dθ/π = s_m + k − ½ − Σ τ_i,   B_N = Σ r_m
  ```
  **Free check every implementation should run:** `r_m + Στ_i + ½ = s_m + k = s_{m+1} + 1` in every
  cell. The ½ is mean-of-drift, an artifact of the trapezoid, never a property of the cell. **[proven]**
- **Subtract the continuous part to make jumps exact** — if S = N − const − (continuous clock) then
  S and N have identical jumps, giving `Res_ρ(f′/f) = m_ρ = ΔS^mult(γ)` with **no simplicity
  hypothesis**. **[proven]**
- **Lattice rigidity** — the ℤ[ζ₆] norm form has smallest nonzero value 1, so a quantity that
  provably lives on the lattice and measures below norm 1 is **exactly zero**. A residual of 1e−12
  is a certificate. Kronecker one level up: modulus-one lattice value = a sixth root of unity
  exactly. **This is the bridge from computation to proof.** **[proven]**
- **Build the defect out of provably positive summands** — a global equality then forces per-term
  vanishing; no adversary hides a contribution in cross-term cancellation. **[proven]**
- **Identify at one sample, never at the trace** — prove pointwise kernel equality first; take the
  sum only after basiswise equality. Removes "maybe two errors cancelled". **[proven]**
- **Hermitian/anti-Hermitian split** — *compute* (don't postulate) `P_nd(H) = ½(H+H†)`; the global
  claim becomes a fixed-point equation holding **basiswise**. **[proven]**

### Extract
- **Projection bijection + loss ledger** — read first. 3D→2D drops the **radius** (Cayley→circle);
  2D→1D drops the **angle** (circle→strip). **[proven]**
- **Towers — climb with one ruler.** Rank-uniform instruments; *rank-uniformity is where limits
  come from.* If `ρ^r ≤ C` for **every** rung then ρ ≤ 1; with the inverse, ρ = 1 exactly — that
  **is** temperedness, and on the carrier it says the strand is a **helix, not a spiral**. **[proven]**
- **Grade the mode space by the local algebra** — take the event's mode space to be
  `C[X]/((X−ρ)^m)`, so `finrank` **is** the vanishing order and traces carry multiplicity linearly.
  **[proven]**
- **The exact gauge — move to the coordinate where the triangle inequality is lossless.** Represent
  `A(x) = (1/2πi)∫ M(u)x^{−u/2}du` where the integrand is *real magnitude × deterministic phase*;
  then `|A(x)| ≤ B_τ x^{−τ/2}` with `B_τ` **independent of x**, so `|∫g| ≤ ∫|g|` discards no
  arithmetic cancellation. Replaces a ~60-page oscillation estimate with one magnitude bound.
  *Fails when the phase is not deterministic in the chosen coordinate.* **[proven]**
- **Evaluate the oscillatory integral in closed form instead of estimating it** — insert the Mellin
  representation, Fubini, Taylor at the endpoint, evaluate each monomial as a Γ. DC-first at the
  level of the integral. **[proven]**
- **Free contour height equals free exponent** — taking the remainder's contour at any τ₁ > 0 gives
  arbitrary polynomial saving for no extra work. **[proven]**

---

## 6b. Two sorting instruments — where is the difficulty, really?

These decide *which chart* a difficulty lives in, before you spend effort on it.
Both at `universal.tex:6740` and `:6759`.

**CHART DEGREE — a decision procedure, not a quantity.** Given a difficulty that grows with
degree, state the governing gate in the 3D chart and **test it for rank-uniformity**. If the 3D
statement is the same statement at every rank, the degree-growth lives in the *projection*, not
the object. Checked here: per-rail conjugate-pair reality and the det-one ledger are the same
finite-multiset algebra at every rank (`fiber_det_one`, `localPoly_reciprocal`, Lean, for any
finite duality-stable multiset), and native-cell closure is the same geometric identity at every
rank, measured through GL(14). Everything that *does* grow with degree — the
Chandrasekharan–Narasimhan exponents, the $(d-1)/2d$ law, the smeared Sym¹³ reopening — is 1D.
**Fails when the 3D statement is not rank-uniform; the rank-uniformity check IS the instrument,
the assertion is not.** Falsifier in print: persistence of the Sym¹³ late-window slope alongside
exact 3D closure would be a measured chart/carrier divergence. **[measured + proven]**

**LEDGER TOLL — a sorting rule for open problems.** The 3D→2D→1D descent carries its loss ledger,
and fiber ↦ (ordinate; radius, angle) is a **proven bijection** (`record_bijective`). Therefore
**any input that only becomes open after the radius and angle channels are discarded is a
statement about the unledgered shadow** — a toll paid to the classical category, not a property of
the object. Applied to the two survivors of the niceness chain, it relocates the frontier: *"not
hard analysis at high degree — two reach/extinction statements about a projection that provably
discards nothing when its ledger is kept."* **Fails when a split leaves arithmetic on both sides;
the value is that one half becomes unconditionally free.** **[proven bijection + discipline]**

**THE LEDGER-SEAM SPLIT — the mechanism that makes the toll more than a slogan.**
`RequestProject/AxisPairing.lean`, 60 lines, splits the axis-reality gate exactly at the seam:
```
pairedBank K F  := Σ_{n∈F} (K n + conj(K n))
oddMode ε K K' F := Σ_{n∈F} (K n − ε·conj(K' n))
pairedBank_real        : (pairedBank K F).im = 0        -- every bank, every fiber, NO arithmetic
readout_decomposition  : Σ K n = (pairedBank + oddMode 1 K K)/2
fe_iff_oddMode_eq_zero : (Σ K n = ε·Σ conj(K' n)) ↔ oddMode ε K K' F = 0
```
So the standing wave's **reality is free**, and the entire arithmetic content of the axis
functional equation is the **extinction of one odd mode** — the genre this machinery is strongest
in. **[proven]**

**Meta-observation worth more than either instrument.** Across five version bumps of the clock
paper the *named arithmetic input moved three times*: cell closure → inverse-warp transfer (killed
by the neutrality control) → transfer exponent θ_W < κ/2 (proved) → grown exponent θᵉ_W < κ/2
(operative). **Each move was forced by a control, not by taste.** That is what a self-correcting
program looks like from the outside, and the version trail is the evidence.

## 6c. The formal layer — what is actually in Lean

Independently measured, not agent-reported:

- **6,366 theorems/lemmas** (4,766 `RequestProject`, 1,600 `staging_rp2`)
- **Zero custom axioms anywhere.** Consistent with the standing rule that the footprint stays
  `{propext, Classical.choice, Quot.sound}`.
- **121 of 567 files contain `sorry`** — but `staging_rp2` has only **two** (`HermitianResolventTrace`,
  `AllHelix`), so the scaffold is concentrated in `RequestProject`.
- `staging_rp2` is **not in the lakefile**; related `GlobalHelix*` modules do live in `RequestProject`.
  Treat it as parked infrastructure, not part of the build.

**GRH is a conclusion, never a hypothesis.** Every occurrence in `staging_rp2` has the shape
```
... (h : ResolventReceiver a χ T) : GRHSpectral.GRH χ
```
i.e. *capture ⟹ GRH*: exhibit a **self-adjoint** operator whose resolvent trace equals
$-L'/L(\tfrac12+i\cdot)$ and is regular off its spectrum, and GRH follows **by spectral reality
alone, no positivity**. The theorems are conditionals whose hypothesis is the hard part, and the
files say so in their own docstrings — `HelixMultiplicative.lean:34`: *"exactly why this is hard
and why it is the genuine GRH step"*; `:95`: *"is the open GRH content, not this."*

**This is the same shape as `FiniteWeightFiber`'s temperedness (§4), and it is the program's
characteristic pattern: the theorem is real, the hypothesis is the frontier, and inhabiting it is
a separate named job.** When reading any capstone here, ask first *what inhabits the hypothesis* —
the corpus is honest about this and the reader should hold it to the same standard.

⚠ **The corpus elsewhere flags the trap this pattern invites:** `vonNeumannOp γ = γ • id`
trivially has eigenvalue γ, so it *realizes* each ordinate as an eigenvalue of a hand-chosen
operator and **does not derive** reality from an independently given one. A real spectral proof
needs an operator defined independently of the zeros **plus** a proof its spectrum equals the zero
set. Do not read a construction as a derivation.

## 7. Verification and falsification instruments

These are the reason results here are checkable, and they are the most transferable part.

- **Precision-tracking as the identity test** — an identity's residual *tracks precision*
  (10⁻²⁹/10⁻⁴⁸/10⁻⁷⁹ at 30/50/80 digits); a model floor is digit-independent. Report the sweep,
  not a number. **[measured]**
- **Ablate every stage** — run the full stack and each stage removed. Every ablation floors at
  O(1)–O(100) while the full stack tracks precision. Load-bearing **measured, not argued**. **[measured]**
- **Two controls that fail on opposite gates** — build a control passing gate A and failing B, and
  another failing A. The gates are then separated by dedicated counterexample classes, not by
  argument. **[measured]**
- **Same-term-algebra control** — feed the identity a system with the *identical per-term algebra*
  but different coefficients. If the target closes at machine zero and the control fails by 10²,
  the identity is coefficient-sensitive and cannot be a termwise interchange. **[measured]**
- **Compile the non-discrimination theorem for your own device** — prove one stage closes any two
  residuals identically, so forcibility carries no information about the fiber. *Corollary
  enforced: forcible closure is the TRANSPORT half and is NEVER niceness evidence.* Corroborated:
  true anchor, detuned fiber, and random-angle fiber all force-close 30/30 at the float64 floor.
  **[proven]** — *the single most honest instrument in the corpus.*
- **Adversarial witness that passes the neutral layer and fails only at the conclusion** — build the
  maximally hostile object (a genuine spiral), show it passes the entire analytic payload verbatim,
  then show it violates the tower ceiling at the first rung. Unit modulus enters exactly once, as a
  conclusion. **[proven]**
- **Deliberately violate the method law to measure it** — keep the violating variant as a control.
  The sharp-window clip control manufactures resistant cells with exploding weights while the native
  run closes 30/30. *"The never-clip method law made measurable."* **[measured]**
- **Circular-shift null, not IID permutation** — for correlated sequences, IID overstates
  significance. A run-1 signal at p = 0.0355 under IID failed to replicate under circular shift.
  **[discipline]**
- **The sharp null** — a control that destroys **exactly one** property. Completely multiplicative
  Steinhaus phases keep the multiplicative skeleton and kill only the arithmetic. **[discipline]**
- **"A mechanism that would also make the null flat is an automatic fail (it proves too much)."**
- **Cross-cell independence check** — apply the weights that close cell k to cell k+1. If one weight
  vector closed everything, you fitted a global nuisance. **[measured]**
- **Read the window drift, never the global slope** — split into log-windows and report slope per
  window; pre-register what the drift must do. **[measured]**
- **Sensitivity test with teeth** — perturb any ingredient by 5% and show the answer moves off the
  target. An integer-landing claim without it is unfalsifiable. **[measured]**
- **Anchor-gate before verdict** — validate engines against exact anchors *before* any falsifier
  verdict. Two silent numerical bugs were found this way. **[discipline]**
- **Per-run calibration column** — calibrate every run to 1.00000 and carry it as a column;
  calibration ≠ 1 auto-flags contamination. **[discipline]**
- **The validation ladder** — run the pipeline on cases where the answer is known, **including at
  least one known negative**, before reporting the unknown. A ladder of same-sign cases lets a
  sign-blind bug survive. **[discipline]**
- **Design the instrument so one of its readings has a theorem-known answer** (built-in truth-gate).

---

## 8. Non-circularity certification — run before publishing any reduction

Distilled from the **RBRL retraction**, the most instructive dead end in the corpus. A device must
pass all four.

**TEST A — full-range instance.** Instantiate at exactly the parameters your theorem uses and read
the statement aloud. RBRL at (a=1, b=∞) reads `|E(n) − C₀| ≤ κ√V` — *which is the conclusion with a
change of variable*. Verdict in-file: **"the derivation is valid and empty."** One minute; run it
first.

**TEST B — calibration.** Where did the constant come from? RBRL's κ was measured on **the very
defect it bounds** — *"a device calibrated on its own target is an assumption wearing a number."*

**TEST C — independent construction.** The two compared sides must be independently constructed and
the comparison **downstream of both**, not the definition of either. Build side A with a definition
that provably mentions none of side B's symbols; state explicitly that the comparison is downstream.

**TEST D — strict weakness (the positive criterion).** *Every instance you actually invoke must be
strictly weaker than the conclusion.* Surplus in *un-invoked* instances buys nothing. Locate your
surplus and prove the uniformity — **that uniformity is the actual theorem.**

**Companion — what a real defect must look like:** integer-valued, monotone, non-negative. *A
sign-oscillating count-minus-ramp is the **ledger**, not the defect.* Diagnostic: an event-free cell
should book exactly −½.

**CONSTRUCTION-GAP vs ESTIMATE-GAP.** Classify every residual. It tells you whether more analysis
can possibly help — the difference between "work harder" and "find the missing object."

---

## 9. The deflation protocol — how to refute your own rigidity claim

Six steps, earned by demolishing three of this program's own claims in one afternoon.

1. **Is the special value the extremum of a monotone family?** Then it is automatic, not rigidity.
2. **Does the deduction use anything beyond "x = c ⟺ parameter = c₀"?** If not, its content is nil.
3. **Perturb the family.** Two criteria agreeing on the original family and diverging on its
   neighbours were agreeing *extensionally*, not structurally.
4. **Demand a preimage in the object.** *"A cell whose order cannot be exhibited anywhere in the
   object is not structure."*
5. **Check whether other equally natural charts give other cells.** cos → μ₆, sin → μ₁₂, tan → nothing.
6. **What survives is only what is neither an extremum nor a convention.**

**Corollary:** an answer set as small as {1,2} is the most common coincidence available, so
agreement there is near-zero evidence.

---

## 10. Registers, evidence tagging, and how an item moves

**Three tags, never blended** — **[proven]** (kernel-checked, *with the axiom footprint stated as
part of the tag*), **[measured]** (script path + precision + sample size, all three),
**[interpretation]**. Tags attach to **claims, not paragraphs**. A [measured] tag without precision
is [interpretation] wearing a tag.

**Fourth tier: [certified]** — interval/exact arithmetic with **proven error bounds**. The only
tier that can enter a proof. Precision ≠ certification.

**[cited]** — a community theorem consumed and named at point of use, **never a conjecture**.

**Retraction-in-place** — write the retraction into the section it belonged to, with each
compounding cause named *separately*, the replacement observable, and the numeric contrast.

**Correction ledger, both directions** — publish corrections *of the literature* and *of yourself*
in one list. One-sided is the tell.

**Corroboration-vs-status separation** — a second, weaker derivation route is a *validation
instrument, not a gap*, and its coverage must never appear in the same table as the mainline.

**How an item moves register:** a measured item may become proven only via a **named route with its
remaining step stated**, and the route must carry the field *"does more numerics help?"*. **A
promotion with no stated route is not a promotion.**

**Consume classical theorems as typed fields** — make each cited input a named field of a structure,
so "cited" vs "proved" is separated by the type checker. Pair with an **interface ledger**: each
hypothesis, its meaning in your frame, and what discharges it. **[discipline]**

**Compile a non-vacuity control for every interface** — a counter-instance proving the interface
consumes genuine content. **[proven]**

---

## 11. Failure modes — the part worth reading

1. **Importing a chart artifact as an obstruction.** The convergence abscissa, the strip, the window
   [1,N] are features of the *projection*. A two-rail deficit went from N^0.474 to N^0.0019 on
   carrier-native sampling. **Cleanest instance:** the transcendence question in a multi-rail
   independence argument is a chart artifact — mode lattices p^{−d}ℤ and q^{−e}ℤ meet only in ℤ, so
   every cross mode cancels **exactly**, and irrationality measures never arise.
2. **Worst-case analysis means harmonics were already dropped.**
3. **Estimating before the DC is evaluated.** Every landed result has the shape: find the common
   mode, compute it *outright*, estimate only the remainder.
4. **A device calibrated on its own target is an assumption.**
5. **Agreeing confirmations are worth nothing; only decomposition is** (§9).
6. **The literature gate run late.** Eleven turns were built on an "antipodal law" that is
   Pomerance 2015. **Gate before building.**
7. **Refuting a definition nobody used.** Quote the source definition with `path:line` and diff
   before writing REFUTED.
8. **Multi-rail ≠ multi-function.**
9. **Never enumerate what a law can decide.**
10. **A monotone quantity crossing your constant is not a hit.** A ratio passed *through* π/3 while
    monotonically decreasing; at 10⁶ alone it reads as a 0.03% hit. **Run any harmonic-constant test
    at ≥2 scales and report the trend.**
11. **Falsify a constant by parameter-scan, not precision.** `0.337 ≈ 1/3` died when the free dial
    moved it monotonically (0.304 → 0.359 → 0.392). **A constant that moves with a free dial is not
    a constant.**
12. **The collinearity check on any two-scale fit.** Over n ∈ [200,9000], log n spans 5.6→8.8 and
    log₂n vs log₂log n are collinear — fitted coefficients meaningless. This produced a *withdrawn*
    result.
13. **Quantile-of-the-mean, never mean-of-quantiles.**
14. **Surrogate circularity.** IAAFT fixes the power spectrum — whose transform *is* the ACF — so it
    reports "zero excess" by construction. **Always ask: does my surrogate preserve the statistic I
    am testing?**
15. **Fast convergence to a false value** — reading a *quotient* as a clean object converged fast to
    a wrong derivative because the quotient had poles. *"The most dangerous failure mode on record."*
16. **Best-fit rational approximation certifies fake rationality.** The honest discriminator is
    lattice membership.
17. **Dimension tools give smallness, never emptiness.** Negative dimension gives N^ε **per window**;
    there are infinitely many windows.
18. **Sample the carrier coordinate, not the chart's own ticks** — otherwise the instrument aliases
    away exactly the structure it looks for.
19. **A degenerate measurement may be a theorem talking.** A naive μ,σ returning 0,0 was the theorem,
    not a bug.
20. **When the main term is < 1, the error *is* the answer** — budget and second-moment arguments are
    structurally blind to a set of size three.

---

## 12. Classical under another name — the attribution table

| House name | Classical identity |
|---|---|
| digit/carry ledger | Legendre + Kummer |
| the carry automaton (#400) | **Holte's "amazing matrix"**, AMM 104 (1997) 138–149; Diaconis–Fulman, AMM 116 (2009) 788–803. Eigenvalues 1, p⁻¹, …; stationary distribution **Eulerian, independent of p** |
| the antipodal law (#396) | Pomerance, AMM 122 (2015) §5 — both arcs, same threshold |
| multi-rail digit budget Σβ_p < 1 | Bloom–Croot, arXiv:2509.02835, **Conjecture 1**, verbatim at κ=1/q |
| dimension + finiteness clause | Han Yu, arXiv:2004.05924, Conjecture 1.4 |
| the exponent 0.02595 | Pomerance's published heuristic; OEIS A030979 |
| ledger + smooth-number positions | Granville–Ramaré — their κ_p(n) *is* our carry count |
| the DC constant log 3 − 1 | Maier–Tenenbaum / Erdős–Hall — the **same computation**, not an analogy |
| the clock chart / cell integral | Riemann–von Mangoldt counting via arg Λ; the cell = π law *is* the argument principle |
| the exact gauge | Watson/Mellin + non-stationary phase (the file says so) |
| dwell | occupancy spectrum / extreme-value quantile |
| the S(t) cocycle | a coboundary of a per-scale potential |
| bounded primitive ⟹ continuation | Landau: abscissa = growth exponent of partial sums |
| split at x=1 and reflect | Hecke's classical converse-theorem proof, essentially verbatim |
| two-clock Bessel | Mellin–Barnes / Meijer-G |
| differenced resolvent | Hadamard/Mittag-Leffler counterterm |
| graded mode dictionary | generalized-eigenspace picture of algebraic multiplicity |
| generator descent D(q)T(1)D(q⁻¹) | torus conjugates transvections; ⟨S,T⟩ = SL(2,ℤ) |
| clock projectors as polynomials | Lagrange interpolation + Chow–Künneth/Beauville (Deninger–Murre) |
| channel constancy / annihilator | equidistribution on a closed subgroup + Weyl/Parseval (Sato–Tate apparatus) |
| the bounded-complexity lift | spreading-out + relative Hilbert schemes + lisse rigidity |
| the rigidity squeeze | Frobenius/Galois commutant vs cycle span (Tate-conjecture verifications) |
| the universal rigidity trap | Legendre/Kummer 3-adic valuation of a central binomial |
| harmonic volume | Harris's construction, computed |
| mantissa normalization | the standard "renormalize for bounded slopes" of fractal geometry |
| **the whole of `erdos377_partial.tex` §4–6 + Appendices** | van der Corput, Weyl differencing, Vaughan, Erdős–Turán–Koksma — **and the file says so** |
| sub-random-walk transfer (`lem:transfer`) | the classical Dirichlet-series abscissa theorem, σ_c ≤ limsup log\|A(x)\|/log x (Titchmarsh §9.14). Value added is the Lean formalization and the strip bookkeeping — **not** a new theorem |
| the grown primitive | Riemann's own e^{−n/x} smoothing; Γ(s)L(s) is the standard Mellin pair. Novel part is the *diagnostic use* against a random control, not the object |
| wild ε via filtration tower + stationary phase | **Deligne, *Les constantes des équations fonctionnelles*** — ⚠ **NOT CITED in either clock paper. The one genuine attribution gap found in the sweep.** |
| the harmonization archetype | Furtwängler's Principal Ideal Theorem (credited) |
| Vandermonde moment-tower faithfulness | Prony / Vandermonde identifiability |

**What is genuinely house in that last row:** fine blocks, the r-uniform constant, adaptive order
with verified window overlap, the amplitude-only r = 2 saving, counting-not-estimating the bad
pairs, and measuring the saving against log n.

---

## 13. Dead ends, with cause of death

A documented dead end is worth as much as a technique. The corpus has ~50; these are the
transferable ones.

- **The entropy budget** (Σβ_p ≤ 1 over balanced rails). Measured maxima 6.8–7.0 against a claimed
  1. **Cause, structural:** the cost identity charges βp log n per rail *only* when the rail freezes
  at every scale; for p near n^{1/K} with K fixed the freeze is cheap and the rails are many. **The
  budget binds only as d_p → ∞.**
- **Carry conservation.** Proven, then proven **inert** — the small-prime share of log C(2n,n) → 0.
  *Kept deliberately: "knowing that it is inert is worth more than not having looked."*
- **RBRL.** Retracted: restatement, self-calibrated constant (§8).
- **"Half of every band" for all k.** Withdrawn — it summed Mertens over intervals shorter than 1.
- **The csc addition law used term-by-term.** 119× worse than the product bound. *The identity is
  exact; the triangle inequality discards the reorganisation that makes it additive.*
- **"A short lattice vector controls the error."** Dead by construction — the shortest possible
  vectors gave *cleaner* than generic results. *"A short vector is not a defect; the bound that said
  so was lossy."*
- **Dimension-negativity ⟹ finiteness.** False.
- **Pruned-tree finiteness.** Live-node count grows **linearly** with depth, no saturation.
- **The growth-clock reading.** Retracted with *both* compounding causes named: prefactor
  contamination and mixed strata.
- **Ghost spectral lines.** Hann skirts of giant Euler lines; killed by peak enumeration.
- **"Solved warps buy values."** They buy **summability, not values** — cross-validation shows the
  cell-closure ratio has *zero* predictive power for registration.
- **Lane surgery.** The half-lane objects have a natural boundary at the centre; no decomposition
  into complete readables exists.
- **Semiregularity.** Structurally blind; twelve transverse obstructions are cohomologically
  invisible. *"Falsified as specced; the refuted pointer stays in the record."*
- **The Pfaffian no-go.** det = −3^b for **every** étale-ℤ/3 Prym sixfold ⟹ the whole family splits.
  Three further designs (μ₆, S₃×ℤ/3, PSL(2,7)) split too — *"the third null of the night, published."*
- **Baker for k ≥ 3.** Baker bounds *linear* forms; the cleared k ≥ 3 form is **quadratic** in the
  logs. Caught by self-audit before delegation.

---

## 14. Orphans — built and never used

Listing these is the honest part; several are the most promising things in the corpus.

- **THE LADDER has never been run**, on any problem. Prove where every rail cooperates, then
  transfer. The prototype is Spiro's τ(n) = τ(n+5040) — 5040 = 7! is smooth, divisible by every
  small rail — with Heath-Brown then removing the crutch. *"The transfer step is the theorem."*
  Named live: #727's k=1 is Balakran and **Balakran's method was never run up to k=2**.
- **The csc addition law** — proven, verified to machine precision, never used. Its stated *correct*
  use (one rail's mass against the other rail's complete phase sum) is described and never executed.
- **The vanishing-adjustment clock** — the fourth clock layer, "the layer that turns Satake data
  into vanishing," never invoked in a proof.
- **The obstruction-directed extension operator 𝔈** — boxed schema, two prototypes, nothing consumes it.
- **The phasor delay adapter** — one partial improvement, immediately superseded.
- **Li positivity** — a required admissibility stamp no downstream theorem consumes.
- **The general registration-gap family** `S_{H,K}` — full cocycle laws proved; only the π/m vs 1
  pair is ever used.
- **The GL(3)/GL(4) vector-clock law** — Lean-proven, 36/36 measured, no downstream consumer.
- **The bounded-width front** — named "the finiteness lever" for #377, never pursued.
- **The transfer protocol** (`mdhnt_transfer_prompt_v1.md`) — a complete outsider-testing protocol
  with **no results anywhere in the repo**. Cheapest high-value gap.
- **`tmp/GRADE4_PROGRESS.md`, 3303 lines** — the largest markdown file in the repo, referenced by
  nothing. Sixteen further unmined files in `tmp/` cover the Weil/Hodge/grade-ladder arc.
- **The value-registration law** — named as *the* single theorem-target through which any
  carrier-native centre value must pass; measured in a 24-row census; never proven.
- **Erdős #400's literature gate: NOT RUN** (its own register line) — though the Holte
  identification above now partially discharges it.

---

## 15. Running it on a new problem — the checklist

1. Write the object's **structural presentation**. None ⟹ no lift.
2. **Run the literature gate now.** Not later. Search the *mechanism*, not the topic.
3. **Is the object secretly a known function?** Sandwich it between known functions before assuming
   difficulty. This dissolved a conjecture as mis-posed.
4. Give the object **its own scale**. Never unit 1.
5. **Evaluate the DC exactly.** Only then estimate the remainder.
6. Classify the target: *uniform-in-n* (hardest) → *positive-probability* (softer) → *fluctuation*
   (softest, computationally accessible). Attack the softest form that answers the question.
7. Choose the geometry; load the rails you intend to compare.
8. Harmonize clocks to the common refinement. **Measure only at complete cells.**
9. Write the **registration law**: chart = native + defect, defect integer, monotone, ≥ 0.
10. Sublinear integrated defect ⟹ zero. Say so, and say it is the dichotomy.
11. **Run the four non-circularity tests (§8) before publishing the reduction.**
12. Project with the loss ledger. Never claim state equality from readout equality.
13. If an obstruction is retained, synthesize the re-adapter and re-enter at step 7.
14. Tag every output **proven / measured / certified / interpretation**. Blending them is the one
    unforgivable error, because it is the one a reader cannot detect.

> **The standing diagnosis.** The ledger gives everything **multiplicative or per-rail**. Every
> problem's actual question needs a **collision or density** statement, which the ledger does not
> reach. That gap is the frontier of the method, and the missing instrument has a name — **the
> ladder** — and has never been run.
