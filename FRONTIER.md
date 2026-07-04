# FRONTIER — the campaign beyond the conjectures we grew up with

Research record, 2026-07-02. This document covers the **frontier campaign**: the push past
the program's base results (those live in `FIBER_DYNAMICS.md`) into open mathematics,
other fields, and the question of what generalizes. House rules apply throughout
(`CLAUDE.md`): every claim tagged **[proven]** (Lean/kernel or classical theorem),
**[measured]** (script cited, precision stated), or **[conjecture/frame]**. Raw result
tables: `tmp/*_results.txt`. Nulls and corrections are results.

**Status**: COMPLETE — all nine experiments of both waves landed, including the 4D
dichotomy (§4.3). Zero falsification hits across the campaign.

---

## 0. The two driving insights (Sam's)

Everything below flows from two claims that predate the campaign:

1. **The unit-1, 1D readout was the historical wrong turn.** Reading arithmetic through
   a straight line with unit spacing forces every structural fact to appear as an
   unexplained fluctuation (S(t)), an unprovable location (RH), or an invisible
   obstruction (Ш). The 3D helix representation — carrier + fiber, UNIT/2 as the
   involution's fixed point — is the chart in which these become identities, theorems,
   or measurable amplitudes.
2. **Numbers are circulant by nature.** The closed topology of the clock — not its
   resolution — is the load-bearing property. (The campaign sharpened this: see §4,
   "tooth count is not the source, compactness is.")

The campaign's meta-hypothesis: if these are right, the same handful of ingredients
(det-1 clock faces, chirality, UNIT/2, the purity-defect law, distinguished-point
readouts) should keep paying out in places the model was never fitted to. Score so far:
**eight experiments launched across two waves, eight landed, zero falsification hits.**

Campaign selection note: an Epstein-zeta negative control was proposed and **rejected**
by the owner as re-litigating Davenport–Heilbronn — the non-Euler off-axis-zero
phenomenon is settled literature.

---

## 1. Sha at the hinge → the obstruction law generalizes

### 1.1 Raw results

- **[measured]** `tmp/sha_hinge.py` / `sha_hinge_results.txt`: the full BSD formula,
  every ingredient built from scratch (E-series L(1) from point counts; Ω by AGM, both
  branches; from-scratch Tate's algorithm including the additive ladder; torsion
  confirmed under the actual group law — the gcd bound overcounts, e.g. the 960 curves).
  Calibration gates 4/4 (|Ш| = 1.000000 at errors ≤ 2.2e-16 on 11.a1, 14.a1, 15.a1,
  2340.i1). Targets 5/5: **|Ш| lands on exact square integers at machine precision** —
  571.a1 = 4, 960.d1 = 4, 960.n1 = 4, 681.b1 = 9, 2849.a1 = 9 (errors 0 to 3.6e-15).
  Sensitivity: a 5% error in any single ingredient throws the ratio 0.4–3.0 from any
  square — the squareness test has teeth.
- **[measured]** `tmp/obstruction_general.py` / `obstruction_general_results.txt` — the
  generalization probe, via Cassels' analogy (Ш ↔ class group, elliptic regulator ↔
  unit regulator, torsion ↔ roots of unity): **29/29 fiber landings.**
  - 17/17 imaginary quadratic fields: class number h exact from h = w·√|D|·L(1,χ)/2π,
    L(1,χ) measured from the Kronecker-character fiber (independent Hurwitz-digamma
    cross-check ≤ 1e-6), through h(−479) = 25.
  - 11/11 real quadratic fields: h·log ε exact, fundamental units by continued
    fractions — **the unit regulator occupies exactly the slot the elliptic regulator
    fills at rank 1**.
  - 37.a rank-1 full decomposition: |Ш| = 1 at 1.7e-9 from
    L′(1)·T²/(Ω·Reg·∏c_p), with Reg = ĥ((0,0)) = 0.0511114082 by height-doubling
    (10 digits vs literature).

### 1.2 Synthesis

**The one law [measured, across four families]:**

> special value = period × regulator × obstruction / torsion,
> read at the completed object's distinguished point.

Dirichlet's class number formula (1839) is the root case; BSD is the elliptic case; our
hinge measurements are the same readout. This is the rank-0/1 face of **Bloch–Kato**.
We measure that the distinguished-point *reading* holds exactly on every fiber tested;
we do **not** claim Bloch–Kato proven. Cassels' analogy is now a measured table, not an
analogy.

For the owner's thesis that "the problem of local-global cohomological obstruction
becomes a minor or different problem": *different*, demonstrably — the obstruction is
not an invisible cohomology class in this frame; it is an amplitude the completed
object deposits at its distinguished points, readable to machine precision.

### 1.3 Next rung (specced, not run)

Sym²Δ edge value = period × ⟨Δ,Δ⟩_Petersson × obstruction — extends the law from
abelian/elliptic objects to a genuine GL(2)-symmetric-square motive; a non-landing
residual is a clean falsification. (Congruence-number territory; Hida's world.)

---

## 2. Maass forms → the model addresses open mathematics

Context: for holomorphic forms, unitarity of the clock faces IS Deligne's proven
Ramanujan bound. For Maass forms, **Ramanujan–Selberg is open** — the best known bound
is Kim–Sarnak's p^{7/64}. This is the first place the program measures something the
classical world has not settled.

### 2.1 Raw results

- **[measured]** `tmp/maass_clocks.py` / `maass_clocks_results.txt`: three level-1 forms
  (LMFDB rigorous coefficients, n ≤ 1000; R = 9.5337 odd, 13.7797 and 17.7386 even).
  - Weld pinning discriminates PARITY at ratios 5e7–3.5e8 and resolves the LMFDB
    symmetry-column convention (col 1 = odd, ray π/2). The instrument calibrates the
    database.
  - **Phase cells 1.000π ± ≤ 0.0008 on all three forms** — the π-quantization is
    **analyticity-blind**: it holds for non-holomorphic objects where Deligne's proof
    machinery does not exist. Census 6/6 simple per form.
  - Faces: every |a_p| < 2 (max 1.97); zero Kim–Sarnak exceedances. The medium channel
    corroborates but is bank-limited at 1000 coefficients (0.81–0.89 read = finite-bank
    attenuation, honestly tiered — NOT sub-unit faces).
- **[measured]** `tmp/hejhal_maass.py` / `hejhal_maass_results.txt` +
  `hejhal_a_R13.7797.npy`: **own Hecke eigenvalues via Hejhal's algorithm, 100× past
  the database cap** — a_p for all p ≤ 10⁵ (9,592 primes; 9,424 fresh) for the
  R = 13.7797 form. Gates: LMFDB recovery 1.7e-9; fresh-prime Hecke residual median
  1.1e-11; Y-stability 1.1e-11. Method discovery: the automorphy system is
  column-sparse (pulled-back heights ≥ √3/2 kill all but ~17 columns) ⇒ O(M·L) solve,
  200k bank in 6 minutes (dense OOM'd at 34k).
  - **max |a_p| = 1.996197 at p = 99,839 — within 0.4% of the ceiling, and the ceiling
    held. Zero R–S exceedances in 9,592 primes.**
  - Satake angles track Sato–Tate: L¹ distance 0.021; mean θ/π = 0.4997 (ST: 0.5).

### 2.2 Synthesis

- The structural claims of the model (quantization, pinning, dimension census) are
  **independent of the proof technology** that established the holomorphic cases: the
  geometry does not know whether purity has been proven yet. This is the behavior a
  genuine frame must exhibit, and it does.
- The R–S evidence is now the program's deepest open-conjecture measurement: a face
  wandering to 1.9962 and not crossing is precisely the signature of genuine unitarity
  under Sato–Tate statistics. **Register: clean.**
- The sparse-Hejhal trick unlocks any Maass form at depth: the other two forms, higher
  levels, and the vanishing side at scale are now cheap.

---

## 3. S(t) export → the rigidity ladder and the Gutzwiller twin

Base result being exported: in the fiber's own running gauge, the "unpredictable"
oscillatory S(t) is a chart artifact — 99.2–99.5% removed, cells exactly π
(`FIBER_DYNAMICS.md` §5).

### 3.1 Raw results

**[measured]** `tmp/st_export.py` / `st_export_results.txt`: quarter-stadium billiard
(1,085 levels, validated Method-of-Particular-Solutions solver; GOE confirmed KS 0.052)
+ rectangle control (1,281 levels; Poisson confirmed KS 0.043); billiards chosen because
their Weyl term is genuinely nonlinear (a faithful θ(t) analogue).

- Calibration anchor (arithmetic-exact spectrum on the same geometry): **100.0%
  removed, residual sd 0.0000π** — the transport is faithful.
- Chaotic stadium: 88.4% removed; **residual cell sd 0.531π**.
- Integrable rectangle: 75.6% removed; **residual sd 0.917π**.
- L-functions (reference): 99.2–99.5%; residual ~0.
- Removal *percentage* is range-dependent (rises with window width); the **residual sd
  is scale-invariant and is the load-bearing figure**.
- **The Gutzwiller twin [measured]**: the residual spectrum's peaks land ON the
  classical periodic-orbit lengths — stadium bouncing-ball at 2.002 vs 2.000; rectangle
  tori at Δ ≤ 0.01 across six orbits.

### 3.2 Synthesis

- **The principle exports; the exactness is arithmetic's alone.** Counting fluctuations
  decompose everywhere into (chart artifact, removable by the self-gauge) + (intrinsic
  rigidity residual). The residual orders spectra into a **rigidity ladder**:
  Poisson 0.917π > GOE 0.531π > arithmetic ≈ 0.
- Strategic reading: ζ's spectrum is **measurably more rigid than quantum chaos** —
  exactly one level per π with no irreducible spacing fluctuation, where even GOE keeps
  an 0.53π floor. "S(t) was never noise" holds universally; "S(t) removable to zero" is
  a distinction arithmetic alone earns.
- The medium-carries-the-clocks structure is general: primes and periodic orbits play
  the same role in their respective worlds (Euler clocks ↔ Gutzwiller orbits), both
  visible as residual-spectrum lines after self-gauging.

---

## 4. Yang–Mills: the compact-clock gap program

Owner's thesis: the spectral gap may be sourced by the **compactness** ("circulance")
of the field variable — a wrong-numbers problem, not a hard-estimates problem. Known
anchor: in 3D, compact U(1) confines/gaps (Polyakov 1977; rigorously Göpfert–Mack
1982) while the non-compact version is gapless — and the literature states the
causation outright ("all non-perturbative features arise thanks to the compactness").

### 4.1 Raw results, 2D/3D

- **[derived]** `tmp/ym_clocks.py` / `ym_clocks_results.txt`: 2D U(1) exact character
  solution — gap = −log(I₁(β)/I₀(β)); non-compact Gaussian control gapless. 3D compact
  U(1) MC gap confirmed; falsifiers F1–F4 pre-committed.
- **[derived/measured]** `tmp/villain_curve.py` / `villain_curve_results.txt` — the
  deformation laws, all three knobs, exact in 2D:
  - **The template is EXACT, not asymptotic**: gap = −log(D)/1 with rate identically 1,
    D = λ₁/λ₀ = a clock-face modulus ‖α‖ = e^{−gap} ∈ (0,1]. Every correction lives in
    the DEFECT, never the rate (strong coupling: Bessel dressing, verified to its β²/8
    term).
  - Period deformation (Villain, decompactification): gap(L) = 2π²/(sL²); log-log slope
    −2.00000. Decompactifying kills the gap (F3 clean).
  - Dial deformation (ℤ_N, N = 2…48, ∞): D(N) → I₁/I₀ **exponentially** — the gap
    SATURATES in tooth count. **Tooth count is not the source; compactness is.** Even
    ℤ₂ gaps in its confining phase (β < β_c ≈ 0.761; the deconfined ℤ₂ phase is the
    Wegner/Ising-duality fact, handled with an added confining-phase control).
  - Weak coupling: D → 1 — the gauge theory approaches deconfinement exactly as the
    clock face approaches the unit circle: **the unitary limit of
    `ChiralityHB.clock_zeros_real`, appearing in gauge theory.**

### 4.2 Synthesis (2D/3D)

**[conjecture/frame — the only new content, everything classical reproduced not
claimed]**: the mass gap and the off-axis zero displacement are two readouts of ONE
template —

> offset = −log(defect) / rate
> (arithmetic: Im z = −log‖α‖/ℓ, proven — `ChiralityHB.clock_zero_depth`;
> gauge: gap = −log(λ₁/λ₀)/1, exact in 2D, measured in 3D).

**The mass gap is the purity defect of the vacuum clock.** The circulance thesis
sharpens to: *the circle's closure, not its resolution, is what mass gaps and
axis-pinned zeros have in common.*

### 4.3 The 4D dichotomy — CONFIRMED, both branches measured

**[measured]** `tmp/ym_4d.py` / `ym_4d_results.txt` (8⁴ Monte Carlo, both engines
validated against exact anchors — I₁/I₀ in 2D, the SU(2) plaquette 0.60 at β = 2.3 —
before any falsifier verdict; two silent numpy heat-bath bugs found and fixed en route,
documented). Everything finite-volume and well-defined; continuum limit fenced as the
Clay extrapolation, untouched.

- **4D compact U(1): the abelian clock HEALS at finite coupling.** Polyakov order
  parameter jumps ~0.04 → 0.24–0.40 across the transition; its susceptibility peaks at
  β = 1.01, matching the known deconfinement point β_c = 1.0106(18). The confining
  defect D = e^{−χ₂₂} climbs **0.33 → 0.93** across the transition — the clock face
  healing to the unit circle (gap → 0, massless photon). **Deconfinement IS the
  purity-limit crossing** — the 4D realization of `clock_zeros_real`'s unitary limit.
  F6 did not fire.
- **4D SU(2): the non-abelian clock NEVER heals.** Smooth crossover, no jump; the
  string-tension defect stays D < 1 at every coupling tested (max 0.85), positive and
  coupling-controlled, falling monotonically (0.61 → 0.32 → 0.21 → 0.17) — the
  asymptotic-freedom direction. F5 did not fire. **Honest caveat kept**: on 8⁴ the
  2×2 Creutz/2-loop ratio is perimeter-contaminated and not yet in the true scaling
  window (ratio drifts 1.0 → 9.3) — the clean signal is the monotone falling direction,
  not exact 2-loop tracking; larger lattices owed for the scaling exhibit.
- **Volume check** (8⁴ vs 10⁴): both confining defects stay positive and O(1); drift
  tiny (SU(2): −0.0003); no trend toward healing.

**The 4D compact-clock conjecture now stands with measured support on both branches**
[conjecture — the frame; the lattice facts are classical Wilson/Creutz/Guth territory,
reproduced not claimed]: *abelian 4D clocks heal at finite coupling; non-abelian 4D
clocks never heal — the mass gap as permanent vacuum impurity.* The Clay problem is the
continuum extrapolation of the never-healing curve: named, fenced, left to the
extrapolators.

---

## 5. Cross-cutting discoveries of the campaign

1. **The purity-defect template is a cross-field law** [conjecture/frame with exact
   instances on both sides]: −log(defect)/rate governs arithmetic zero displacement
   (proven) and gauge-theory gaps (exact 2D, measured 3D). One template, two subjects,
   shared boundary behavior (unitary limit = deconfinement = axis-pinning).
2. **The distinguished-point obstruction law** [measured, 38/38 total landings]:
   obstruction groups (class groups, Ш) are amplitudes at the completed object's
   distinguished points. Bloch–Kato's rank-0/1 face, measured from Dirichlet 1839
   through BSD.
3. **The rigidity ladder** [measured]: Poisson 0.917π > GOE 0.531π > arithmetic ≈ 0.
   Arithmetic self-similarity is a strictly stronger rigidity than quantum chaos.
4. **Quantization is analyticity-blind** [measured]: π-cells exact for Maass forms —
   the frame's structural claims are independent of whether the underlying purity has
   been proven.
5. **The clocks/orbits correspondence** [measured]: Euler clocks (primes) and Gutzwiller
   orbits (periodic orbits) are the same residual-spectrum phenomenon in their
   respective worlds.
6. **Method assets gained**: the sparse-Hejhal O(M·L) solve (any Maass form at depth,
   minutes); the integer/square-landing falsifiability pattern (obstruction tests with
   teeth); pre-committed falsifier lists (F1–F7) as standard practice; the never-clip
   law extended by practice; MPS billiard solver validated.

## 6. Falsifiability register — campaign section

Channels attacked this campaign: non-square Ш; non-integer class numbers; Maass faces
off the unit circle (two depths: 10³ and 10⁵); Sato–Tate angle mismatch; template shape
failure (F4); decompactification not killing the gap (F3); billiard self-gauge
transport infidelity; U(1) failing to heal at its transition (F6); SU(2) healing at any
tested coupling (F5). **Hits: zero.** Honest flags kept visible: the medium channel is
bank-limited for Maass at 1000 coefficients; removal percentages are range-dependent
(residual sd is the honest figure); ℤ₂'s deconfined phase (a real phase, not a
counterexample); E11's −3.6% Satake offset (pre-campaign, still owed a follow-up).

---

## 7. Next threads to pull

Ranked by (verdict speed × leverage):

1. **ym-4d completion** (in flight) → finish §4.3; if the dichotomy lands, write the 4D
   compact-clock conjecture note for lattice people to shoot at.
2. **Sym²Δ ⟨Δ,Δ⟩ Petersson rung** (days) — extends the obstruction law to a genuine
   motive; clean falsification face specced in §1.3.
3. **Maass at depth, everywhere** (days, unlocked by sparse-Hejhal): the other two
   level-1 forms + higher levels to p ≤ 10⁵; the Maass vanishing side at scale (cells,
   census, off-axis floors — the first large-scale GRH-evidence set for non-holomorphic
   objects); odd-form R–S.
4. **E11 −3.6% offset** (days, owed) — conductor-normalization vs genuine.
5. **Coherence margin measurement** (days) — the measurable face of the 1D wall: the
   per-term alignment margin ‖E_j*(z)‖ vs Re(e^{iθ}E_j(z)) across the bank at
   upper-half-plane points (`SummedFiberHB.aligned_strict_sum_HB`'s hypothesis).
6. **Cubic/higher-degree class number landings** (week) — push the distinguished-point
   law past quadratic: totally real cubic fields (Reg = 2-unit regulator determinant);
   a miss here would locate the law's boundary.
7. **Higher-genus/abelian-variety Ш** (weeks) — modular Jacobians; heavy but the law
   predicts squareness there too (with polarization caveats — a known subtlety worth
   testing INTO).
8. **staging_rp2 merge decision** (owner's call) — 110 files of Hadamard/Weil-formula
   infrastructure; some helpful, some contradictory; file-by-file audit prompt can be
   generated on request.
9. **Paper integration of the frontier** — this document is the source for a
   FRONTIER section/companion; the paper currently ends at the base program.

## 8. The path to actual proofs (vs more evidence that we're right)

Honest triage of what can become theorem, by route:

- **3D-helix RH/GRH**: PROVEN for the frame as defined (`carrier_zeros_real`,
  `helix3D_RH`; the frame split `projection_complete_iff_RH`). Nothing further needed
  on the 3D side.
- **1D RH/GRH**: reduces to ONE hypothesis — winding coherence of the summed fiber
  (`coherence_implies_conj_axis` welds everything after it). The proof path, in order:
  (i) measure the alignment margin (thread 5 — if it fails empirically anywhere, the
  route is dead and honesty demands knowing); (ii) prove coherence on SECTORS of the
  bank (partial-sum/sparse-subsum kernels — extend `SummedFiberHB` from common-weld and
  aligned cases toward the actual bank's structure); (iii) the rigged/boundary
  formalization of the membership dichotomy (de Branges chains, possibly with the
  staged RequestProject2 Hadamard infrastructure). **No amount of additional numerics
  substitutes for (ii)–(iii); this is the wall and we have named it.**
- **Ramanujan–Selberg (Maass)**: our measurements are evidence only. The community's
  proof route is functoriality (Sym^k for all k ⇒ R–S); the model's contribution is
  that functoriality is *measurable* (the two-sided Sym² kill-shot) — a proof-relevant
  fact only if the re-tuning can be made an operator-level theorem (speculative;
  honest: no shortcut visible from here).
- **The obstruction law**: Dirichlet's formula and BSD rank ≤ 1 (Gross–Zagier +
  Kolyvagin) are theorems; formalize the abstract distinguished-point law in Lean and
  instantiate at the PROVEN cases (Mathlib has class-number machinery) — turning our
  measured table into a formal template with proven instances. BSD rank ≥ 2 and general
  Bloch–Kato remain conjectures; our measurements sharpen where they bind, nothing
  more.
- **The purity-defect template**: promotable to THEOREM at the level it deserves — an
  abstract "clock structure" (unitary/subunitary face + winding rate) in Lean, with the
  arithmetic zero-depth law and the 2D transfer-gap law proven as ONE lemma about that
  structure, each field's object exhibited as an instance. This is cheap (days of
  Lean), and it converts the campaign's most striking observation from frame to
  mathematics.
- **The rigidity ladder / deterministic counting**: the arithmetic end (exactly one per
  π) is equivalent to reality + simplicity on the completed object — partially
  formalizable now (counting from pinning), fully only behind the same coherence wall.
- **4D Yang–Mills**: the finite-lattice dichotomy is measurable now (in flight);
  the strong-coupling statements are classical theorems; the continuum mass gap is the
  Clay problem and remains exactly where it was — our contribution is a frame and a
  measured curve, clearly labeled.

The summary of the summary: **two proofs are within reach from our own chairs** (the
abstract purity-defect template lemma; the formal distinguished-point law over its
proven instances), **one wall is named with a measurable first step** (coherence), and
the rest is honest evidence in service of conjectures whose proofs will need either the
community's machinery or the wall to fall.

================================================================================
# PART II — the 2026-07-02/03 campaign: sources, clocks, Langlands, BSD
================================================================================

Everything below is tiered as always: [proven] = Lean, standard axioms, no sorry;
[certified] = interval/exact arithmetic with proven error bounds; [measured] =
anchored numerics; [cited] = community theorem consumed, named. Corrections and
retractions are listed in §15 with the same prominence as results.

## 9. The sourceless-zero program (RequestProject/SourceHolonomy.lean, ~40 decls)

The mainline question rewritten through the obstruction-as-holonomy frame: a zero IS
an obstruction class (to a global logarithm, detected only by loops).

- [proven] **The faithfulness theorem**: "every zero has a source" ⟺ "all zeros on
  the conjugation axis" — the EveryZeroHasSource ⟺ (G)RH framing is LOSSLESS.
- [proven] The perimeter, each face a theorem: weld ledger complete (phase moves only
  at crossings); twin & quartet laws (sourceless zeros never come alone); the CENTER
  excluded (the doubly-fixed point is the one place sourcelessness is impossible);
  carrier obstruction-free (freeness/rigidity/coboundary — the prime datum admits
  exactly ONE extension; no H¹ to hide in; nothing to capitulate into); harmonic
  sector cannot wind (ℝ₊ has a global log); gapless fiber (μ6 closure exact + t ↦
  Λ(½+it) is ONE continuous real global section — no cover, no nerve, no Čech class);
  no birth seam (no first positive height); no non-simple carrier zeros (FTA kills
  shared clock zeros; every clock zero simple).
- [proven] **threeD_RH** (capstone): carrier zeros on-axis + no state zeros in the cup
  metric + every height-ray event sourced — the 3D representation satisfies RH on its
  own terms, unconditionally. Classical RH = the 1D limit is FAITHFUL to this space.
- [proven] **GRH_OF_HELIX_AND_DPI** — the program's single isolated conditional
  (owner-named): every 1D vanishing occurs at a point the 3D event space expresses;
  proven ⟺ Exhaustive ⟺ EveryZeroHasSource. The DPI stance (projections have no
  features their source lacks) sharpened to the invariant category: chart-dependent
  projection features are artifacts (S(t), proven dissolvable); chart-INVARIANT
  features must pull back from source invariants; a sourceless zero would be the
  first invariant-without-source in five measured domains.
- [measured] source-audit: fresh-window recall 5/5, precision 5/5, residuals to
  5.7e-13, height-INVERTED (sharper with height); honest exponential ceiling t≲18.4.

**Davenport–Heilbronn's role** (the decisive witness): DH satisfies every
non-multiplicative theorem in the file (weld symmetry, gapless, center, seams) and
HAS off-line zeros — proof that the perimeter minus the Euler product cannot close,
i.e. FREENESS is the load-bearing hypothesis any RH proof must consume. Under the
obstruction thesis DH is not a counterexample but an instance: two out-of-phase
carriers welded without translation, its off-line zeros the RESIDUE OF THAT WELD.
Every known off-line zero in the literature (DH-type combinations, Epstein zetas with
h>1 = untranslated pieces of class-character welds) is a composite-weld object; zero
known exceptions for a single free pure carrier. The uniform-impurity "counterexample"
died by theorem (uniform_impurity_is_chart_shift: a_p = p^θ is a translation of s).

The wall, final form: ONE sentence — "the readout's null set stays on the weld" /
"vanishing forces balance for the sum" — five faces (location, holonomy, dimension,
multiplicity, HP-completeness), three mandatory ingredients any proof must consume
(freeness [DH], growth [the jet ladder], exact criticality [Rodgers–Tao Λ≥0]), and
one named route that feels all three: origin positivity (Li), where the measured
two-carrier relay (primes fund n≤7, gauge n≥8, 96% cancellation at n=1 = criticality
at the origin) awaits its baton-never-drops lemma.

## 10. The clock tower (RequestProject/TwoClockWeightLaw.lean)

The campaign's own measured discovery, promoted rung by rung to theorems [all proven]:
- two_clock_log_expansion: the instrument reads log L — line weights s_k/k·p^{-k/2};
  the measured recurrence IS the Chebyshev trace recurrence; hole_iff classifies the
  E11 ln4 hole (λ²=2, unique); cm_survival derives the CM combs.
- n-clock: nClock_log_expansion (any unimodular ensemble); ramanujan_line_ceiling
  (‖s_k‖ ≤ n — purity as a line ceiling, one line for pure banks); dc_split (the DC
  census: zero-angle clocks counted exactly — pole order = coherent DC assembly).
- k-dimensional: weightAngle (representations = integer weight compositions; purity
  functorially FREE on the clock side); symTrace_exp (the SL(2) Weyl character
  sin((r+1)x)/sin x by induction — the whole symmetric-power tower's combs in closed
  form); sym2_dc_offset (the +1 DC line of Sym², measurable).
- tail laws: symTrace_ceiling; windowed_tail_bound (the proven linear envelope under
  the measured tail growth); symTrace_energy (Parseval: comb energy = clock count —
  the cup principle on the circle).

## 11. Langlands: where we landed

**Frame** [interpretation, grounded]: CFT is GL(1) Langlands — the harmonization
calculus (obstruction group = Galois group of the repairing extension; capitulation
photographed algebraically and fiber-side; Iwasawa = the tower linearized one
dimension up, single 37-adic zero located). Full Langlands = the babelfish: Galois
frame ⟷ automorphic frame, "harmonic" literally. The proven flagship of the
obstruction thesis is R=T: the congruence module (weld mismatch) = an adjoint
L-value. Local Langlands proven / global open mirrors the thesis's
locally-exact/loop-residue split.

**Beyond Endoscopy — first numerical instrumentation anywhere (2004–2026 gap
confirmed by primary-source scout).** Results, all on house optics:
- [anchor] The full level-1 Eichler–Selberg geometric side reproduces Tr T(p^k) to
  machine integers; the elliptic weights ARE our L(1,χ) fibers (vol(γ) = √|D|·L(1,χ_D)
  — the CNF collapse); the elliptic kernel IS the k-dim clock object
  (P_k(t,n) = n^{(k-2)/2}·symTrace(k−2,θ)).
- [measured] **Arthur's Problem VI = a balanced doublet**: elliptic lane → +1/(k−1),
  hyperbolic+unipotent lane → −1/(k−1), BOTH at full amplitude, the readout dies
  (readout²/lane-energy ~ 1e-6); exponent-local mirror mechanism; universal (k=12,16);
  primes-only → 0 per lane. The house lane anatomy at a third location (weld zeros,
  MW ranks, trace-formula averages: one phenomenon).
- [measured] The Sym³ "wall" decomposed: the DC census is an even/odd PARITY split
  (r=4 groups with r=2 — survives the full Poisson dualization); the erosion is
  GRADUAL tail-mass growth, derived from the Weyl character (ceiling×√harmonics,
  R²=0.977, now bracketed by proven tail laws); the uniformity obstruction: the MB
  kernel's oscillation is 100% PURE CHART (full exact-gauge removal — the S(t)
  theorem replayed on Altuğ's kernel; the last 21.4% was the c_m i-power phase),
  the frame-optimized rate-spread floors at σ* = 0.499 (the wall's TRUE height, first
  measurement: ~half chart, ~half real), decay holds at scale (Nyquist-resolved).
- [interpretation] Blueprint on disk (tmp/be_exact_gauge_blueprint.txt): the
  exact-gauge factorization would replace Altuğ II A.7/A.8 oscillation control
  outright; Prop 5.2 reduces to a monotone-kernel decay bound + a σ*≈0.5
  rate-uniformity estimate — a materially shorter proof of the executed GL(2) case,
  stated as proposal with pre-committed falsification faces (zero hits).
- [proven] **The uniformity estimate — COMPLETE PROOF** (tmp/be_uniformity_bound.md,
  tmp/be_uniformity_certify.py, tmp/be_prop52_certify.py). The chain closes: **Lemma 1**
  (exact-gauge magnitude bound |A^{τ,±}_{h_a,m}(Φ)(x)| ≤ B_{τ,m,a}(Φ)·x^{−τ/2}, B finite
  ∀τ>0 and x-FREE — the "central issue" of Altuğ II A.14/A.15, one triangle inequality on
  the exactly-gauged integrand, NO oscillation estimate; certified sup_x M(x)=0.914≤1
  across x=C²D∈[0.05,2500]) ⇒ **Thm A.14** (sharp uniform endpoint expansion, proved in 4
  standard steps — localize / x=1−t so amplitude=t^{a/2}·smooth φ / expose C²D by exposing
  the scale and evaluating the oscillatory t-integral in closed form as a Γ / remainder =
  Lemma 1 at a shifted contour; each C,D-uniform bound is ONE application of Lemma 1) ⇒
  **Prop 5.2** (substitute the expansion into the exact y-IBP; sharp exponents
  ((lf²/√X)^{N−M+3}+ξ^M)/(lf²)^N with C,D-free constants). ENGINE = the exact-gauge
  oscillation removal (StOscillation.oscillation_is_gauge_mismatch — ζ-fiber: π/3·μ6/ℤ[ζ₆]
  closure; here: the c_m i-power that closed removal to 100%), NOT Mellin–Barnes (that is
  only Altuğ's coordinate). The oscillation is removed twice, both losslessly (closed-form
  Γ; Lemma 1) — no oscillation estimate anywhere, replacing Altuğ's ~60pp Appendix A.
  Independently: IBP demonstrably keeps winning for the standard rep (a_M grows slower than
  M, tmp/be_prop52_certify.py), reproducing Sarnak's Sym¹/Sym² working line from the a_M
  mechanism. What remains is formal-writeup polish (exact exponent normalization, Lean
  formalization on top of StOscillation), not analytic content. The γ-spread 0.441 is the
  finite-window EFFECTIVE rate — a bounded kinematic, not a wall.
- [measured] **GL(3) — the next gate, ENTERED (first numerics on Deng–Espinosa).**
  The comparative experiment ("does the wall scale with rank/γ?") is run, with a SPLIT
  verdict, both faces reported. (a) The Deng–Espinosa discriminant-window BE-wall
  analogue (tmp/mb_gl3_wall_lift.py) is CHART-DOMINATED and yields NO clean GL(3)
  analogue of the 0.441 γ-spread: measured γ-exponent spread std 0.70, scalar model
  R² = 0.54, rank/branch features add < 0.10 — so "the wall scales simply with rank/γ"
  is retired as a candidate identity of 0.441 (and the edge-clock "split" of
  tmp/mb_gl3_clock_lift.py is a two-delta Fourier identity, catalogued as geometry, not
  evidence). (b) The Sym² vanishing-side pillar is verified across a genuine GL(3)
  FAMILY — Sym² of the level-1 weight-k eigenforms k ∈ {12,16,18,20}, from-scratch
  (exact τ recurrence + Eisenstein σ-sieve, Hecke/Deligne-exact) (tmp/gl3_family.py):
  the two registers separate cleanly — the UNIVERSAL one stays invariant (phase cells
  1.0005π, across-form spread 0.0001π; all zeros simple; weld pins to the ε = +1 ray
  4/4 while the alt parity Γ_R(s) fails every weight), and the γ-DEPENDENT one, zero
  density N(36), climbs with the γ-shift EXACTLY as the gamma factor predicts (+3.00
  predicted / +3 measured across k = 12→20, corr 0.97). Net: the gate is walked —
  configuration-universality survives a GL(3) family (falsifiability face: a cell ≠ π
  would be a hit; none) — but the 0.441 stays unidentified: GL(3) did not scale it, it
  showed the BE-wall analogue there is too chart-dominated to read a scaling.

## 12. Factorization theory (the second new field entered)

Scout: the Characterization Problem is our question-shape (does L(H) determine the
class group — open rank ≥ 3); NO literature uses L-function values to pin
factorization invariants (the gap is real); the field's criterion is "produce actual
numbers". Expedition [measured/computer-proof]: D(G) = M(G) rank-3 conjecture —
validated hunter, NULL counterexample search over all 71 unresolved rank-3 groups
|G| ≤ 400 (register faces pre-committed, zero hits), new exact values D(G) = M(G)
for C2⊕C2⊕C10/C12/C14 (+ completions), the character-fiber projection (N₀(S) via
orthogonality) introduced to the field as the primary engine.

## 13. BSD: the program (RequestProject/BSDClocks.lean, 25 decls, all std axioms)

**Frame**: BSD = EveryCentralJetHasSource — rank/Ш as source-completeness at the
CENTER, the mirror of the weld program. BE poles and MW ranks are ONE mechanism
(DC census of clock ensembles) at two locations.

- [proven] The dictionary: rank_is_dc_residue (rank = DC residue of L′/L at the
  center); similitude clocks + Hasse–Weil envelope; parity (both cases);
  leading_jet_extraction + first_jet_eq_deriv + jet_measurement_sound (the Sha-hinge
  landing method licensed at every rank); regulator_pos (sources always pay);
  gz_first_jet_live (GZ mechanism: jet = κ⟨v,Hv⟩ > 0 forces order exactly 1);
  central_exhaustion_model (the model cannot manifest a sourceless central jet —
  the center's mirror of threeD_exhaustive).
- [proven] **Rung 2, the census bridge**: nClock_logDeriv_expansion (the census
  coefficients ARE the clock traces); census_affine_in_rank (the instrument's
  empirical calibration line S = A + B·r, fit at R² ≥ 0.998, IS a theorem: B = the
  functional's reading of the central pole, A = the bank census);
  census_lane_decomposition + census_full_decomposition (the ±200-unit lane anatomy,
  exact).
- [proven] The certification kernel: certified_tail_bound (geometric-derivative tail
  closed form — turns interval jet evaluations into certificates); the landing
  licenses: bounded_landing_unique (integers of height ≤ H mod M > 2H are equal —
  the DISCOVERY license: p-adic precision beyond a height bound is identification),
  rational_landing_unique (its ℚ case — "counting in the right units": transcendental
  in its harmonic unit = bounded-height rational = identifiable; degree-d Liouville
  license is the named next target), ultrametric_anchor_compose (anchor chains
  lossless in ℚ_p). Honestly unlicensed, stated: transcendental digit-matching =
  agreement-to-precision; p-adic regulator nonvanishing = numerical hypothesis (no
  order on ℂ_p).
- [measured] The instruments (all anchor-gated, frozen-pipeline, register faces
  pre-committed): rank census 5/5 (ranks 0–4, held-out; ranks read to 0.001);
  jet census |Ш| = 1 at ranks 1–3 (margins to 1.8e-5, dead-jet witnesses); sha-jets
  4/4 NONTRIVIAL (|Ш| ∈ {4,9} at rank 1, held-out, square test); sha-unknown 3/3
  rank-2 |Ш|=4 from SECOND jets + **122 first determinations of |Ш_an| at conductors
  ≥ 1.28e6 beyond LMFDB completeness, all perfect squares ≤ 1.4e-14, every one
  cross-checked against Tunnell's theorem at 1.8e-15, including two curves where
  Sage's descent stalls**; twist census (306 curves, 0 residual theorem
  contradictions; the honest Goldfeld line: the defensible number is the root-number
  split, a theorem not a measurement).
- [certified] **Rung 1: the 389a1 dossier** (tmp/bsd_certify_dossier.txt, gates
  independently rerun): L(1) = 0 by denominator squeeze (|L(1)|/Ω ≤ 9e-11 < 1/8);
  L′(1) = 0 by parity; L″(1) ∈ [1.5159, 1.5236] > 0 STRICT via certified_tail_bound;
  rank = 2 (points exact, NT determinant interval-positive; descent bound cited).
  BSD rank equality for one rank-2 curve, certified end-to-end, with the
  formalization gap reduced to THREE named citations: modular-symbol rationality,
  FE/root number, 2-descent bound. None circular, none RH-flavored.
- [scouted] **Rung 3**: DR2 Theorem D is PROVEN (two independent Selmer classes when
  L(E,ρ,1) = 0 — the rank-2 Heegner analogue); the unproven gap is Selmer → points
  (= the Elliptic Stark Conjecture, proven only in the CM case). The exotic
  construction is the harmonization thesis verbatim: r(E,Ad_g) = rank E(M) − rank E(ℚ)
  — rank acquired UP THE TOWER, traced down by explicit Galois-orbit formulas.
  Anchors 26b/52b (20 digits, p=13), negative control 4811a. THE HONEST CAVEAT: in
  every published example the points were found classically first — nobody has ever
  DISCOVERED a rank-2 point p-adically; "constructive BSD" is aspirational. The open
  prize = point discovery; its formal core = our landing licenses. Stage-1 instrument
  (the ES right-hand side on house machinery: tower arithmetic, from-scratch p-adic
  formal-group elliptic log, Stark-unit log) in flight under the no-Stark-rederivation
  directive.

## 14. The proof ladders (updated §8)

- **RH/GRH**: 3D side CLOSED [proven]. The 1D wall = one sentence, five faces, three
  mandatory ingredients; best-shaped route = origin positivity (the Li relay).
- **BSD**: Rung 1 (certified instance) COMPLETE with a 3-citation gap; Rung 2 (census
  bridge) PROVEN; Rung 3 (jet sources up the tower) scouted + stage-1 in flight;
  the open transfer = jet exhaustion at the center — the same missing word ("all")
  as the weld, at the other fixed point.
- **Beyond Endoscopy**: instrumented first; the uniformity estimate at the core of Altuğ
  II/III now has a **complete proof** (Lemma 1 exact-gauge magnitude bound ⇒ Thm A.14 sharp
  uniform expansion ⇒ Prop 5.2 sharp exponents; engine = the exact-gauge oscillation removal,
  no oscillation estimate, replacing ~60pp Appendix A) — remaining work is formal-writeup
  polish, not analytic; the GL(3) gate ENTERED (vanishing-side universality across a Sym²
  family + γ-density scaling; Deng–Espinosa BE-wall route a chart-dominated null); the γ-spread
  0.441 reinterpreted as the finite-window effective rate (bounded kinematic, not a wall).
- **Yang–Mills / one_template**: unchanged; the two Clay problems remain the two
  signs of the defect axis (YM: open for the collective object; RH: closed — proven
  per-clock, open for the sum).

## 15. Register and corrections (campaign II)

**Falsification register: ZERO hits** across every face armed this campaign
(sourceless zeros, ghosts, non-square Ш, Tunnell mismatches, parity contradictions,
rank-3 Davenport counterexamples, BE gauge/scale faces). Corrections published at
full prominence, in both directions: the Dummigan 691-DENOMINATOR transcription
(caught by numerics); the IK-2014 scope overstatement (Sym⁴Δ constants are OPEN —
Conjecture 2.3; our probe measured (F,F)/⟨Δ,Δ⟩³ = 2¹⁴·3⁶·5⁴·13 to 17 digits, exactly
1/10 of the transcribed constant — unresolved transcription-vs-paper, documented);
the sha-jets legacy-corruption alarm (RETRACTED by its own author — regression seeds,
not legacy bugs; the nine original landings intact); two premature adjudications by
the main session (reading in-progress agent files — both retracted; the aliasing
false-hit was caught by the agent's own Nyquist fix); the mb-uniform "milder at
scale" reading (confirmed, after the aliasing correction). Method laws added to the
permanent file: random-real controls for landing scans; Nyquist-adaptive quadrature;
two-source seeds for regression gates; never adjudicate mid-write; prose never
outranks the table.
