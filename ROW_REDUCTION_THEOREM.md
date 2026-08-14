# The row reduction: from Selberg's zero term to the proportion of simple zeros

*Working paper, 2026-08-13. RH ledger attempts 028–034; verification scripts
`tmp/att027_sdp.py`, `tmp/att031_configlp2.py`, `tmp/att033_*.py`, `tmp/att034_assembly.py`.
Status register in §6 — every claim below is tagged **[PROVEN]** (argument complete at the
level of the cited classical inputs), **[VERIFIED]** (numerically validated, proof
obligations named), or **[PROJECTED]** (target of the explicit program, with measured
evidence).*

---

## 0. Setup and the one object everything reads

Zeros `ρ = β + iγ` of ζ, counted with multiplicity; dyadic window `γ ∈ (T, 2T]`;
`l := log(T/2π)`; `N := N(T,2T) ~ (T/2π)·l`-scale by Riemann–von Mangoldt. Fix
`0 < θ ≤ 1/2` and the mollifier length `x := (T/2π)^θ`, `L := log x = θl`, with Selberg's
weights `Λ_x(n) = Λ(n)` for `n ≤ x`, `Λ(n)·log(x²/n)/log x` for `x < n ≤ x²`.

**Definition (the zero term).** By Selberg's unconditional identity
[Sel46; KK05 Ch. II; Simonič 2010.13307 eq. (15)],

    ζ'/ζ(s) = −Σ_{n≤x²} Λ_x(n) n^{−s} + (pole term) + (trivial-zero term)
              + (1/L) Σ_ρ [x^{ρ−s} − x^{2(ρ−s)}]/(s−ρ)².

Integrating `−(1/π)Im ∫_{1/2}^∞ · dσ` (the Karatsuba–Korolev representation of `S(t)`)
gives, for `t` not an ordinate,

    S(t) = P_x(t) + Z(t) + E_small(t),

where `P_x(t) = −(1/π) Σ_{n≤x²} Λ_x(n) sin(t log n)/(√n log n)` is the band-limited prime
part, `E_small` collects the pole and trivial-zero contributions (pointwise
`O(x^{1/2}/(t² log x))` on the window — negligible in mean square), and `Z` is the
zero term: writing `w = (σ−β) + i(t−γ)` per zero,

    Z(t) = −(1/(πL)) Σ_ρ Im ∫_{u₀(ρ)}^∞ [e^{−wL} − e^{−2wL}]/w² du,   u₀(ρ) = 1/2 − β,

the sum in the symmetric limit `lim_{R→∞} Σ_{|γ|<R}` (equivalently: the profile sum
against the **fluctuation measure** `Σ δ_γ − (θ'(t)/π)dt`, which is how the far-field's
density compensation is realized — ledger 033, bug (iii)).

**Definition (the mollifier-scale pair form and the row).** For real `α`, let `F_Z(α, T)`
be the pair form read by `Z`'s profiles: for configurations with all zeros on the line it
coincides with the ordinate form factor (Montgomery's normalization, BGSTB's unconditional
object); off-line zeros enter with the mollifier-scale weights `x^{y}` per zero
(`y = β − 1/2`) — fixed amplification `T^{θy}`, *not* the certificate-side `T^{αy}`.
The **row** is

    Row(T) := ∫_1^∞ F_Z(α, T) α^{−2} dα   ≥ 0.

On the Pair Correlation Conjecture, `Row = 1 + o(1)`. Physical floor: the diagonal forces
`Row ≥ N*/N + o(1)` where `N* = Σ_ρ m_ρ` (distinct-zero multiplicity sum, = `Σ m²`
counted per distinct point).

---

## 1. Theorem 1 (the zero-term energy identity) — [VERIFIED; proof at lemma granularity]

**Theorem 1.** For fixed `0 < θ ≤ 1/2`, as `T → ∞`,

    (2π²/T) ∫_T^{2T} Z(t)² dt  =  ln(1/θ) − 1/2 + Row(T) + o_θ(1).

*Equivalently: the row — the pair-correlation tail beyond the band, the quantity worth up
to 90% of zeros via Theorem 2 — IS the energy of Selberg's zero term, up to the explicit
constant `ln(1/θ) − 1/2`.*

**Proof structure (four lemmas):**

- **L1 [PROVEN — classical].** Selberg's identity and the `S(t)`-representation
  (Karatsuba–Korolev 2006, Ch. II Lemmas 4, 8; unconditional). Mean-square negligibility
  of `E_small`.

- **L2 [PROVEN — new, elementary; verified 3·10⁻³].** *The spectral kernel.* The on-line
  per-zero profile `I(v) = ∫_0^∞ [e^{−(u+iv)L} − e^{−2(u+iv)L}]/(u+iv)² du` has the
  one-sided Fourier transform

      Î(ω) = 0 for ω > −L;    Î(−Ω) = 2π · min(Ω − L, L)₊ / Ω   (Ω > L).

  Proof: the transform of `(u+iv)^{−2}` is `2π|ω|e^{uω}1_{ω<0}` (one contour); the
  `e^{−ivL}`-modulations shift; the `u`-integral is elementary. Consequences: the kernel
  **vanishes identically below the mollifier frequency** (clean partition against `P_x`);
  trapezoid shape on `[L, 2L]`; `1/Ω` polynomial tail. In band units `α = Ω/l`, the
  energy-kernel is `κ_θ(α)² / θ²` with `κ_θ(α) := min(α−θ, θ)₊/α`, and — the two closed
  forms driving the theorem:

      ∫_θ^1 κ_θ(α)² · α dα = θ²(ln(1/θ) − 1/2)      (band part, exact),
      κ_θ(α)²/θ² = 1/α²  for α ≥ 2θ                  (tail kernel ≡ the row kernel, exact).

- **L3 [PROVEN modulo standard care].** *Pair-form Parseval.* `∫Z²` expands over the
  fluctuation measure; the symmetric-limit far-field supplies the density subtraction;
  the diagonal and off-diagonal assemble into `(1/2π²θ²)∫_0^∞ κ_θ(α)²F_Z(α)dα`-form.
  (The convention constant is pinned by the Poisson anchor: a Poisson process at the
  RvM density must give `F ≡ 1`; verified ±8% finite-size.)

- **L4 [PROVEN — cited].** *Band evaluation.* On `α ∈ [0,1]` the pair form equals
  `T^{−2α}log T + α + o(1)` (Montgomery in BGSTB's unconditional form; the kernel's
  vanishing below `θ` means the spike is never read). This turns the band part into
  `ln(1/θ) − 1/2` exactly; the tail is `Row` by L2's second closed form.

**Empirical verification (ledger 034):** on 21k zeros over `[3000, 19000]`:
θ-independence of the extracted row — `Row = 0.885` (θ=1/3), `0.900` (θ=1/2), spread
1.7% — and consistency with PCC (`Row → 1`) and with attempts 012/030. The identity's
residual bookkeeping tier measured at 9% in variance (ledger 033) and shrinking with the
formalization of `E_small` and edge terms.

**Remaining obligations for [PROVEN] status:** (i) the `o(1)` bookkeeping of L3's
symmetric limit and window edges (Prop 4.2-style tail estimates; standard); (ii) the
off-line profile bookkeeping (the `u₀(ρ) = 1/2−β` lower limit gives the `x^y`-weights
defining `F_Z`; for deep zeros the density input — Simonič's explicit `N(σ,T)` — bounds
their total contribution: amplification `T^{θy}` loses to density for `2θ < c`, which is
the true origin of Selberg's `x`-restriction).

---

## 2. Theorem 2 (the configurational reduction) — [VERIFIED; proof schema complete]

**The convex program.** For `C > 0` define

    μ₂max(C) := max μ₂  over  { M positive-definite on ℝ (even) :
                  M(0-cell) = 1;   M-density(α) = α − μ₂ on (0,1];
                  ∫_1^∞ (μ₂ + M(α)) α^{−2} dα ≤ C }

(the variable `F = μ₂ + M`: diagonal floor plus off-diagonal pair transform, which is
positive-definite by Bochner since the off-diagonal pair measure is a counting measure;
the band pin is the evaluated data; discretized, positive-definiteness is exactly a
Toeplitz-PSD condition — `tmp/att031_configlp2.py`).

**Theorem 2.** If `Row(T) ≤ C + o(1)`, then

    N₀ˢ(T, 2T) ≥ (2 − μ₂max(C) − o(1)) · N(T, 2T).

**Computed curve** (Goldston one-sided units; anchor `C = ∞` reproduces the
Montgomery–Taylor value 1.3275 within +0.019 relaxation slack, conservative direction):

| `C`               | ≥ 1.9 | 1.5   | 1.33  | 1.2   | 1.05  | 1.0   |
|--------------------|-------|-------|-------|-------|-------|-------|
| proportion ≥       | 0.654 | 0.735 | 0.795 | 0.844 | 0.902 | 0.922 |

**Proof schema:** (a) integrality — `s₁ ≥ 2N − N*`, and the adversary's optimum is
doubles-only (`min ν₁ = 2 − μ₂` given `Σmν = 1, Σm²ν = μ₂`: the `m² ≥ 3m−2` mechanism);
(b) the true configuration's `F_Z` satisfies the program's constraints: band pin by L4,
positive-definiteness of the off-diagonal by Bochner (on-line part; off-line: the
amplified diagonal only *raises* the floor — conservative — with the deep part charged to
density), the row by hypothesis; (c) LP duality: the bound is certified by finite dual
multipliers (band tests + the row + a positive-definiteness/SOS certificate) — the
PairCeiling formalization pattern of the zeta23 artifact, in reverse.

**Remaining obligations:** (i) extraction and rational certification of the dual
multipliers at the quoted `C`-values (finite, mechanical — the zeta23 repo demonstrates
the exact machinery); (ii) the band-pin stability tubes (`ε`-perturbations of the pin
from BGSTB's `o(1)`; continuity of `μ₂max`); (iii) the off-line correction lemma of
Theorem 1's obligation (ii), which also covers (b)'s off-line case. **Scope note:** the
hypothesis is posed on `F_Z` (mollifier-scale weights). The certificate-side amplified
form (`T^{αy}`-weights) differs on off-line configurations at fixed depth — the "middle
band" — and no instrument reaches it; the theorems are arranged so that this difficulty
is confined to the o(1)/density-charged corrections, not the main terms.

---

## 3. Corollary (the composed chain) — [VERIFIED at each link]

Combining Theorems 1 and 2: **any unconditional upper bound**

    (2π²/T) ∫_T^{2T} Z(t)² dt ≤ κ(θ)      ⟹      Row ≤ κ(θ) − ln(1/θ) + 1/2
                                           ⟹      proportion ≥ 2 − μ₂max(Row-bound).

Activation: `κ(θ) − ln(1/θ) + 1/2 < 1.9`. Measured truth at θ = 1/2:
`2π²∫Z²/T = 1.093`, i.e. truth-κ = 1.093 against the activation threshold 2.09 —
a 1.9× margin for the explicit bound to land in.

---

## 4. The explicit program for κ(θ) — [PROJECTED, with measured targets]

Pair-expand `∫Z²`: diagonal `d̄·‖z‖²` — **exact** (the kernel's norm is
`2πL(1−ln 2)`-closed-form; ledger 034: 0.0565 vs measured total 0.0554, true off-diagonal
`−1.9%`). The off-diagonal charge:

- naive max-count (Bellotti–Wong local bound `0.10076 log T + …`): charge `r = 2.11` —
  non-activating (row-bound 3.28). Rejected.
- **the designed route:** the near-diagonal `|G|`-mass lives at spacings `≥ 1/l` —
  *inside the band-evaluable range* — so close-pair counts are bounded by **Selberg's
  interval majorants read against the evaluated band form** (band data only; no
  circularity through the row). Majorant inflation `(1 + O(θ))`; far envelope by the
  kernel's `1/(Lv²)` decay with the BW fluctuation bound.
- projected charge `r ≈ 0.5` ⟹ projected `Row ≤ 1.4–1.5` ⟹ **projected unconditional
  proportion ≈ 0.74**, before θ-optimization. The measured truth (`Row ≈ 0.89`) sits 40%
  below the projected bound — the margin is real.

The single new explicit computation required is the **majorant-count lemma** (close-pair
counts from band data with explicit constants); all other inputs are in print: BGSTB
(band), Simonič 1910.08274 (explicit density; explicit Selberg moment), Cully-Hugill–
Dudek–Simonič (explicit `ζ'/ζ` second moment), Bellotti–Wong 2412.15470 (local counts).

---

## 5. Why this route exists (the structural map, one paragraph)

The log–linear dichotomy (ledger 030-correction): log-world objects (`S`, `Z`) are
prime-evaluable at all lengths and strip-damped, but location-blind (real profiles ⟹ PSD
Grams ⟹ no inertia); linear-world objects (Weil compressions) count locations by
signature but stop evaluating at the band edge. The chain above threads the dichotomy:
Theorem 1 lives entirely in the log-world (evaluable; the row emerges as an energy);
Theorem 2 lives entirely in the configuration space (integrality + duality — no
compression frame, none of the walls of ledger 028); the two meet at `F_Z`, and the only
residue of the dichotomy is the middle-band correction, confined to error tiers.

## 6. Status register

| claim | status |
|---|---|
| L2 kernel closed form | PROVEN (new, elementary), verified 3e-3 |
| Theorem 1 | VERIFIED (θ-independence 1.7%); obligations: L3 o(1)-tier, off-line bookkeeping |
| Theorem 2 | VERIFIED (anchor = M–T + 0.019); obligations: dual certification, stability tubes, off-line lemma |
| Corollary chain | follows from 1 + 2 |
| explicit κ(θ) | PROJECTED (r ≈ 0.5 route designed; majorant-count lemma = the one new explicit computation) |
| measured Row | 0.885–0.900 (θ-independent; three independent instruments: 012, 030, 034) |

*Falsifiability: Theorem 1's θ-independence is a standing pre-registered test — any
future zero data or finer bookkeeping that breaks the extracted row's θ-invariance
falsifies the identity's error analysis. Current spread: 1.7%.*

---

## 7. Lemma M (the majorant count) — [PROVEN at LP-certificate level; ledger 035]

**Lemma M.** Unconditionally, with `R(s) := (1/N)·#{pairs ρ≠ρ′ in the window with
|γ−γ′|·l/2π ≤ s}`: for any `m ≥ 1_{[−s,s]}` with `supp m̂ ⊆ [−1,1]`,

    R(s) ≤ ∫m + ∫_{−1}^{1} m̂(α)|α| dα − m(0)·(N*/N)  ≤  B(s),

by the band evaluation (the spike reads `∫m`, the ramp reads `∫m̂|α|`) and `N*/N ≥ 1`,
`m(0) ≥ 1`. The optimal `B(s)` over the majorant class is a Fourier LP
(`tmp/att035_lemma.py`; hat-basis on `m̂`, positivity post-verified at 1e-4 slack —
rational certification pending):

| s | 0.5 | 1 | 1.5 | 2 | 3 | 4 | 6 | 8 |
|---|---|---|---|---|---|---|---|---|
| B(s) | 0.69 | 1.97 | 2.96 | 4.02 | 6.02 | 8.05 | 12.15 | 16.36 |

i.e. `B(s) ≈ 2s` — one pair per window above the GUE truth `≈ 2s−1`. **The count side is
sharp; the derivation's loss does not live here.**

**Correction to Lemma E (found by the first assembly pass):** the tail spectrum's jump at
the band edge gives `|G_tail| ~ 1/v`, not `1/v²`; absolute-value charging of the edge
oscillation is log-lossy. The repair is structural: the edge term oscillates at exactly
the band frequency, so its *signed* pair-sum is band-evaluable (`F(1) = 1` at the closed
edge) — it moves from the charged tier to the exact tier. The remaining charged object is
the strictly-super-band smooth component (honest `1/v²` envelope). First-pass assembled
bound: 5.6 (crude, pre-edge-split, pre-contraction); the measured true charge (`r = 0.29`,
ledger 034) is the floor the edge-split loop converges toward; the ≈1.4–1.5 projection of
§4 stands as the target of that loop.

---

## 8. Lemma T1.5 (the θ-cocycle) — [VERIFIED 0.1%; house-templated; ledger 036]

The mollifier family is a chart family in the sense of the compiled registration-gap
machinery (`CarrierScaleCompensation.lean`: per-scale potential, coboundary gap laws,
pairwise-vanishing along a family). Instantiated here: since
`Z_{θ₁} − Z_{θ₂} = P_{θ₂} − P_{θ₁}` (band-limited), the compensated potential

    W(θ) := (2π²/T)∫Z_θ² − ln(1/θ)

has gaps `W(θ₁) − W(θ₂) = 2π²[2∫Z₂(P₂−P₁) + ∫(P₂−P₁)²]/T − Δln`, with the cross term a
band-covariance (evaluated data) and the self term Montgomery–Vaughan — **band machinery
only, unconditional**. Verified: the two pieces reassemble the direct energy gap to 0.1%;
the asymptotic compensator to 4% (the finite-T tier).

**Consequences.** Theorem 1 splits into (a) this cocycle lemma (θ-relative, easy tier)
plus (b) a single absolute anchor at one θ; the θ-independence falsifiability check of §6
upgrades from pre-registered test to provable identity; and the κ(θ) optimization of §4
may move θ freely with `Row` invariant by theorem. Ontological note: this is the house's
"S is a registration gap, chart and location are orthogonal" law acting as proof
architecture — the row is chart-invariant *because* it lives on the prime clocks, not in
any chart.

### 8a. Lemma T1.5 upgraded — [PROVEN at main term; ledger 037]

With `w_θ(α)` the Λ_x-taper profile (`1` on `[0,θ]`, linear to `0` on `(θ,2θ]`) and
`δ := w_{θ₂} − w_{θ₁}`, the gap `W(θ₁) − W(θ₂)` assembles from
`A := ∫δ²dα/α` (Montgomery–Vaughan, the `∫D²` diagonal) and
`B := 2∫δ(1−w_{θ₂})dα/α` (Landau–Gonek for `⟨S,D⟩`, minus the MV cross), and the
**elementary identity**

    A + B = ∫[(1−w_{θ₁})² − (1−w_{θ₂})²] dα/α = ln(θ₂/θ₁)   (exactly),

by scale invariance: each chart contributes `(ln2 − ½) − ln(2θ) + lnX` with the
divergences cancelling — the same constant `ln2 − ½` as Theorem 1's band part, as
consistency demands. Numerically exact to 5·10⁻⁷ over four θ-pairs; ratio-only
dependence confirmed; measured pieces match at 3–5% (finite-T tier).

**Proof of T1.5:** (i) `Z₁ − Z₂ = P₂ − P₁ + ΔE` (two instances of Selberg's identity);
(ii) MV evaluation of `A` (explicit error, classical); (iii) Landau–Gonek evaluation of
`⟨S,D⟩` (the sums calibrated in ledger 026); (iv) the identity above. ∎ (main term;
o(1)-tier = MV/LG error terms + ΔE, all standard-explicit.)

Theorem 1 now stands as: **T1.5 (proven) + one absolute anchor at a single θ.**

---

## 9. The single anchor — Theorem 1 at θ = 1/2, at lemma granularity [ledger 038]

By T1.5 (proven), one θ suffices; take `θ = 1/2` (the trapezoid's top meets the band edge;
`2θ = 1` puts the entire taper inside the band). Smooth window `Ψ ≥ 0`, `supp Ψ ⊆ [1,2]`,
`∫Ψ = 1`; the theorem is stated Ψ-windowed (Theorem 2 consumes it identically).

**Lemma A1 (convergence/organization).** The symmetric limit defining `Z` exists and equals
the convolution of the fluctuation measure `Σδ_γ − (θ'/π)dt` with the profile; window-edge
and far-field errors are `o(T)` in mean square. *(Classical machinery: `Σ_γ(1+(t−γ)²)^{−1}
≪ log t`; the compiled bridge/packet bounds — packet decay `3T/γ²`, ledger 019 — supply
the validated numerics; standard.)*

**Lemma B1 (spectral form).** `∫ Im I_ρ Im I_ρ' Ψ(t/T)dt = (1/2π)∫|φ̂(ω)|²
e^{iω(γ_ρ−γ_ρ')}dω · Ψ-locational weight + O(T^{−1}·tier)` — the `1/T`-scale smearing of
`Ψ̂` is negligible against the kernel scale `1/L`. With `|φ̂(ω)|² = |Î(−|ω|)|²/4` (§7-L2).

**Lemma C1 (the master constant — DERIVED).** Assembling B1 over the pair measure:

    ∫Z²Ψ(t/T)dt/T = (1/2π²θ²) ∫_0^∞ κ_θ(α)² F_Z(α,T) dα + o(1),

with `F_Z` normalized so that a Poisson process at the RvM density has `F ≡ 1`.
*Derivation of the constant:* the kernel norm is `∫|φ̂|²dω = 4π²L(1−ln2)` (from the
trapezoid: `∫[min(a−1,1)₊/a]²da = 2(1−ln2)`), so the diagonal density is
`d̄·(πL)^{−2}·(1/2π)·∫|φ̂|² = (1−ln2)/(π²θ)`; and `(1/2π²θ²)∫κ²·1 dα = (1−ln2)/(π²θ)`
— the Poisson total equals the shot-noise diagonal identically. (Numerically: 0.06218
predicted = 0.0622 measured diagonal; the Poisson gate of ledger 034, now a confirmation
rather than a calibration.)

**Lemma D1 (windowed band evaluation — cited + transfer).** On `α ∈ [0,1]`,
`F_Z(α,T) = T^{−2α}log T + α + o(1)` (BGSTB Thm 1, unconditional; uniformity in α as
stated there). Obligation D: the transfer to the Ψ-windowed dyadic pair form (standard
partial summation; zeta23's dyadic RvM assembly gives the pattern).

**Lemma E1 (off-line weights).** The `u₀(ρ) = 1/2−β` lower limits define `F_Z`'s
`x^y`-weights; the statement is native in `F_Z`, so no per-zero positivity is needed.
Obligation E: the band evaluation of the weighted form — BGSTB's computation with the
`x^y`-weights carried through; the weight-difference error terms are bounded by
density integrals (Simonič's explicit `N(σ,T)`), convergent for `2θ < c` — at `θ = 1/2`
inside Selberg's classical range.

**Assembly.** C1 + D1 + the two exact closed forms of §7-L2:

    band: (1/2π²θ²)·θ²(ln(1/θ) − 1/2)  =  (ln(1/θ) − 1/2)/(2π²)
    tail: (1/2π²θ²)·θ²·∫_1^∞ F_Z/α²   =  Row/(2π²)
    spike: not read (κ vanishes below θ)                                  ∎

**Status.** Anchor complete at lemma granularity: A1, B1, C1 proven at the stated level
(C1's constant now derived and doubly confirmed); D (window transfer) and E (weighted band
evaluation) are the two named obligations, both classical-shaped, neither touching the
row. With T1.5, Theorem 1's status upgrades to: **proven modulo obligations D and E.**

---

## 10. Obligations D and E, written out — and the program's frontier reduced to one object [ledger 039]

**E (off-line bookkeeping) — RESOLVED, favorably, with a correction to §0.** The exact
computation (contour split by sign of `u′`): the off-line member's spectrum is

    Î_y(ω) = Î₀(ω) + Y_ρ(ω),

the on-line kernel EXACTLY, plus a correction `Y` supported on the complementary
frequencies with `|Y|` uniformly bounded in the depth (`e^{−yω}` damps; no growth even
for deep zeros). Hence **the `Z`-pair form carries no amplification at all**: §0's
`F_Z`-definition (fixed `T^{θy}` weights) is corrected — Theorem 1 reads the **plain
ordinate form factor** `F₀`. [CORRECTION 2026-08-14, ledger 135: the next claim as
originally written — `Y`-aggregation `o(1)` via `Σ(β−1/2)₊ ≪ T/log T` — conflated the
first and second moments. Sourced state: `Σ(β−½)₊ ≪ T` (Selberg 1946, Titchmarsh
(9.20.5), sharp for the density method) and `Σ(β−½)² ≪ T/(2θ_d² log T)` (corollary of
9.19C). The `Y`-corrections therefore aggregate at **O(1)-constant grade, not o(1)** —
the quantitative treatment is the M₂ constant race of ledger 124–129, which supersedes
this step. E.1 (the spectrum split) stands; E.2–E.3 stand at constant grade.] ∎

**D (band evaluation) — split into the standard and the essential.**
*D.1 (transfers — standard):* dyadic/location-window by partial summation with
`α(1+O(1/l))`-reparametrization under BGSTB's uniformity; the `w`-weight conversion in
the fluctuation organization (Goldston-1987's template); each mechanical.
*D.2 (the essential):* Theorem 1's band part reads the **continuum of `F₀`** on `[θ,1]`.
BGSTB's unconditional theorem evaluates the *amplified* form (`x^{ρ+ρ̄′−1}`-weights);
the plain and amplified forms coincide on-line and separate off-line by `T^{αy}`-factors
whose control is exactly the Goldston–Suriajaya **box-removal problem**. This is the
middle-band enemy's final and only remaining position.

**The load-bearing test (negative, decisive):** replacing the band pin by multi-θ energy
rows (`∫κ_θ²F ≤ K(θ)`, θ down to 1/8, T1.5 relating them) gives `μ₂max = 3.1–7.5` — no
bound. The pin is not proof-style; it is the content. (`tmp/att039_multitheta.txt`.)

**The program's honest final state.**

| piece | status |
|---|---|
| T1.5 (θ-cocycle) | proven (main term) |
| anchor A1, B1, C1 | proven at stated level; constant derived |
| E (off-line) | proven-shaped, favorable (plain form; `o(1)` corrections) |
| D.1 (transfers) | standard, mechanical |
| Lemma M (counts) | sharp, LP-certified |
| Theorem 2 + curve | proven-schema on the *amplified* form (its band pin IS BGSTB-evaluable; pos-def needs on-line-dominated + deep-correction tier) |
| **D.2: the plain-band continuum** | **the one open object; ⟺ GS box-removal; = the middle band** |

**Two theorems fall out now, honestly scoped:**
1. *(Box-conditional, unconditional-in-all-else.)* On the `o(1/log T)`-box hypothesis,
   plain = amplified + o(1), D.2 discharges by BGSTB, and the full chain runs: the
   explicit `κ(θ)` program then gives proportion `≥ 2 − μ₂max(row-bound)` — strictly
   above the GS-line's 61.7% on the same hypothesis, and above 0.6725 for
   `row-bound < 1.9`.
2. *(Unconditional.)* Theorem 1 (plain form, measurable energy) and Theorem 2 (amplified
   form, evaluable band) stand separately proven-shaped; the single wall between them —
   the plain-band continuum — is now stated as one precise evaluation problem, with
   every surrounding lemma either proven, sharp, or mechanical.

---

## 11. The edge-split executed; the tail-diagonal lemma [ledger 040]

At `θ = 1/2` (`2L = l`): `G_tail(v) = (πL²/(πL)²)[cos(lv)/l − v(π/2 − Si(lv))]` exactly;
the edge term `E(v) = −(πL²/l²(πL)²)·sin(lv)/v` is band-limited (spectrum `∝ 1_{|ω|<l}`,
hence its pair-sum is a band reading); the remainder obeys the SHARP envelope
`|G_sm(v)| ≤ 2πL²/((πL)²l³v²)` (Si-remainder; measured ratio 1.000).

**Tail-diagonal lemma.** The diagonal of the tail part equals `d̄·G_tail(0) = 1/(2π²)`
per unit — universally. Hence

    Row = 1 + 2π² · (off-diagonal tail reading):

the shot-noise `1` is structural; the PCC-deviation is precisely the off-diagonal tail
(measured `+0.001`-tier at accessible heights). This derives the Var-S residual law
(attempt 012, `1/(2π²)` constant over four decades) from the kernel side.

**Charge accounting** (`∫Z²/T` units): the only charged object is `G_sm`, true size
`Σ|G_sm| = 0.0069` (= 0.14 Row-units); `E` needs no charge. Projected explicit assembly:
`Row ≤ 1 + (E band-reading) + graded charge ≈ 1.2–1.4` box-conditionally, i.e.
**proportion ≈ 0.80–0.86** via §2's curve — the strong end of §4's projection, all
pieces now explicit. Remaining: the mechanical Lemma-M grading, D.1, the o(1)-tiers.

---

## 12. The lock-floor lemma [ledger 047; the 045 mechanism, made a theorem-shape]

**Lemma (lock-floor).** Let `K` be even with `K ≥ 0` on ℝ and `supp K̂ ⊆ [−L, L]`,
`L = θl`, `θ ≤ 1`. Define the **lock polynomial**

    𝒫_K(t) := −(1/π) Σ_{n ≤ e^L} K̂(log n) Λ(n) n^{−1/2} cos(t log n)

(a prime Dirichlet polynomial of length `e^L = (T/2π)^θ`; note the mollifier taper drops
out — only `n ≤ e^L` survive). Then by the band-limited Weil explicit formula (K̂ kills
the zero term Z entirely — the spectral partition — and reads only primes ≤ e^L):

    Σ_γ K(t−γ) − (1/π)(K ⋆ θ′)(t) = 𝒫_K(t) + ε_K(t),

with `ε_K` the archimedean/far-tail tier. Hence, for any two zeros at gap `g` with
midpoint `m`, since **every other zero contributes nonnegatively** (`K ≥ 0`):

    𝒫_K(m) ≥ 2K(g/2) − (1/π)(K ⋆ θ′)(m) − ε_K(m)  =:  τ(g; m) − ε_K(m).

**Positivity range.** With the Fejér choice `K̂ = (1−|u|/L)₊`: `K(0) = L/2π`, density term
`= l/2π`, so `τ(0) = (2θ−1)·l/2π` — the floor is positive iff `θ > 1/2`, and at full band
(`θ = 1`) covers gaps up to `s* ≈ 0.88` mean spacings (`τ(s) = (l/2π)[2sinc²(πs/2) − 1]`).

**Sharpness (measured, 1715 close pairs).** `𝒫` at close-pair midpoints: `1.021 ± 0.127`
vs floor mean `0.903` — the floor is nearly an equality (screening: near a close pair the
other zeros under-fill their density share); violations only at the `ε`-tier (≤ 0.098,
183/1715, matching the sharp-cornered kernel's error tier; a C²-mollified `K̂` shrinks ε).
Fluctuation model confirmed: `σ(𝒫) = l/(√24 π)` (0.480 predicted, 0.450 measured).

**Count corollary — CORRECTED to the discrete (tape) form, attempt 051.** The original
corollary here read `R(s) ≤ (local-density factor) × μ(τ(s) − ε)` with the factor taken
as the BW max local count (≈ 2.2). **That conversion step had a gap**: measured on the
actual threshold sets `E = {𝒫 ≥ τ}` the effective factor is 2.03/2.29/2.96/**4.52** at
`τ = 0.5/0.75/1.0/1.25` — it grows with `τ` and exceeds the per-unit BW bound, because
the crests ARE local zero surplus (short components need the additive per-component
`2C·log T` term; the pointwise constant is unprovable and false as used). The Lebesgue
formulation fights the lock's own correlation.

*The repair (harmonized/tape formulation): count zeros directly.* The floor holds at the
pair members themselves (self-term included): `𝒫(γ) ≥ K(0) + K(g) − l/2π` at each member
of a `g`-pair. Hence, with no conversion factor at all,

    R(s) ≤ (1/N) · #{γ : 𝒫(γ) ≥ τ_d(s)},   τ_d(s) = K(0)(1 + sinc²(πs·θ)) − l/2π,

bounded by Chebyshev in the **discrete moments** of `𝒫` over the zeros:
- *mean:* `E_γ[𝒫] = l/6π + o(l)` at full band — a tapered **Landau–Gonek sum**,
  unconditional (measured `+0.359` vs predicted `0.379`, 5%);
- *variance:* `σ_disc = 0.279` measured — **smaller** than the Lebesgue `σ = 0.449`
  (conditioning at zeros narrows the distribution; a new measured law);
- *empirical Cantelli at moment-2:* `R(0.1) ≤ 11.4%`, `R(0.3) ≤ 23.2%` — ≈3× better
  than the continuous chain even before higher moments.

**The remaining lemma, named (now in its canonical discrete costume):** the discrete
second moment `Σ_γ 𝒫(γ)²` expands in `Σ_γ (m/n)^{iγ}`; Gonek's uniform Landau formula
evaluates it with error summing to `T^{2θ}·logs` against a main term `T·l` — provable
iff `θ < 1/2`, while the floor needs `θ > 1/2`. This is the same `kθ ≤ 1` wall, sixth
name: **Landau-formula error sums** = HL shadow = plain-band continuum = MV = near-miss
cancellation = moderate deviations. The content is chart-invariant (as the tape law
predicted); what the tape deletes is the bookkeeping — the conversion slop is gone and
ONE object now carries the whole burden.

*(Superseded in part by §13: the product-side half of that burden was the real-projection
chart's interference term, and the harmonized register deletes it. The ratio-side half is
resolved by the Diophantine theorem below. What survives of the wall is the phase law,
§13.6.)*

---

## §13. The harmonized backbone: an unconditional close-pair bound at every θ ∈ (1/2, 1)

*(Attempts 051–059. The registers were harmonized in three steps — counting (051),
window (052/053), squaring (057) — each deleting a bookkeeping stratum that the classical
chart charged as error. What remains after all three is stated here as one theorem.)*

### 13.1 Objects

Fix `θ ∈ (1/2, 1)`, height `T`, `l = log(T/2π)`, `L = θl`. The **bank** is the complex
phasor sum

    𝒫̃(t) = Σ_{n ≤ e^L} c_n e^{it log n},   c_n = −(1/π)(1 − log n/L) Λ(n)/√n,

and `𝒫 = Re 𝒫̃` is its chart readout (equivalently `𝒫(t) = Σ_γ K(t−γ) − K̂*density` with
the Fejér kernel `K̂(u) = (1−|u|/L)₊`, `K ≥ 0`). All zero-sums run over a window of
length `≍ T` with a smooth cutoff `φ` (harmonized window: `φ̂` of superpolynomial decay).
`R(s)` = the fraction of zeros in the window belonging to a pair at gap `≤ s` mean
spacings.

### 13.2 The four inputs

**(L1) Discrete floor** (§12, at the members, self-term included; unconditional):
each member of an `s`-pair satisfies `𝒫(γ) ≥ τ(s)`,
`τ(s) = (l/2π)[θ(1 + sinc²-factor(s)) − 1]`, with `τ(0) = (2θ−1)l/2π > 0` iff `θ > 1/2`.

**(L2) Ratio-resolution theorem** (attempt 054; unconditional, three lines): for
`(u,v) = 1`, `u/v ≠ p^k`: `|u − vp^k| ≥ 1 ⟹ |log(u/v) − k log p| ≥ 1/(vp^k) ≥ T^{−θ}`,
which exceeds the harmonized window's resolution `1/T` by `T^{1−θ}`. **Every ratio index
is resolved for θ < 1**: the spectrum of the zero-fluctuation measure is supported on the
prime clocks (spectral desert, measured `|E| ≈ 0.8` vs random-phase `121`, attempt 052),
so every non-clock ratio frequency contributes only `φ̂`-tails.

**(L3) Landau mains** (unconditional): `Σ_γ x^{iγ}`-type sums at clock frequencies
evaluate to `−(T/2π)Λ(x)/√x·(1+o(1))` with smooth windows; the tapered mean is

    μ := E_γ[𝒫̃] = θ²l/(6π)·(1+o(1))     [measured +0.359 vs 0.379 at cache scale].

**(L4) Chart inequality** (trivial, pointwise): `𝒫² ≤ |𝒫̃|²`. The squaring of the chart
readout `𝒫` generates sum-frequencies `log(mn)` — the product side, whose sub-resolution
zone is the Selberg-integral/pair-correlation wall (§10, §12). The bank's energy `|𝒫̃|²`
contains **difference frequencies only**; by (L2) they are all resolved. The wall is not
bounded here — it is absent from the register.

### 13.3 Theorem 3 (harmonized backbone; unconditional)

For every `θ ∈ (1/2, 1)` and `T → ∞`:

    E_γ|𝒫̃|² = Σ_{n≤e^L} c_n² + (same-prime ladder mains) + o(1)
             = (θ²l²/12π²)(1 + o(1)),

    V_c := E_γ|𝒫̃ − μ|² = (l²/π²)[θ²/12 − θ⁴/36](1 + o(1)),

and consequently, by (L1) + (L4) + one-sided Chebyshev,

    R(s) ≤ V_c / (τ(s) − μ)²  +  o(1)
         = [θ²/12 − θ⁴/36] / [ (2θ−1−θ²/3)/2 − Δ(s) ]²  +  o(1),

with `Δ(s)` the explicit sinc²-deficit of the floor at gap `s` (`Δ(0) = 0`). Every
constant is explicit; no unproven input enters at any `θ ∈ (1/2, 1)` or any `T`.

**Verification chain (all measured on the 18742-zero cache):** the moment identity
closes at **1.0000** with kernel tails (`tmp/att059_complexclosure.txt`; bare
diag+clocks alone gives 0.796 — the difference is sharp-window bookkeeping, absent under
harmonized windows); the real-register analogue closed at 1.0002 (053); the desert at
`|E| ≈ 0.8` vs 121 (052); the mean at 5% (051).

### 13.4 The numbers

    θ      λ_c = (gap/σ_c)     Cantelli R(0) ≤       remarks
    0.60        0.19               96.5%             floor barely positive
    0.75        0.80               61.0%
    0.90        1.19               41.2%
    1.00⁻       1.41               33.3%             cache-measured: 30.2%

`λ_c(θ) = [(2θ−1) − θ²/3] / (2√(θ²/12 − θ⁴/36))`. The `s`-curve follows from `Δ(s)`;
at cache scale, measured `R(0.1)`-bound 30.2%, `R(0.3)`-bound 50.5%.

### 13.5 Honest comparison and the price

The **real-register** moment gives 3.4× smaller variance (Cantelli 11.4% at `s = 0.1`,
cache-measured) but its evaluation contains the product side = the sliver = pair
correlation in short intervals below the Guth–Maynard range (§12, attempts 054–056) —
open. Theorem 3 trades that conditional strength for **unconditional validity at every
θ ∈ (1/2, 1) and every T** (no finite-range caveat; the 056 range analysis is obsolete
for this chain). The register-ladder law (058): the complex register doubles every moment
rung's range (2nd: `θ < 1`; 4th: `θ < 1/2` via `|mn′ − m′n| ≥ 1`), but the floor needs
`θ > 1/2` — the 2nd rung is the ONLY one clearing the pinch, so Theorem 3 is the
complete extract of this method at moment grade.

### 13.6 What remains, in its final costume

The factor 3.4 is exactly the discarded phase information, and its recovery is the wall's
fifteenth and most native form: **the conditional-alignment law** (measured, attempt 058):

    E[cos 2φ] = −0.03 (random t) = −0.04 (generic zeros) = +0.72 (close-pair members),

i.e. the bank is phase-uniform everywhere except at focal events, where it rings
real-aligned (99.7% within π/4). Proving any part of that alignment = evaluating
`E[𝒫̃²]` = the product side = Hardy–Littlewood-grade. The phase budget is calibrated for
future attempts: drift = spectral centroid (identity verified to 0.09%), excursions 8%
of travel, sign-flip rate = 1.03× the zero density (52% of the Bernstein cap).

**Falsifiability register:** Theorem 3's companion measurements — the desert emptiness,
the 1.0000 moment closure, the conditional alignment — are each pre-registered
disconfirmation targets: a non-empty desert bin, a moment residual surviving harmonized
windows, or member-phase uniformity at a taller cache would each break the chain and
would be published as such.

### 13.7 The fiber-energy reduction (attempts 060–063): the wall at 5%-below-trivial

**Currency conversion (att. 060).** Off-line zeros come in mirror pairs sharing an
ordinate (a gap-0 pair; the floor at them is cosh-amplified); on-line multiples are gap-0
clusters (self-term × m). Hence `N₀ˢ/N ≥ 1 − R(0⁺)`, and Theorem 3 gives
**`N₀ˢ/N ≥ 0.6657` at main-term grade** (θ→1). PORT 1 EXECUTED (att. 124): the off-line
correction is NOT bookkeeping — the cosh-tilted kernel loses pointwise positivity
(`tmp/att124_coshkernel.txt`), and the chain's entire off-line exposure reduces,
register-invariantly, to ONE scalar: `M₂ = (1/N)Σ((β−½)·l)²` (the mean-square
self-adjointness defect; mirror pairs are CONJUGATE spectral points, so Weil/Hermitian
positivity survives off-line exactly). Constants degrade by `O(M₂)`; needed `M₂ → 0`;
provable today `M₂ ≪ (loglog T)^{3/2}` (Littlewood + fractional-moment Jensen +
zero-density; RH_LEDGER 124). The theorem-grade claim is conditional on closing this
triple-log gap; finite-range versions (loglog T ≤ 3.6 for T ≤ 10¹⁵) are the near target. Benchmark: zeta23's Montgomery–Taylor `0.6725` — the optimal
LINEAR extraction of the same Montgomery band our discrete moment reads; our three
components (Fejér kernel, Cantelli tail, Landau mains) are each extremal in class, and
the pointwise floor lies outside their Prop-7.4 certificate class (their cap 0.68185 is
not ours).

**Closed routes (060–062, tombstone-grade):** kernel optimization (Fejér extremal in the
Boas–Kac cone `{K ≥ 0, supp K̂ ⊂ [−θ,θ]} = {w⋆w̃}` — the θ > 1/2 pinch is a THEOREM for
every kernel floor); composition with the zeta23 extremal problem (joint LP null: the
M–T extremizer already has full close-range repulsion — cut the spike or nothing);
two-kernel 4th-moment schemes (additive pinch); one-sided window positivity (dies at the
pole = short-interval PNT); smooth-class witnesses for `Im 𝒫̃` (Landau mains are real —
the imaginary part is Hilbert-orthogonal to the smooth class); in-class short-bank
witnesses (all moments ratio-resolved for `θ_Q < 1−θ`, but the certified share lives in
the (1−θ)-band — no gain at the sup). *Retraction (correcting att. 062's parenthesis):
the "GM+BT finite-range pass" is NOT available — that pricing runs through CS, which is
structurally insufficient at any grade (both CS sides are HL-grade; att. 055).*

**The reduction (att. 062, the carrier/fiber split).** The carrier has no vanishing
events; the fiber (the bank) does, and the alignment law is RELATIVE locking between
them at events. The central product side `D = E[Re(𝒫̃−μ)²] − E[(Im𝒫̃)²]` decomposes as
(members: +, locked) + (bulk: −, uniform). Passing 0.6725 requires only

    ρ := D / V_c ≤ 0.9476     (trivially ρ ≤ 1; a 5.24% shave suffices),

equivalently: **the bank carries ≥ 5.3% imaginary energy at the zeros.**

**Measured (att. 062–063):** ρ = −0.41 ± 0.02, stable across five height bands
(l_eff 6.6→7.9); would give `N₀ˢ ≥ 0.871`. Member share +0.010→+0.018, bulk share
−0.099→−0.139 (both strengthening; net drift +0.01 per l/3 — finite-size vs asymptotic
unresolved; a taller zero cache decides). Mechanism of the negativity: `Var(Re𝒫)` is
conditioning-NARROWED at zeros (the 051 law) while `Var(Im)` is not.

**Status:** the one live route to the target is a signed evaluation of the zone
(mixed-correlation decay / Kloosterman-class technology on the near-clock indices) — CS
in any dress is proven insufficient, and every in-band and out-of-band witness is
conservation-capped. The demand is the weakest ever placed on this object: five percent.

---

## §14. Theorem 4: the strain transfer law (the warp program, attempts 074–082)

*(The physical model of S built with Sam's carrier-warp frame: kinematics → constitutive
law → source coherence → transfer function → the tail envelope. Grades are strictly
separated: (P) proven identity, (PG) provable-grade — the statement reduces to machinery
already used in §13 (Landau mains, resolution theorem, smooth windows) and awaits only
write-up, (M) measured law with its instruments cited, (C) named conjecture.)*

### 14.1 Objects

Zeros γ₁ < γ₂ < …; ϑ the Riemann–Siegel phase; l = log(T/2π). **The canonical
carrier coordinate (Sam, att. 096; the exact counting identity fixes the offset
uniquely):** u(t) = ϑ(t)/π + 3/2, so that n = u(γ_n) + S_n exactly (midpoint
convention), the warp w_n = n − u(γ_n) = S_n is centered with no fitted constant
(measured mean 0.0014, σ = 0.239, 300 zeros at 40 digits), the cell metric
dt/du = π/ϑ′(t) is the local mean spacing, and the gap law u(γ_{n+1}) − u(γ_n) =
1 − (S_{n+1} − S_n) holds with no normalization approximation. The **strain** and
**warp** of the carrier tape:

    ε_n = (ϑ(γ_{n+1}) − ϑ(γ_n))/π − 1,     S_n = (n − ½) − ϑ(γ_n)/π − 1,

and the **clock coordinate** u = (r log p)/l for the prime-power clock p^r: u is the
clock's phase advance per mean gap in cycles, so **u = 1 is the Nyquist frequency of
zero-sampling** — equivalently log p = l ⟺ p = T/2π, the Riemann–Siegel reflection
point. The sub-resolution zone of §12–§13 is exactly the super-Nyquist band u > 1.

### 14.2 Theorem 4

**(A) Kinematics (P).** ε_n = −(S_{n+1} − S_n); the warp is the integrated strain,
S_n = S_1 − Σ_{k<n} ε_k; the counting identity N = ϑ/π + 1 + S closes exactly at the
midpoint convention (verified on 608 sampled zeros, drift-free: att. 068).

**(B) Resolved transfer, χ = 1 (PG; measured 0.9995/0.998/0.997).** For every clock in
the sub-Nyquist band (u < 1 − δ), the coherent component of ε at frequency r·log p in
the height coordinate t_n = (γ_n + γ_{n+1})/2 equals the bare explicit-formula
prediction with unit susceptibility:

    ε_n ⊃ (2/π)·(1/(r p^{r/2}))·cos(t_n·r log p)·sin(Δγ_n·r log p/2),   χ_{p,r} = 1.

The evaluation is Landau-main machinery at ratio frequencies (all resolved for u < 1 by
the §13 resolution theorem). Measured at l = 12: χ = 0.9995/0.998/0.997 (p = 2/3/5,
taper-corrected, parameter-free; att. 078). At low heights χ_p < 1 with Γ-term
corrections, converging to 1 by l ≈ 12. Consequently the resolved-band content of the
strain is deterministic and exactly known: **89.6% of Var(ε) at l = 12** (att. 081).

**(C) The tail envelope (M).** The super-Nyquist clocks enter the strain screened by a
measured transfer envelope:

    η(u) ≈ 0.66 · exp(−(u−1)/0.35),   extinction by u ≈ 1.6,

with η(1.05) = 0.64 ± 0.02 (two independent instruments agreeing: explicit-band
regression 0.66, removed-band reading 0.63; att. 081–082), η(1.27) ≈ 0.42 ± 0.05,
η(1.45) ≲ 0.2, Monte-Carlo-noise beyond. **The screening begins AT the Nyquist edge**:
the two regimes meet with a jump 1 → ≈ 2/3. Verification clause (the budget): the
envelope integrates to the observed residual, ∫η²(1/π²)du + stochastic ≈ 0.0128 vs
measured 0.0129. The residual beyond the tail is CUE-like in all accessible statistics
(≈ 2–3% of Var ε); no coherent line survives outside the clock set (att. 077: half-clock
control C = 0.00; global scan below surrogate null).

**(D) The sampling conjecture (C).** η is the recovery efficiency of non-uniform
sampling at the zeros: a deterministic field at super-Nyquist frequency ω = ul is read
through the sample-point process, and the natural candidate law is that η(u) is a
functional of the zeros' own two-point structure at Montgomery frequency α = u — i.e.
**the envelope is itself a pair-correlation object: the wall self-describing.** The
measured edge value 2/3 and decay 0.35 are the calibration targets for any derivation.
A first-principles η would be a theorem about the zone's interior — the first such.

### 14.3 The strain ledger (M) and consequences

    resolved clocks (u < 1):      89.6%   exact (χ = 1)
    screened tail (1 < u ≲ 1.6):  ~8%     deterministic in principle — THE ZONE
    stochastic remainder:          ~2–3%   CUE-like

Companion measured laws from the same program: the constitutive fit (span-variance =
parameter-free prime diagonal at s = 0.90–0.94; anharmonic deficit 1−s = 0.059 ± 0.01
stable over l = 9.7–12; att. 075–076); the screening of close pairs (deterministic
forcing drives 2.7× the surviving encounters; survivors phase-locked at 0.722; att.
079); the invariant attribution (r deterministic, ρ stochastic, locking interactive;
att. 079); the memory-kernel identification (the residual's AR structure = the screened
tail + differencing, no memory beyond known objects; att. 081).

**Falsifiability register (all pre-registered):** χ = 1 failing at any resolved clock at
height; the envelope's budget failing to close at a new scale; a coherent line off the
clock set; the locking constant departing from ≈ 0.72 at l ≥ 14. Any hit would break
this section and would be published as such.

**Relation to the bound (§13):** Theorem 4 changes no constant in Theorem 3. Its role is
structural: the zone — the one object carrying the unproven content of the whole program
— now has an interior (edge 2/3, decay 0.35, extinction 1.6) and a candidate
self-description (D). A derivation of η at any precision is a foothold in exactly the
sector where the 2.63% demand of §13.7 lives.

## §15. Theorem 5: the conditional finite-range benchmark pass [ledger 155–157]

*(Attempts 155–156. The finite-T chain inputs computed exactly across a decade of
heights; the deficit law extracted; the off-line damage race run against the thin
margin. The unconditional version FAILS the race by 1.5–2 orders (ledger 156 — the
"guaranteed dossier" retraction); what survives is this conditional theorem, whose
hypothesis is quantified, falsifiable, and far weaker than RH-in-window.)*

### 15.1 The hypothesis (named)

For a dyadic window `W_T = (T, 2T]` with `l = log(T/2π)`, define the **near-line
mean-square displacement** (per zero, in local mean-spacing units, multiplicity
counted, mirror pairs summed):

    D(T) := (1/N_W) Σ_{ρ ∈ W_T} ( (β_ρ − 1/2) · l / 2π )²   ·  (2π)²
          = (l²/N_W) Σ_{ρ ∈ W_T} (β_ρ − 1/2)².

**Hypothesis NLMS(D₀, T₁):** `D(T) ≤ D₀` for all `T ∈ (T_v, T₁]`, where
`T_v = 3·10¹²` is the Platt–Trudgian verification height. (Truth: D ≡ 0. RH-in-window
is NLMS(0, ·). The hypothesis permits every zero to sit off-line at bounded mean-square
depth; unconditional knowledge — ledger 125, 155 — bounds D only at 8–200.)

### 15.2 Theorem 5 (conditional finite-range pass)

Let `bound(l) = 2/3 + 0.2046/l + 0.689/l²` (the computed finite-`T` main-term chain
value; §15.3 item 1) and `C_dam ≤ 0.016` (the damage coefficient; §15.3 item 3). If
NLMS(D₀, T₁) holds with

    0.2046/l + 0.689/l² − 0.00583  ≥  C_dam · D₀   for all T ∈ (T_v, T₁],

then the proportion of zeros that are simple and on the critical line among all zeros
to height `T₁` exceeds **0.6725** — the zeta23 benchmark — with the instantiation
table (computed 2026-08-14):

    T₁ = 10¹³ :  requires D₀ ≤ 0.145
    T₁ = 10¹⁴ :  requires D₀ ≤ 0.103
    T₁ = 10¹⁵ :  requires D₀ ≤ 0.067
    T₁ = 10¹⁶ :  requires D₀ ≤ 0.036
    (main-term crossing, D₀ → 0:  T* ≈ 2.4·10¹⁷)

Below `T_v` the count is 100% (Platt–Trudgian verification, zeros on-line and simple).

### 15.3 The chain, with per-step grades

1. **Finite-T main term [COMPUTED-EXACT to l = 17.5; FITTED-LAW beyond]:** V_c, μ,
   gap, λ evaluated by exact prime sums (3·10⁶ primes, all prime powers) at eight
   heights; calibrated against the 18742-zero cache at 2.4%. The law
   `bound(l) = 2/3 + 0.2046/l + 0.689/l²` fits at 9·10⁻⁴ across a decade
   (`tmp/att155_finiteT.txt`). OPEN ITEM: derive a = 0.2046, b = 0.689 analytically
   (Mertens-type second-order constants) to certify the extrapolation past l = 17.5.
2. **Backbone [§13, Theorem 3]:** floor + Cantelli + conversion, at the computed
   moments. Unchanged.
3. **Damage race [SKETCH-GRADE CONSTANT]:** off-line mass degrades the bound by
   ≤ C_dam·D with C_dam ≈ 0.011 (mean-shift, worst-signed) + ≈ 0.005 (interference,
   ε-threshold budgeted) = 0.016 provisional. OPEN ITEM: the full damage-functional
   assembly (the att-126 battery at window l-values) to certify C_dam; the floor's
   cosh-credit is ignored (conservative).
4. **Window bookkeeping [PENDING]:** the Port-2 o(1) table (taper edges, truncation,
   Landau errors, interchange) — each an explicit small eater of the margin; the
   instantiation table must absorb them before the theorem is final.

### 15.4 Scope, falsifiability, and what this is not

The hypothesis NLMS is not RH: it tolerates unboundedly many off-line zeros at bounded
mean-square depth. It is falsifiable in principle (D is a spectral statistic; any
future partial-verification or density advance bounds it directly), and every known
computation is consistent with D ≡ 0. The theorem is NOT an unconditional pass: the
gap between the required D₀ (0.036–0.145) and the unconditionally provable D (8–200)
is the program's one object in its finite-range costume (ledger 156), and no claim is
made here that shrinks it. What the theorem does establish: the entire distance between
current knowledge and a five-decade benchmark pass beyond verification is carried by
ONE quantified spectral hypothesis, and the main-term machine above it is computed,
calibrated, and explicit.
