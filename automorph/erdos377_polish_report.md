# Polish report (pass 2) — `erdos377_partial.tex`

Written for the auditor. Line numbers are the **post-edit** file (2147 lines).
Companion to `erdos377_appendix_report.md` (pass 1); D-numbers below refer to
that report's discrepancy list.

---

## 0. Status

| Item | Status |
|---|---|
| Consistency read, whole document | **COMPLETE-WITH-MISMATCHES** — 6 mismatches found, 2 of them consequential (`[B1]`, `[B2]`); both reported in-place in §B.9 and here, neither silently resolved |
| Rendering | **COMPLETE** — all 11 `Lemma~B.\ref` constructions normalized; all refs resolve; the `[Exact constants to be finalised]` placeholder is gone (Lemma `measure` finalized *and* reframed); abstract and Theorem 1 now carry the explicit rate |
| Constants | **COMPLETE-WITH-MISMATCHES** — first-sum accounting propagated; `A`/`T₀` confirmed consistent; **the target in `eq:weyl` does *not* match what ETK + assembly consume** (`[B2]`) |
| Provenance | **COMPLETE** — input list (i)–(iv) including PNT, five Lean anchors listed, defensive disclaimers removed, numerics remark relabelled |
| Compile | **COMPLETE** — 28 pp., 0 errors, 0 undefined references, 0 multiply-defined labels, 0 underfull vboxes, **0 overfull boxes beyond 10 pt** (7 remain, max 9.87 pt) |
| Lean file | **UNTOUCHED** |

**Release gate.** The document should not ship until `[B1]` is decided. It is a
one-line change either way and nothing downstream moves, but as it stands the
main text asserts `F ≤ HQ^J` and `r_max = 3J+3` for a level set on which the
true bounds are `F ≤ HQ^{J+1}` and `r ≤ 3J+5`.

---

## 1. Mismatches found (reported, not resolved)

### `[B1]` — the amplitude range under the top-level exclusion. **Consequential.**
*Locations:* main text lines 209, 241, 381, 470; appendix `eq:Frange` (line 965),
table row 1 (line 1667), `eq:xrange` (line 1638), `eq:rmax` (line 944), and
the verification paragraph at line 1696. Recorded in-document at §B.9, line 1840 ff.

The amended Proposition `equi` uses exponents `k−1,…,k−J`, which in Appendix B's
indexing (`j_i = k−i+1`) is the level set `i = 2,…,J(k)+1` — appendix §B.6(d).
But `eq:Frange` was derived for the level set `i = 1,…,J`. With `F = |h_{i₀}| t Q^{i₀−1}`,
`t ≤ Q`, `|h| ≤ H` and now `i₀ ≤ J+1`:

```
Q  <=  F  <=  H Q^(J+1)          (one power of Q above the stated  F <= H Q^J)
x  =  log F / log N  <=  3(J+1) + o(1)      (log N >= (1/3) log Q (1-o(1)))
r  =  max(2, ceil(x)+1)  <=  3J+5           (stated: r_max = 3J+3)
```

*Provenance of the slip:* the pre-amendment text said `F ≤ HQ^{J+1}`, which was
correct for **its** indexing; pass-1 report item D5 called the sharp bound
`HQ^J`, correct for the **appendix's** indexing; the amendment adopted route (d),
which shifts the level set up by one, and kept `HQ^J`.

*Proposed resolution (recommended).* `r_max := 3J+5` in `eq:rmax`, and
`F ≤ HQ^{J+1}` at all six sites. Consequences, all inert: `ϱ = k+3J+5`;
`η' ≥ 2^{−3J−6}` rather than `2^{−3J−4}`, still `exp(−O((loglog n)^{1/3}))`;
§B.8's first display holds with `c` enlarged from `4log2` to `5log2`
(it needs `(3J+6)log2 ≤ c(loglog n)^{1/3}`, and `J ≤ (loglog n)^{1/3}+1`).
Lemma `dominance`'s hypothesis, `T₀`, the block count and the Type II bound
all absorb the change without alteration.

*Alternative resolution.* Use the levels `k−1,…,k−J+1` (one fewer). Then
`F ≤ HQ^J` and `r_max = 3J+3` stand verbatim, at the cost of `2^{−J(k)} →
2^{−J(k)+1}` in §assembly — an absolute factor 2, invisible in the rate.

### `[B2]` — the target exponent in `eq:weyl`. **Consequential.**
*Locations:* `eq:weyl` (line 190); appendix `eq:blocksum` closing sentence
(§B.3, lines 1202–1206); `eq:T0`; §B.9 first paragraph. Recorded in-document at
§B.9, line 1868 ff., with a forward pointer added at §B.3 (line 1204).

`eq:weyl` asks for `S(h) ≪ π(P)(log P)^{−A}` with `A` **fixed**. That is not
what the Erdős–Turán step consumes. With `u = log log n`: the band has
`N ≫ P/log n` primes so `π(P)/N ≪ k`, and at `k = K = (log n)^{1−ε_n}`, where
`log P = (log n)^{ε_n} = e^{u^{2/3}}`, the relative error delivered to
Theorem `ET` is

```
<<  J (3 log H)^J  ·  k  ·  (log P)^(-A)
 =  exp( u  -  (A+1) u^(2/3)  +  O(u^(1/3) log u) )
```

which is `≤ (log n)^{−1} = e^{−u}` only if `A ≥ 2u^{1/3} − 1`. **No fixed `A`
suffices**, so the chain "eq:weyl (fixed A) → ETK → Prop equi with
`o(1) ≤ (log n)^{−1}`" does not close as stated.

*Why nothing is actually broken.* §B.8 proves the stronger, `log n`-measured
bound — `L^{η'} ≫ (log n)^A` for every fixed `A`, i.e. per-block saving
`exp(−exp(u^{2/3}(1+o(1))))` — and §B.9 consumes **that**, not the `(log P)^{−A}`
proxy. The defect is in the statement of the intermediate target only.

*Proposed resolution.* Restate `eq:weyl` as `S(h) ≪ π(P)(log n)^{−B}` for every
fixed `B`, and substitute `log n` for `log Q` / `log P` in §B.3's closing
sentence, in `eq:T0` (`(log Q)^{10A+40} → (log n)^{10B+40}`), and in §B.9's
bookkeeping. No estimate changes: `Q ≥ exp(½(log n)^{ε_n})` still dominates
`T₀ = (log n)^{O(1)}`, and all three Type II terms keep the same margin.
Verification that `B ≥ 2` suffices: `(3log H)^J = exp(O(u^{1/3} log u))` and
`k ≤ log n`, so `J(3log H)^J k (log n)^{−B} ≤ (log n)^{−1}` for `B ≥ 2` and `n`
large.

### `[M3]` — `eq:Jk` off by one.
*Location:* appendix `eq:Jk` (line 929): `J(k) := min{J, k}`. Main text
Proposition `equi` (line 170): `J(k) := min(⌈(loglog n)^{1/3}⌉, k−1)`.
Consistent with the index shift (the appendix needs `j_i ≥ 1` for `i ≤ J(k)`
with `j_i = k−i+1`; the main text needs `k−J ≥ 1`), but the two displays read as
contradictory. *Proposed resolution:* leave `eq:Jk` as the appendix's own
convention and rely on the new bridge Remark (line 872), which is what I did; or,
if `[B1]` is resolved by the recommended route, change `eq:Jk` to `min{J, k−1}`
so that the appendix's level set `2,…,J(k)+1` also satisfies `j_i ≥ 1`.

### `[M4]` — Lemma `typeI` is stated for a single monomial, used for a sum of them.
*Location:* Lemma `typeI` (line 358): `g(l) = c n l^{−j}`. The phase actually
estimated is `Ψ_h(x) = Σ_i h_i n x^{−j_i}`. The bridge is Lemma `dominance`,
which §equi cites at the point of use (line 207), so the argument is complete;
but the lemma as displayed is narrower than its application.
*Proposed resolution:* state Lemma `typeI` for the band phase of `eq:phase`,
with the dominance hypothesis as a standing assumption — or add one clause to its
statement pointing at Lemma `dominance`. Not applied: frozen statement.

### `[M5]` — two accountings of the small-`k` bands (slack, not contradiction).
Appendix `[A1]` (line 800) bounds the bands `k < J` by `Σ 2^{−k}/k = O(1)`;
the main-text remark (line 275) bounds them trivially by `Σ_{k≤J} 1/k ≪ logloglog n`.
Both are true, the appendix's is sharper, and `logloglog n ≪ (loglog n)^{2/3}`
so the stated rate is unaffected. No action needed; flagged so the auditor is
not surprised by the discrepancy.

### `[M6]` — Lemma `measure`'s original range was too generous. **Resolved under
explicit license** (the prompt directed me to finalize or reframe this lemma).
As printed it claimed the log-uniform law for all `1 ≤ a < b ≤ n^{1/(k+1)}`.
The relative error is `o(1)` only when `log(b/a) ≫ log n · e^{−c√(log P₀)}` — for
`b` near `n^{1/(k+1)}` the claim exceeds what PNT-with-classical-error gives,
which is exactly the content of Remark `noshortcut`. The finalized statement
carries the error term explicitly and the proof states the range in which the
relative error is `o(1)` (all `ν ≤ T₀ = (log n)^{O(1)}`, with exponential margin).

---

## 2. Every change, by location

### Rendering / references
| # | Location | Change |
|---|---|---|
| R1 | lines 206–207, 221, 247, 356, 370, 385–386, 440, 442, 449 | All 11 `Lemma~B.\ref{…}` / `Lemma~A.\ref{…}` / `eq.~B.\ref{…}` constructions normalized to `\ref` / `\eqref`, with `Appendix~\ref{app:regimes}` prepended where a bare number would be uninformative. Verified: `grep -c "~[AB]\.\\ref"` returns 0 |
| R2 | — | **Numbering decision:** flat theorem numbering retained rather than switching to `\newtheorem{theorem}{Theorem}[section]`. Per-section numbering would produce "Lemma B.1 … B.10" alongside the appendix's own `§B.0 … §B.9` headings, with different content at nearly every index — a collision at maximum density. Navigability is instead supplied by the `Appendix~\ref{…}` qualifiers |

### Main text — consistency with the amendment
| # | Location | Change |
|---|---|---|
| C1 | 23–41 (abstract) | Explicit rate `loglog n + O((loglog n)^{2/3})`; sentence added naming what is proved here vs. the one imported theorem; conjecture formula moved to a display (also clears a 21.2 pt overfull) |
| C2 | 47–54 (Theorem 1) | `(1−o(1))loglog n` → `loglog n + O((loglog n)^{2/3})`, "with an effective implied constant" |
| C3 | 56–62 | `E(n) = o(loglog n)` → `E(n) = O((loglog n)^{2/3})`; Mertens error `o(1)` → `O(1/log n)`; the registry-problem sentence reworded from a parenthetical aside to a plain statement of relative strength |
| C4 | 76–85 (component (E)) | Levels `{n/p^{k−1}},…,{n/p^{k−J}}`; `(log n)^{1−ε}` → `K(n)`; "the carry-free proportion is at most that"; explicit note that the top level is unused and that Lemma `measure` is corroborative |
| C5 | 86–90 (component (A)) | Sum over `J(n) < k ≤ K(n)` with **two** flanking trivial ranges; explicit rate |
| C6 | 93–99 (§density opening) | Paragraph added: nothing from §equi to §assembly consumes this section; its one optional use is §B.6(b), which §B.6(d) bypasses |
| C7 | 105–147 (Lemma `measure`) | **Finalized and corrected.** Placeholder deleted. Normalization corrected from `log(b/a)/(k log n)` to `log((log n − log a)/(log n − log b))`; second (expanded) form given; error term made explicit as `O(exp(−c√(log n/(k+1))))`; the divergent `σ^c_k = (Σ_m log((2m+2)/(2m+1)))/log n^{1/(k+1)}` replaced by the convergent per-block quantity `σ^c_ν = log((ν+1)/(ν+½)) / log((ν+1)/ν)`, increasing from `log(4/3)/log 2 = 0.41504…` to `½`; proof supplied; Lean anchors moved out of the statement into following text |
| C8 | 152–162 (numerics) | Retitled "Empirical corroboration; not an input to any proof", labelled `rem:numerics`, opening sentence states that no statement depends on it |
| C9 | 168–174 (Prop `equi`) | Schedule moved to a display (rendering; clears 16.7 pt overfull). Statement unchanged |
| C10 | 190–197 (`eq:weyl`) | Sum range `p ∼ P` → `p ∈ (n^{1/(k+1)}, n^{1/k}]`; **exponent `k−i+1` → `k−i`**; parenthetical added naming the level set. *Applied* because three other sites (Prop `equi`, lines 209 and 470) already read `k−i` and the amended Prop `equi` says explicitly that the top level is excluded — and because `k−i` is correct under **both** resolutions of `[B1]`. The *target* `(log P)^{−A}` was left alone: see `[B2]` |
| C11 | 223–227 | "**no analytic result is cited**" → "**no oscillatory-sum estimate is imported**" (the unqualified claim contradicted the same paragraph's input list, which names PNT); stale "`J ≍ log k`" → "`J = J(k)` as scheduled in Proposition `equi`" |
| C12 | 259–262 | "Citations are provenance only" → PNT named as the one listed item not proved here, everything else provenance only |
| C13 | 419–426 (Vaughan proof) | Stale pointer "the three points at which the statement must be read as amended" corrected: (i) and (ii) are now incorporated in the statement; only (iii), the subinterval convention in the bilinear term, remains |
| C14 | 465–474 (§schedule) | Display split in two (rendering; clears 25.2 pt overfull). Content unchanged |
| C15 | 519 (§assembly) | Defensive parenthetical "(no ineffective input appears anywhere in the proof)" removed; "with effective constants throughout" retained |
| C16 | 524–570 (Provenance) | Rewritten: **Inputs** (i)–(iv), with (iii) naming PNT-with-classical-error, where it is consumed (band masses at `k > √log n`, and §B.6(b)), and that it is the one imported theorem; **Lean anchors** as a labelled list — `prime_not_dvd_centralBinom_iff_carryFree` (K); `levelOneCarryPrimes_filter_eq_sdiff`, `levelOneCarryMass_eq_band_sum`, `levelTwoJointCarry_fiber_logMass` (B); `primeHarmonicMass_railBand_le_uniform` (band-Mertens). Also clears two overfull boxes (106.4 pt, 76.7 pt) |

### Appendix — framing only, no mathematics touched
| # | Location | Change |
|---|---|---|
| A1 | 867 | "Six statements … require amendment" → "Ten" (there are ten flags) |
| A2 | 871–909 | **Remark `rem:bridge` added.** Three parts: (a) *level index* — the appendix's `i` and the main text's `i'` differ by one, `i = i' + 1`, so Prop `equi`'s level set is `i = 2,…,J(k)+1` here, exactly route §B.6(d); (b) *what that excludes* — every `i₀ = 1` case (table rows 2–3, `T₀`, §B.6(a)–(c)) is outside the main line and serves only §density's corroborative analysis, row 1 alone carries the theorem; (c) *flag status* — all ten of `[A1]`–`[A10]` discharged, with the site of each discharge named, and a pointer to the two that are not |
| A3 | 1657–1664 (§B.7) | Framing paragraph before the table: under the top-level exclusion only row 1 arises; rows 2–3 retained because the enumeration is exhaustive only with them and because §density needs them. **The table's mathematics is unchanged** |
| A4 | 1840–1885 (§B.9) | `[B1]` and `[B2]` written out in full, with the arithmetic, both resolutions for `[B1]`, and the substitution list for `[B2]` |
| A5 | 1204–1206 (§B.3) | Forward pointer to `[B2]` added after the sentence that derives `eq:weyl` |
| A6 | 1661–1671 | Table: `\small` → `\footnotesize`, `\tabcolsep` 6 pt → 2.5 pt, row 3 column 5 shortened to "§B.6(b), or void by (d)" (rendering; clears 89.1 pt then 18.4 pt overfull) |

### Typography only (no content change)
| # | Location | Change |
|---|---|---|
| T1 | 630 (Lemma `tau2`) | Leading `\;` removed so a line break is permitted (12.6 pt) |
| T2 | 1462–1470 (Remark `typeIIreach`) | Two conditions moved to a display (43.6 pt) |
| T3 | 1794–1812 (§B.9) | ETK first term and the `h`-weight sum moved to displays (36.1 pt, 102.2 pt) |

**Frozen regions confirmed untouched:** Lemma `typeIB`'s `r = 2` saving display
(lines 1231–1236, 1281), Lemma `typeIIB`'s `G₀ = (Fj)^{4/5}` threshold
(lines 1423, 1434, 1450, 1684), Lemma `fourier1`'s constant. `RequestProject/Erdos377CarryRails.lean`
never opened.

---

## 3. Constants — checks requested

**Dominance hypothesis vs. the schedule.** `Lemma dominance` needs
`Q ≥ 8eH e^{r_max}`. Taking logs: `log(8eHe^{r_max}) = r_max + 2loglog n + O(1)
= 2loglog n + O((loglog n)^{1/3})`, while `eq:logQ` gives
`log Q ≥ ½(log n)^{ε_n} = ½exp((loglog n)^{2/3})`. With `u = loglog n` the
requirement is `½e^{u^{2/3}} ≥ 2u + O(u^{1/3})`, i.e. `u^{2/3} ≳ log(4u)` —
true for `u ≳ 8`, i.e. `n ≳ exp(exp(8))`. **Satisfied**, and it remains
satisfied under `[B1]`'s `r_max = 3J+5` since that changes only the
`O((loglog n)^{1/3})` term. The verification is already in the document, in
the paragraph following Lemma `dominance` (line ~1042). The Type II variant
needs the same with an extra factor `K`; `log K ≤ loglog n`, so it too holds.

**`F ≤ HQ^J`, everywhere it appears.** Six sites — main text 209, 241, 381, 470;
appendix `eq:Frange` 965, table row 1 at 1667, and 1696. **All are wrong by one
power of `Q` under the amended level set**; see `[B1]`. Left in place, reported.

**`A` vs. `T₀`.** `T₀ = e^{80} ϱ^{10} (log Q)^{10A+40} ≤ (log n)^{10A+50}` and
`Q ≥ exp(½(log n)^{ε_n})`, so `Q ≥ T₀` for every fixed `A`, with the ratio
doubly exponential. The main line therefore has `F ≥ Q ≥ T₀` and never enters
the residual regime. **Consistent.** If `[B2]` is resolved as proposed, `T₀`
becomes `e^{80}ϱ^{10}(log n)^{10B+40}` and the same check goes through unchanged.

**First-sum accounting.** §assembly (lines 501–515) carries
`≪ 2^{−J(n)} log K + logloglog n = e^{−c(loglog n)^{1/3}} loglog n + O(logloglog n)`,
with the `logloglog n` attributed to the bands `k ≤ J(n)`. The tail is
`C log(log₂n / K) = C ε_n loglog n + O(1) = C(loglog n)^{2/3} + O(1)`, which
dominates. Propagated to component (A) (C5) and to the abstract and Theorem 1
(C1, C2). Note the two accountings of the small-`k` bands — `[M5]` above.

**Numerical check of the corrected Lemma `measure`.** Band `k = 3`,
`n = 10^{12}`, exact prime sums:

```
band mass:  actual 0.284980   corrected log((k+1)/k) 0.287682   as printed 0.083333
t in (1,2]: actual 0.025270   predicted 0.025406   ratio 0.9947
t in (2,3]: actual 0.015208   predicted 0.015166   ratio 1.0028
t in (1,10]:actual 0.086791   predicted 0.087011   ratio 0.9975
t in (5,50]:actual 0.091161   predicted 0.092650   ratio 0.9839
sigma^c_1 = 0.41504,  sigma^c_2 = 0.44966,  sigma^c_10 = 0.48809,  sigma^c_100 = 0.49876
```

The corrected form agrees to within the finite-`n` Mertens error; the printed
form was low by a factor 3.4 ≈ `k`. The `σ^c_ν` values confirm the lemma's own
prose ("biased below ½ at small quotients, tending to ½ from below at large
ones") and match Appendix B's `σ₁ = log(3/2)/log2 = 0.5850…` for the
complementary carry-free fraction.

---

## 4. Compile

```
pdflatex ×2
28 pages, 535 kB
0 errors
0 undefined references
0 multiply-defined labels
0 underfull vboxes
7 overfull hboxes, maximum 9.87 pt  (was 12, maximum 106.4 pt)
```

---

## 5. Remaining risks, ranked

1. **`[B1]` is undecided and the document is self-inconsistent until it is.**
   Highest priority, lowest effort. Either raise `r_max` to `3J+5` and
   `F ≤ HQ^{J+1}` at six sites, or drop one level. Both are inert downstream;
   what is not acceptable is shipping with `HQ^J` and `r_max = 3J+3` attached to
   a level set that violates both.

2. **`[B2]`: the stated intermediate target does not close the chain.** The
   proof does; the display does not. An auditor reading only §equi → §schedule →
   Prop equi will find a gap that is not there. The substitution `log P → log n`
   is mechanical and I have listed the four sites.

3. **The `k` in Lemma `measure` was wrong for the entire life of the draft**
   (factor `k`, corrected in C7, confirmed numerically). It never propagated —
   §B.6 uses only the *ratio* `eq:hyperbola`, in which `k` cancels — but it is
   worth asking what else in §density carries the same normalization slip. The
   two Lean anchors `levelOneCarryMass_eq_band_sum` and
   `levelTwoJointCarry_fiber_logMass` state the *finite band* form; if either
   encodes the density with a `1/(k log n)` normalization, it disagrees with the
   corrected lemma and should be checked. **I did not open the Lean file, so this
   is unverified.**

4. **PNT-with-classical-error is now named as an input but is not proved, not
   machine-verified, and is the only such item.** The provenance section says so
   plainly. Anyone claiming the paper is "self-contained" should be pointed at
   input (iii). Note that it is needed for *every* band with `k > √log n` —
   not only for the residual regime — so it cannot be removed by taking route
   §B.6(d).

5. **`[M4]`: Lemma `typeI`'s statement is narrower than its use.** The bridge
   (Lemma `dominance`) is cited at the point of use, so this is a presentation
   risk rather than a gap — but it is the kind of thing a referee stops on.

6. **`[M3]`: `eq:Jk` reads `min{J,k}` against the main text's `min(J,k−1)`.**
   Resolved for the reader by Remark `rem:bridge`, but the two displays still
   differ; if `[B1]` is resolved the recommended way, align them.

7. **Flag status is now asserted in Remark `rem:bridge` but not independently
   re-verified.** I checked each of `[A1]`–`[A10]` against the amended text
   while writing that remark, but a second pass over the ten claims is cheap
   insurance — in particular `[A3]` (that the amended Lemma `vdcr` really is the
   sharp form, first term `Nλ^{1/(2^r−2)}` with no `N^{r−2}`: it is, line 348)
   and `[A6]` (that the amended Lemma `typeII` carries `(Fj)^{−1/10}` and
   `M^{−2^{−r_max−2}}`, not `L^{−η'/2}`: it does, line 439).

8. **Seven overfull boxes remain, all ≤ 9.87 pt.** Within the stated tolerance;
   listed here only so their existence is not a surprise.
