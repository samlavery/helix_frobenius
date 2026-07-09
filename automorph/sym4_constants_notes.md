# Sym⁴ critical-value constants — literature notes

Compiled 2026-07-02. RETRIEVAL ONLY. Primary source for nearly everything below
is the full text of Ibukiyama–Katsurada, *J. Math. Soc. Japan* **66** (2014),
139–160 ("Exact critical values of the symmetric fourth L function and vector
valued Siegel modular forms"), extracted directly from the published PDF
(J-STAGE, DOI 10.2969/jmsj/06610139) via `pdftotext`, not a search-engine
summary — page/line references below are to that extracted text and match the
printed page numbers (139–160) in the paper itself. This is a primary-source
read, cross-checked against the paper's own abstract as independently indexed
on Project Euclid/J-STAGE (matches verbatim). Zagier's original 1977 paper
(LNM 627) and his 1994 "Modular forms and differential operators" paper were
both fetched and searched directly in full text; the 1994 paper contains
**no** Sym⁴/Δ material (it is entirely about Rankin–Cohen brackets in the
abstract sense) — flagged so this dead end isn't retried. The 1977 LNM 627
PDF was fetched but is a poor-quality scan not amenable to reliable OCR/text
extraction in this pass; every fact below attributed to "Zagier 1977" is
sourced via **direct quotation inside IK 2014's own text** (which quotes
Zagier's conjecture and page-cites it as [25] = Zagier, *Modular Functions of
One Variable VI*, LNM 627, 1977, pp. 105–169), not from reading Zagier's
paper itself.

---

# EXPERIMENT-READY FACTS

## 1. Zagier's 1977 conjecture — exact statement (IK 2014, p. 140, "Conjecture 1.1")

Quoted verbatim from IK 2014 (their Conjecture 1.1, attributed to Zagier [25]):

```
((2π)^(−3s+33) Γ(11)^(−1) Γ(s)Γ(s−11) L(s, Δ, Sym(4)) = c(s) · 2^33 · (Δ,Δ)^3
```

for **s = 24, 26, 28, 30, 32**, where c(s) is given by the table:

| s  | c(s) |
|----|------|
| 24 | 2⁵ × 3² |
| 26 | 2⁵ × 3 × 5 |
| 28 | 2² × 23 × 691/7² |
| 30 | 2³ × 653 |
| 32 | 2 × 3 × 34981*/7 |

(*) IK 2014's own footnote: "He [Zagier] stated 34891 instead of the above
prime 34981, but this is an obvious typo since 34891 = 23 × 37 × 41" (i.e.
34891 factors, so is not prime, confirming 34981 — which IS prime — as the
intended value). This typo-correction is IK 2014's own editorial remark, not
mine.

**Normalization spelled out exactly as IK 2014 state it (p. 140):**

- **⟨Δ,Δ⟩ convention**: defined by IK 2014 immediately above the conjecture as
  ```
  (Δ,Δ) = ∫_{SL2(Z)\H} |Δ(τ)|² y^10 dx dy
  ```
  i.e. the **unnormalized** Petersson inner product over the standard
  fundamental domain of SL(2,ℤ)\ℍ, with measure `y^10 dx dy` — note the
  exponent is `y^(k-2) = y^10` for weight k=12 (the standard convention
  `|f|² y^k · dxdy/y²  = |f|² y^(k-2) dx dy`), **not** divided by the
  hyperbolic volume of the fundamental domain and **not** including any
  extra normalizing constant (no `1/vol` factor, no extra 4π's). This is
  IK 2014's own explicit definition, given as a displayed equation, so it is
  unambiguous for this paper.
- **Sym⁴ L-function convention**: defined by IK 2014 in §2.2 (p. 143) via
  Satake parameters: for f = Σa(n)qⁿ ∈ S_k(Γ₁) normalized so
  `1 − a(p)x + p^(k−1)x² = (1−α_p x)(1−β_p x)` (this is the **motivic/Deligne**
  normalization — α_p, β_p have absolute value p^((k-1)/2), NOT the unitary
  |α_p|=1 convention), they define
  ```
  L(s, f, Sym(j)) = ∏_p ∏_{i=0}^{j} (1 − α_p^i β_p^(j-i) p^(−s))^(−1)
  ```
  This is the **motivic-normalized** Dirichlet series (finite part only, no
  Gamma factors folded in) — functional equation s ↔ (k−1)j + 1 − s (their
  own statement, p. 143, citing Barnet-Lamb–Geraghty–Harris–Taylor for
  meromorphic continuation/functional equation in general j).
- **Critical points s = 24,...,32 are in this motivic normalization** (NOT
  shifted to be centered at 1/2). For Δ, k=12, j=4: functional equation
  center is at s = (k−1)j+1)/2 = (11·4+1)/2 = 22.5, so s=24,26,28,30,32 sit
  just to the right of center — these are exactly the critical integers in
  the sense of Theorem 3.2 below (2k ≤ s ≤ 3k−4, i.e. 24 ≤ s ≤ 32 for k=12).

## 2. Ibukiyama–Katsurada 2014 exact scope — THE LOAD-BEARING FACT

**This is answered directly and unambiguously by IK 2014's own text — read
carefully, because the paper's abstract is easy to over-read as proving more
than it does.**

### (a) What is PROVEN with the exact rational constant, for Δ specifically

IK 2014's **Theorem 2.2** (p. 154) proves, for r = 2,4,6,8,10 (i.e.
s = r+22 = 24,26,28,30,32):

```
(2π)^(−3r−33) Γ(11)^(−1) Γ(r+11)Γ(r+22) L(r+22, Δ, Sym(4))
  = (2π)^(−3r−33) Γ(11)^(−1) Γ(r+11)Γ(r+22) L(r, F₁₃,₁₀ₐ, St)
  = 2^18 · 3^(−6) · 5^(−5) · 13^(−1) × c(r+22) (F₁₃,₁₀ₐ, F₁₃,₁₀ₐ)
```

where F₁₃,₁₀ₐ is an explicitly constructed vector-valued Siegel cusp form of
degree 2, weight det¹³Sym¹⁰ (constructed from theta series on the E₈ lattice,
§2.2), (F,F) is its own explicitly defined Petersson-type inner product (given
as a displayed integral, p. 152), and c(·) is exactly Zagier's table above.
**This is an unconditional, fully proven identity** — no GRH/RH-type
hypothesis anywhere in the chain (built from the Ramakrishnan–Shahidi lift,
theta lifts, pullback formulas, and differential operators — all
unconditional constructions).

**Corollary 1.3** (p. 140, restating Theorem 2.2 via the lift
`L(s,Δ,Sym(4)) = L(s−22, F₁₃,₁₀ₐ, St)`, itself from Ramakrishnan–Shahidi
2007):
```
(2π)^(33−3s) Γ(11)^(−1) Γ(s)Γ(s−11) L(s, Δ, Sym(4)) = c(s) (F,F)
```
for s = 24,26,28,30,32 — "five critical values of the left hand side are
exactly as conjectured by Zagier **up to a common non-zero constant**."

### (b) What is explicitly NOT proven — in IK 2014's own words (p. 140, §1, and p. 147, Conjecture 2.3)

> "Since we do not know the relation between (Δ,Δ)³ and (F,F), **we cannot
> say that we proved Zagier's conjecture completely**, but his conjecture is
> now interpreted into a conjecture on a relation between (Δ,Δ)³ and (F,F)"
> — this is **Conjecture 2.3**: `(F₁₃,₁₀ₐ, F₁₃,₁₀ₐ) = 2^15 × 3^6 × 5^5 × 13 ×
> (Δ,Δ)³`.

**So even for Δ itself, Zagier's exact conjecture (with (Δ,Δ)³ appearing
literally, not via an unrelated auxiliary form's inner product) remains
OPEN as of this 2014 paper** — what is proven is that the *ratios* of the
five critical values match Zagier's table exactly (i.e., the c(s) column is
verified as internally consistent / correctly computed), and that each value
equals `c(s) × (F,F)` for the *same* (F,F) across all five s — but whether
that common (F,F) equals `2^15·3^6·5^5·13·(Δ,Δ)³` is Conjecture 2.3, unproven.
I did not find, in this paper or elsewhere in this search pass, a later paper
that resolves Conjecture 2.3. **NOT FOUND**: any subsequent proof of
Conjecture 2.3 (the (F,F)/(Δ,Δ)³ relation).

### (c) General elliptic modular forms — Theorem 3.2 (p. 147)

> "For any primitive form f ∈ S_k(Γ₁), there exists a constant c(f) depending
> only on f such that **L(l, f, Sym(4))/π^(−3k+3l+3) c(f) belongs to Q(f)**
> for any even integer l such that 2k ≤ l ≤ 3k−4."

This is **algebraicity only** — it proves the critical value, divided by the
right power of π and by *some* unspecified constant c(f) (which the proof
does not compute — it comes from an existence theorem, Ramakrishnan–Shahidi
2007, that is non-constructive for general f), lands in the Hecke eigenvalue
field Q(f). **It does NOT give the exact rational number** at each critical
point, and does NOT identify c(f) with `⟨f,f⟩³` or pin down its normalization
— that identification is posed only as **Conjecture 3.3** (p. 147):

> "For a primitive form f ∈ S_k(Γ₁), there should exist a Hecke eigenform
> G ∈ S_{k+1,k-2}(Γ₂)(Q(f)) such that L(s,G,Sp) = L(s,f,Sym(3)) and that
> (G,G)/(f,f)³ ∈ Q(f)."

This conjecture is explicitly NOT proved in this paper for general f (stated
as a conjecture, immediately after the proof of Theorem 3.2).

### (d) Direct answer to "is weight 16 proven or open"

**Weight 16 (f₁₆ = ΔE₄, the unique normalized weight-16 level-1 cusp form) is
NOT covered by any theorem in IK 2014 that gives an exact rational×π-power×
⟨f₁₆,f₁₆⟩³ constant.** The only applicable result is Theorem 3.2
(algebraicity up to an unspecified, non-explicit constant c(f₁₆) ∈
ℂ — not even proven rational, let alone computed), for critical integers l
with 2·16 = 32 ≤ l ≤ 3·16−4 = 44. Even the *algebraicity* statement (Theorem
3.2) does not identify c(f) with a Petersson-norm power; that identification
(Conjecture 3.3) is open in general. **This is the load-bearing fact for the
experiment**: the exact-constant Sym⁴ landing is proven *only* for Δ's
five critical points 24–32 (and even there, only as `c(s)·(F,F)`, with the
further identification of `(F,F)` with `⟨Δ,Δ⟩³` — Conjecture 2.3 — still
open), and weight 16 has **no exact conjectural or proven constant published
anywhere located in this search** (see item 3 below).

### (e) Related/independent proof routes found (not fetched in full; flagged as unreconciled)

- Chen (arXiv, via Springer *Annales mathématiques du Québec*, DOI
  10.1007/s40316-020-00134-6), "On the standard L-function for GSp₂ₙ×GL₁ and
  algebraicity of symmetric fourth L-values for GL₂" — an independent proof
  route (Rankin–Selberg integrals for GSp₂ₙ×GL₁ rather than Siegel
  pullback/KRS-lift). Abstract fetch only returned bibliographic metadata;
  **NOT FOUND**: whether this paper's algebraicity result is stronger (e.g.
  gives exact constants, or covers weight 16) — not verified in this pass,
  would need a full-text fetch to resolve.
- Pitale–Saha–Schmidt (per a secondary citation surfaced in search) are
  reported to have made "the first advances in the case m=4 for general
  newforms f" beyond IK 2014 — **NOT FOUND**: exact paper title/venue/exact
  scope; only a paraphrased citation snippet was located, not the primary
  text. Flagged, not used as a fact below.

## 3. Weight-16 constants — NOT FOUND

**No published exact (conjectural or proven) critical-value table for
L(Sym⁴f₁₆, s), f₁₆ = ΔE₄, was located in this search pass.** Specifically:

- Zagier's 1977 paper (per IK 2014's own description of its content, p. 139:
  "In 1977, D. Zagier gave the critical values of L(s,Δ,Sym(j)) for j=1,2 and
  proposed a conjecture on exact critical values for j=3,4") is described,
  even by IK 2014 (who read the original), as being **specifically about Δ**
  — there is no indication in IK 2014's own summary of Zagier's paper that
  Zagier's 1977 conjecture was stated as a general formula over all weights k;
  it reads as a Δ-specific numerical conjecture (a specific table for one
  form). **NOT FOUND**: any general-k closed-form version of Zagier's Sym⁴
  conjecture (i.e., I cannot confirm or deny that Zagier's paper contains a
  general-weight formula from the sources reached in this pass — IK 2014
  never states one, and the original 1977 PDF could not be reliably read).
- **NOT FOUND**: any exact expression for ⟨f₁₆,f₁₆⟩ (the Petersson norm of
  the weight-16 level-1 cusp form) as rational·π^a·(product of L-values or
  Bernoulli-number form). Search results confirm Zagier used Rankin's method
  to compute Petersson norms for level-1 cusp forms generally (a 1977-page
  citation, "[Zag77, page 116]," was referenced in a secondary source as
  giving a numerically-verified ⟨Δ,Δ⟩ value to 11 digits via "direct
  summation of 250 first terms in L-series" — but this is ⟨Δ,Δ⟩, weight 12,
  not weight 16, and even for weight 12 no closed-form rational·π^a expression
  was extracted, only a numerical anecdote about verification). **NOT
  FOUND**: a closed-form ⟨f₁₆,f₁₆⟩ formula from any source reached in this
  pass.
- General Rankin/Petersson-norm recipe (found, but generic, not a specific
  number): for f_k = E_{k−12}·Δ type constructions (k ∈ {12,16,18,20,22,26},
  the six level-1 weights with dim S_k = 1), Rankin's unfolding method
  expresses ⟨f,f⟩ via `(4π)^(1−k)(k−2)!/ζ(?) × [Dirichlet series manipulation
  of Eisenstein-series Fourier coefficients]` (paraphrased from a search
  snippet, not a verbatim equation — **flagged as reconstructed shape, not a
  literature quote**, since the exact equation/reference could not be pinned
  to a specific numbered display in this pass). If the experiment needs
  ⟨f₁₆,f₁₆⟩ exactly, it should be computed fresh (e.g. via Rankin's method
  numerically, or via LMFDB, which tabulates Petersson norms for low-weight
  level-1 forms) rather than taken from a literature table — none was found.
- **LMFDB note (not independently verified by fetch in this pass, but worth
  flagging as the likely fastest path to a numerical anchor)**: LMFDB
  (l-functions and modular forms database) is known to list Petersson-norm
  and L-value data for low level-1 weights including weight 16; this was NOT
  checked/fetched in this retrieval pass (out of scope: "retrieval only,"
  and LMFDB values would count as a fresh numerical computation, not a
  citable literature constant) — flagged as a pointer for the experiment
  team, not a sourced fact.

## 4. Critical set and Γ-factors, general weight k — PARTIALLY FOUND

- **Critical integers (proven range, from Theorem 3.2 above, general k):**
  even integers l with **2k ≤ l ≤ 3k−4** (motivic/finite-L-function
  normalization, same convention as item 1). For k=12 (Δ): 24 ≤ l ≤ 32, i.e.
  l ∈ {24,26,28,30,32} — matches Zagier's five points exactly. For k=16
  (f₁₆): **32 ≤ l ≤ 44**, i.e. l ∈ {32,34,36,38,40,42,44} — **seven** even
  critical integers (this range is a direct arithmetic reading of IK 2014's
  own Theorem 3.2 inequality specialized to k=16; the inequality itself is
  literature-sourced verbatim, the k=16 arithmetic is elementary
  substitution, not an independent claim).
- **Γ-factor / motivic weight for general k**: IK 2014 does not give an
  explicit Γ_∞(s) factorization formula for general Sym⁴ in this paper (their
  focus is the finite Dirichlet series `L(s,f,Sym(j))` and its critical
  *values*, not the completed L-function's Gamma-factor bookkeeping). **NOT
  FOUND in IK 2014**: an explicit `Γ_R(s−?)Γ_C(...)Γ_C(...)` shape for
  general k. The Sym⁴ motive has motivic weight 4(k−1) and Hodge types
  {0, k−1, 2(k−1), 3(k−1), 4(k−1)} (standard Sym⁴ Hodge-theoretic fact,
  general knowledge, not from a specific citation in this pass — flagged as
  NOT independently re-verified against a primary source in this retrieval,
  since the prior research pass already flagged this exact point as a gap
  and I did not find a source resolving it either).
- For k=16: motivic weight 4×15=60, Hodge types {0,15,30,45,60} (elementary
  substitution into the general pattern above; not itself a literature quote
  for k=16 specifically).

## 5. NORMALIZATION TRAPS

1. **Motivic vs. analytic s.** IK 2014's `s` (Conjecture 1.1, Theorem 2.2,
   Theorem 3.2) is the **motivic/finite-Dirichlet-series** normalization:
   Satake parameters α_p,β_p have |α_p|=|β_p|=p^((k−1)/2) (NOT unitary), and
   critical integers sit at s=24..32 for Δ (functional equation center at
   22.5), NOT at s=1/2 or s=0. **If the experiment's certified numerics use
   the unitary normalization** `λ_n = a_n/n^((k−1)/2)` as stated in the task
   context, i.e. `L^unit(u) = Σ (Sym⁴λ)_n n^(−u)`, **the shift to IK 2014's
   convention is**: unitary Satake parameters are α_p/p^((k-1)/2),
   β_p/p^((k-1)/2) (absolute value 1), so
   `L^unit(u) = L_motivic(s)` under the substitution `u = s − 2(k−1)`
   (since Sym⁴'s Euler factor has terms α_p^iβ_p^(4−i)p^(−s), and unitarizing
   divides each such term by p^(4(k−1)/2) = p^(2(k−1)), matching p^(−u)
   exactly when u = s−2(k−1)). This matches the shift the task description
   itself already anticipates ("u = s_motivic − 2(k−1)") — **confirmed
   consistent** with IK 2014's explicit Satake-parameter definition (§2.2,
   p.143), though IK 2014 itself never states this shift explicitly (it is a
   direct consequence of their definition, checked by hand here, not quoted).
2. **⟨Δ,Δ⟩ measure convention is NOT universal across the literature** — IK
   2014 use `∫|Δ|²y^10 dxdy` (no extra normalization). Other papers (e.g. the
   general Deligne-period literature, Shimura 1977 "On the periods of modular
   forms," cited by IK 2014 as [19] but not independently re-fetched here) may
   use `∫|f|²y^k dxdy/y²` (equal to IK's convention, since y^k/y² = y^(k−2) =
   y^10 for k=12 — **these are the same thing written two ways**, not a
   trap, but flagged since the task's context mentions "y^k dxdy/y²" as one
   convention to check: **confirmed identical** to IK 2014's `y^10 dxdy` for
   k=12) — vs. yet other authors who divide additionally by the hyperbolic
   volume `vol(SL2(Z)\H) = π/3` or by `4π` or other constants absorbed for
   "nicer" formulas. **IK 2014's own (Δ,Δ) has NO such extra division** — it
   is the bare unnormalized integral. Any comparison to another paper's
   ⟨Δ,Δ⟩ (e.g. Zagier's original 1977 value, or a numerical value from
   another source) must first confirm that paper uses the same bare
   convention, or a conversion factor must be tracked. **This was flagged in
   the prior research pass too and remains unresolved for any source other
   than IK 2014 itself** — I could not independently verify Zagier 1977's own
   ⟨Δ,Δ⟩ convention from the (unreadable) original PDF, and no secondary
   source quoted Zagier's own displayed definition verbatim.
3. **(F,F) is NOT ⟨Δ,Δ⟩³ up to a known constant — it is a conjectural
   relation (Conjecture 2.3), not a normalization fact.** Do not treat
   IK 2014's Theorem 2.2 as giving `L(s,Δ,Sym4)` directly in terms of
   `⟨Δ,Δ⟩³` with a known rational constant — it gives it in terms of `(F,F)`,
   a Siegel-modular-form Petersson norm, and the bridge to `⟨Δ,Δ⟩³` is
   exactly the open conjecture. **If the experiment computes `⟨Δ,Δ⟩` directly
   (e.g. via Rankin's method or a certified numerical Petersson-norm
   routine) and compares against IK 2014's formula, it is testing Conjecture
   2.3 itself**, not verifying an already-proven identity — this should be
   stated explicitly in any resulting writeup (the experiment would be
   probing something IK 2014 left open, which is a legitimate and
   interesting thing to do, but must not be mis-described as "checking a
   proven landing").
4. **c(f) in Theorem 3.2 is not normalized/computable from the paper.** For
   any non-Δ form (including f₁₆), there is no way to extract a numerical
   prediction from IK 2014 — the existence of c(f) is proven but c(f) itself
   is not computed or characterized beyond "depends only on f." Do not
   attempt to back out a "predicted" weight-16 constant from Theorem 3.2 as
   if it were computable from the proof; it is a pure existence statement.
5. **Sym⁴ vs Sym² period conventions do not directly compose.** The prior
   research pass's notes on Sym²/Ad⁰ period bookkeeping (c⁺(f)c⁻(f) vs
   ⟨f,f⟩) are for the **rank-3** adjoint/Sym² motive; IK 2014's Sym⁴
   (**rank-5**) uses a genuinely different period structure (⟨Δ,Δ⟩³, cubed,
   not c⁺c⁻ to the first power) — the two should not be conflated or
   mixed in the same formula without re-deriving the exponent from scratch
   for the rank-5 case specifically (IK 2014's own displayed formula already
   gives the correct exponent — cube — for Sym⁴, so use that directly rather
   than generalizing from the Sym² literature).

---

## Summary table: proven vs. open, for the experiment's two test cases

| Case | Exact critical values proven? | Source |
|---|---|---|
| Sym⁴Δ (k=12), s ∈ {24,26,28,30,32}, expressed as `c(s)·(F,F)` for an explicit auxiliary Siegel form F | **PROVEN** (Theorem 2.2 / Corollary 1.3) | IK 2014, unconditional |
| Sym⁴Δ, same critical values expressed as `c(s)·⟨Δ,Δ⟩³` with Zagier's original rational constants (i.e. Zagier's conjecture in its original, literal form) | **OPEN** (Conjecture 2.3 bridges (F,F) to ⟨Δ,Δ⟩³; not proven) | IK 2014, p.140/147 |
| Sym⁴Δ algebraicity only (no exact constant) | PROVEN (subsumed by the above, and more generally by Theorem 3.2) | IK 2014 |
| Sym⁴ f₁₆ (k=16), algebraicity up to an unspecified constant c(f₁₆) | **PROVEN** (Theorem 3.2, general f, no explicit constant) | IK 2014 |
| Sym⁴ f₁₆, exact rational·π-power·⟨f₁₆,f₁₆⟩³ constant | **OPEN / NOT EVEN CONJECTURED IN PUBLISHED FORM FOUND** (Conjecture 3.3 gives only an existence-type conjecture, no numbers; no weight-16-specific table located anywhere) | IK 2014 Conjecture 3.3; NOT FOUND elsewhere |

**Bottom line for the experiment design:** weight 16 is a genuinely open
target with **zero published numerical constants to test against** — any
landing test at weight 16 is necessarily a from-scratch numerical experiment
with no literature anchor, which should be stated as such. For Δ, even the
"proven" case (Theorem 2.2) does not directly hand over `⟨Δ,Δ⟩³`-normalized
constants — testing the literal Zagier form (`c(s)·⟨Δ,Δ⟩³`) against certified
Δ numerics is equivalent to numerically testing the still-open Conjecture
2.3, which is a legitimate and well-posed target (not GRH-flavored, not
circular — a live, nameable, finite Diophantine-style conjecture), but must
be described as testing an open conjecture, not confirming a proven theorem.
