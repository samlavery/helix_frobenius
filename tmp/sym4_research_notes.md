# Sym⁴Δ / Hida congruence-module literature research notes

Compiled 2026-07-02. All claims sourced with paper/author/year and where found
(search-engine synthesis vs. direct fetch — direct PDF fetches of most primary
sources failed due to compression; those cases are flagged and the claim rests
on search-engine-surfaced abstracts/summaries from ≥2 independent hits where
possible). Where sources disagree on normalization, both are recorded.

---

## Q1. Hida's congruence-module formula (1981/1988), specialized to Δ (level 1, weight 12)

**Primary sources:**
- Hida, H. "Congruence of cusp forms and special values of their zeta
  functions," *Invent. Math.* **63** (1981), 225–261.
- Hida, H. "On congruence divisors of cusp forms as factors of the special
  values of their zeta functions," *Invent. Math.* **64** (1981), 221–262.
- Hida, H. "A p-adic measure attached to the zeta functions associated with
  two elliptic modular forms II," 1988 (companion/extension work).
- Hida, H. "Arithmetic of adjoint L-values" (lecture notes, Pune),
  https://www.math.ucla.edu/~hida/Lec14PuneF.pdf — fetched but PDF was
  compressed/unreadable by the fetch tool; content below is from search-engine
  summaries that quote/paraphrase this and the original Compositio/Inventiones
  papers, cross-checked against Ghate's Compositio 2002 paper and Calegari's
  AWS lecture notes (both found independently).

**Statement (as reconstructed from ≥2 independent search summaries):**

For a normalized Hecke eigenform f (holomorphic, level N, weight k), let
L(s, f, Ad⁰) (equivalently written L(s, Ad(f))) be the adjoint L-function.
After dividing by a suitable transcendental period Ω(f) (a normalization
constant built from the Petersson norm ⟨f,f⟩ and powers of π — see Q3 for the
precise Sym²/Ad⁰ period bookkeeping), one gets an algebraic number

  L^alg(1, f, Ad⁰) = L(1, f, Ad⁰) / Ω(f)  ∈  \overline{ℚ}.

**Hida's theorem (1981a, 1981b):** the primes ℓ dividing L^alg(1, f, Ad⁰)
(outside a small explicit exceptional set) are exactly the *congruence
primes* of f — i.e., primes ℓ such that f is congruent mod (a prime above) ℓ
to another Hecke eigenform g of the same weight and level (Fourier
coefficients a_p(f) ≡ a_p(g) mod ℓ for almost all p).

- Converse direction (ℓ congruence prime ⟹ ℓ | L^alg(1,f,Ad⁰)): proved by
  Hida in the ordinary case, and by **Ribet** in the non-ordinary case.
  [Found in: search summary citing Ghate's Compositio paper's discussion of
  Hida's theorem; corroborated independently by the Calegari AWS lecture
  notes summary and the Pune lecture-notes summary.]

- **Precise mechanism / "congruence module":** the congruence module C_f of
  f is (by definition) the quotient measuring how far the Hecke algebra
  localized at f fails to split off f's eigenspace as a direct summand — its
  order is the standard invariant "size of congruences." Hida's theorem,
  reinterpreted through Wiles'/Taylor–Wiles deformation theory, becomes an
  **"adjoint class number formula":**

    #C_f  ~  L^alg(1, f, Ad⁰)   (equal up to explicit local factors / units
                                  at bad primes and at ℓ | N k!),

  i.e. the L-value gives the exact size of the congruence module, matching
  the size of a corresponding Selmer group (this is the Bloch–Kato/Tamagawa
  framing later made unconditional by Diamond–Flach–Guo, see Q2).
  [Found in: search summary directly quoting/paraphrasing Hida's own
  exposition — "this identity relating L-value with the size of the
  corresponding Selmer group... is called the adjoint non-abelian class
  number formula" — surfaced twice across two independent searches (query 1
  and the Ghate/"c(f)" query), treated as same-source repetition, so this is
  **single-source-confirmed only** (Hida's own lecture notes); I could not
  independently corroborate the precise equality (vs. proportionality up to
  a stated finite fudge factor) from a second, distinct author. Flagged as
  NOT independently cross-checked — see EXPERIMENT-READY FACTS caveats.]

**Specialization to Δ (level 1, weight 12):**

- Δ's companion Eisenstein series is E₁₂ (unique level-1 weight-12 Eisenstein
  series). Ramanujan's classical congruence
    τ(n) ≡ σ₁₁(n)  (mod 691)     for all n ≥ 1
  is exactly the statement Δ ≡ E₁₂ (mod 691) as q-expansions.
  [Found in: two independent search summaries, one via Calegari's AWS notes
  ("Ramanujan's congruence primes," arXiv:2403.03345) and one via a general
  search on "691 Ramanujan congruence"; both state the Δ ≡ E₁₂ (mod 691)
  reformulation identically.]

- **Why 691 specifically:** 691 is the numerator of the Bernoulli number
  B₁₂ (equivalently, 691 | numerator of ζ(12)/π¹² in lowest terms — ζ(12) =
  691π¹²/638512875). 691 is the smallest irregular prime in Kummer's sense.
  Because the constant term of E₁₂'s Eisenstein series normalization
  involves ζ(1−12) = -B₁₂/12, and 691 divides B₁₂'s numerator, E₁₂'s
  q-expansion coefficients collapse mod 691 to look like a cusp form's,
  forcing the congruence with Δ.
  [Found in: search summaries from two independent queries, consistent.]

- **This IS the "Eisenstein congruence" case, not an independent
  cusp-form–cusp-form congruence** (there is only one newform at level 1
  weight 12, so there is no other cusp form for Δ to be congruent to — the
  congruence is necessarily with the Eisenstein series E₁₂). Under Hida's
  general theory this is the boundary/degenerate case: the "congruence
  number" of Δ (in the sense of the paper's Rung A) is understood as the
  largest N such that Δ ≡ (some other form, here forced to be Eisenstein) mod
  N — classically identified as **691** (Δ has no other level-1 weight-12
  cuspidal companion, and 691 is the unique prime where this Eisenstein
  congruence occurs at this level/weight). I did NOT find a source stating a
  composite "congruence number" bigger than 691 (e.g. a prime power 691^a or
  a product with other primes) for Δ specifically — every source names 691
  alone as the congruence prime. **This should be verified computationally
  in the experiment itself** (i.e., don't take "691 exactly, to the first
  power" as literature-given without an independent check), since the
  literature snippets found describe the *prime* 691 as the congruence
  prime but do not explicitly rule out higher congruence modulo 691².

- **691's role precisely:** it is an **Eisenstein congruence prime** (Δ ≡
  Eisenstein series E₁₂), NOT a "cusp-form congruence" in the sense of two
  distinct cuspidal Hecke eigenforms being congruent (impossible at level 1
  weight 12 — dim S₁₂(SL₂(ℤ)) = 1). This is a special/degenerate instance of
  Hida's adjoint-L-value congruence-prime criterion: the adjoint L-value
  framework (which in general detects cusp-cusp congruences) also detects
  Eisenstein congruences via a companion theory (Hida's later extension to
  the Eisenstein ideal / the constant term of the p-adic adjoint L-function;
  this reduces to the classical statement that 691 | numerator(ζ(-11)) =
  -B₁₂/12 up to normalization). [Found independently via two queries; the
  "Eisenstein congruence, not cusp-cusp" framing itself is directly stated
  ("Δ ≡ E₁₂ (mod 691)") in the Calegari notes summary and is standard
  textbook material (also appears self-consistently in the "genus 2
  paramodular Eisenstein congruences" search hit), so treated as
  well-established.]

---

## Q2. Diamond–Flach–Guo (2004): precise statement

**Source:** Diamond, F., Flach, M., Guo, L. "The Tamagawa number conjecture
of adjoint motives of modular forms." *Ann. Sci. École Norm. Sup.* (4) **37**
(2004), no. 5, 663–727. DOI: 10.1016/j.ansens.2004.09.001. Also numdam:
https://www.numdam.org/item/ASENS_2004_4_37_5_663_0/ (metadata only
successfully fetched; full PDF fetch failed — compressed). Cross-checked
against an independent, apparently more recent restatement at
arXiv:2512.02348 ("Adjoint motives of modular forms and the Tamagawa number
conjecture") which gives what looks like an updated/expanded version with
explicitly numbered Theorem 0.1/0.2 — **two independent search hits
converged on essentially the same theorem wording**, so this is treated as
cross-checked.

**Setup:** f a newform of weight k ≥ 2, level N, with Hecke eigenvalues
generating a number field K. Let M = M_f be the (rank-2) motive attached to
f (Eichler–Shimura/Deligne), A = A_f = ad⁰(M) the (rank-3) adjoint motive
(trace-zero endomorphisms of M). λ a finite place of K (dividing a rational
prime ℓ).

**Main theorem (as stated, "Theorem 0.1" in the arXiv:2512.02348
restatement, matching the 2004 ENS abstract's wording):**

> If λ ∤ N·k! and the mod-λ Galois representation ρ̄_f, restricted to
> Gal(\overline{ℚ}/ℚ(√((-1)^{(ℓ-1)/2} ℓ))), is absolutely irreducible, then
> the λ-part of the Bloch–Kato/Tamagawa-number conjecture holds for **both**
> A_f **and its Tate twist A_f(1)** — i.e. at the two points s = 0 and s = 1
> of the adjoint motive (equivalently, L(A,0) and L(A,1) in the paper's own
> notation).

- So: **the two points are s = 0 and s = 1** (motivic normalization for the
  rank-3 adjoint motive A; A itself is s=0, its Tate twist A(1) is s=1 — NOT
  two points of a single L-function evaluated at two different arguments in
  the naive sense, but rather the conjecture applied to A and to A(1)
  separately, which are the two near-central points where Ad⁰ can be
  critical/non-critical in the sense of Bloch–Kato Selmer-group
  formulation).
- **Forms covered:** ALL newforms of weight k ≥ 2, level N — "without any
  restriction on weight or level," for λ outside the explicit finite
  exceptional set above. This generality (Taylor–Wiles-style patching, no
  weight/level restriction) is explicitly flagged in secondary-source
  commentary (a Maass-spaces-on-U(2,2) paper, found independently) as the
  headline strength of the result.
- **Extra consequence:** the method also proves modularity of all
  deformations of ρ̄_f that are crystalline of Hodge–Tate type (0, k−1) —
  i.e. an "R = T" statement for the adjoint deformation problem, in the
  spirit of Wiles/Taylor–Wiles/Fermat's Last Theorem machinery.
- **What "the proved decomposition asserts":** the Bloch–Kato conjecture
  decomposes L(A,0) (resp. L(A,1)) — after removing archimedean/period
  normalization — into a product of local Tamagawa-measure factors times the
  order of the Bloch–Kato Selmer group H¹_f, and DFG's theorem is precisely
  that this decomposition holds λ-adically (i.e. #Sha-type / Selmer terms
  match the ℓ-adic valuation of the L-value) for λ outside the stated
  exceptional set.

**Caveat on precision:** I was unable to get the *exact* internal equation
numbering (e.g. which numbered display in the 663-page-range paper states
the Tamagawa number formula in full, with all local Euler-factor/Tamagawa
measure terms spelled out) because both direct PDF fetches of the ENS paper
failed (compressed streams). The theorem statement above is reconstructed
from two independent search-engine syntheses that both quote the same
"Theorem 0.1" wording almost verbatim, which gives reasonable confidence in
the *statement*, but the reader should treat the internal proof
architecture / exact local-factor bookkeeping as **not verified against
primary text** in this pass.

---

## Q3. Sym² vs Ad⁰ normalization

**Sources:** (a) Gelbart–Jacquet (1978) original functorial-lift paper (not
independently re-fetched here, but its statement is standard and appears
consistently across ≥3 independent search hits: Kim–Shahidi's "Symmetric
cube L-functions for GL₂ are entire" Annals 1999 PDF (fetched via search,
confirms the general pattern one level up for Sym³ vs Ad-cube); a "Triality
and adjoint lifting for GL(3)" 2025 arXiv preprint; and a Hecke–Maaß-cusp-form
discussion snippet). (b) A symmetric-square-Fourier-coefficient-estimates
paper (Archiv der Mathematik) giving the explicit Euler factor formula.

**Exact relation:**

  Ad(π)  ≅  Sym²(π) ⊗ ω_π⁻¹

where ω_π is the central character of the GL(2) automorphic representation
π. Equivalently on L-functions:

  L(s, π, Ad)  =  L(s, Sym²π ⊗ ω_π⁻¹)  =  L(s, Sym²π)  when ω_π is trivial.

**When ω_π is trivial (level-1, e.g. Δ; more generally any classical
eigenform of trivial nebentypus):** the twist is trivial, so

  **L(s, Δ, Ad⁰) = L(s, Sym²Δ)  exactly, no shift, no extra factor** —
  the two L-functions coincide identically as Dirichlet series (same Euler
  product), for Δ. This is the level-1-weight-12 case relevant to the
  experiment.

**Euler factor check (independent formula, second source):** for
f = Σ a_n q^n with L(s,f) = ∏_p (1-α_p p^{-s})^{-1}(1-β_p p^{-s})^{-1}
(α_p β_p = p^{k-1}, "motivic" normalization) —

  L(s, Sym²f) = ∏_p (1 - α_p² p^{-s})^{-1} (1 - α_pβ_p p^{-s})^{-1} (1 - β_p² p^{-s})^{-1}

matches degree-3 Ad⁰ Euler factors term-for-term when ω_π trivial (α_pβ_p =
p^{k-1} plays the role of the "middle" Satake parameter, consistent with
Ad⁰ρ_f's Hodge-Tate weights {0, k-1, 2(k-1)} shifted to be trace-zero).
[Cross-checked: this Euler-factor form is given consistently in the Archiv
der Mathematik search summary and matches the general Ad⁰ρ_f Galois
description in the Gelbart-Jacquet summary — same shape, independent
sources, no numerical disagreement found.]

**Normalization-convention warning (found, and IMPORTANT for the
experiment):** the *automorphic/analytic* convention (unitary Satake
parameters of absolute value 1, functional equation s ↔ 1-s) differs from
the *motivic/Deligne* convention (Satake parameters of absolute value
p^{(k-1)/2}, functional equation centered so that critical points are
integers near s = 0 or s = k-1 depending on which "copy" of the L-function).
The general shift rule (found independently in two searches, both citing
the same general automorphic-to-motivic dictionary):

  L(s + (n-1)/2, M) = L(s, π)     [rank-n motive M ↔ automorphic π, generic form]

For the Ad⁰ (rank 3) case this becomes a shift by 1 (since n=3, (n-1)/2=1)
between the "motivic s" used in Deligne/Hida-style papers (where L(1,f,Ad⁰)
is the near-central/edge point of interest) and the "analytic s" convention
(centered at 1/2) used in analytic-number-theory papers on Sym². **The
experiment must fix ONE convention and state it explicitly**; the
literature is NOT uniform (this is flagged again in EXPERIMENT-READY FACTS
below as normalization trap #1).

---

## Q4. Sym⁴Δ: Hodge data, critical points, Deligne's conjectured period, proven/open boundary

### (a) Hodge data / Γ-factors, degree 5

**Source (general Sym^m construction):** search summary describing the
motive Sym^m(M(f)) for M(f) the rank-2 motive of a weight-k eigenform,
independently corroborated in shape by the Γ-factor formula found for
general Symʳ L-functions (Γ̃_r(s) = π^{-(r+1)s/2} · ∏_{j=1}^{r+1}
Γ((s+κ_{j,r})/2), giving r+1 = 5 Gamma factors for r=4 — i.e. **degree 5**,
consistent across two independent search hits).

- M(f)'s Hodge types: h^{0,k-1} = h^{k-1,0} = 1 (rank 2, motivic weight
  k−1). For Δ, k=12, so M(Δ) has motivic weight 11, Hodge types (0,11) and
  (11,0).
- **Sym⁴(M(Δ))** is a rank-5 motive of **motivic weight 4×11 = 44**, with
  Hodge types (reading off the symmetric-power combination pattern found in
  the general-Sym^m summary): **(0,44), (11,33), (22,22), (33,11), (44,0)**.
  This is a direct arithmetic consequence of the stated general pattern
  "(0, m(k-1)), (k-1, (m-1)(k-1)), ..." specialized to m=4, k=12 — I derived
  this specialization myself from the literature-given general pattern; it
  is NOT itself quoted verbatim from a source discussing Δ's Sym⁴ by name
  (no source was found giving the Δ-specific Hodge numbers explicitly), so
  this specific 5-tuple should be flagged as **derived, not directly
  literature-sourced**, though the underlying general formula is
  literature-sourced and the arithmetic is elementary.
- Local Hecke/Satake roots at good p: if α_p, β_p are f's Satake parameters
  (α_pβ_p = p^{11} for Δ), Sym⁴'s roots are α_p⁴, α_p³β_p, α_p²β_p²,
  α_pβ_p³, β_p⁴ — standard, uncontested.

### (b) Deligne-critical points

**Source:** a functoriality/special-values paper (arXiv 0707.1335-adjacent
search synthesis; direct PDF fetch failed but the search-engine summary
independently reproduced the **odd**-symmetric-power critical-integer lemma
with an explicit inequality, and separately flagged "a companion lemma for
even symmetric powers, including Sym⁴" without giving its exact bound in
the same breath — this half of Q4b is a **gap**, see below).

- **Odd case (found explicitly, r ≥ 0, Sym^{2r+1}, weight-k form φ):**
  critical integers m satisfy  **r(k-1) + 1 ≤ m ≤ (r+1)(k-1)**.
- **Even case (Sym^{2r}, which includes Sym⁴ at r=2):** the search results
  explicitly stated a companion lemma exists but I could NOT extract its
  precise inequality from the accessible summaries (the PDF fetch that would
  have contained it failed). **This is a genuine gap — flagged, not
  guessed.** By general Deligne-critical-point theory (an integer m is
  critical for L(s,M) iff neither Γ-factor at ∞ for M nor for its dual has a
  pole at s=m), and using the Hodge-type list derived in (a) above
  {0,11,22,33,44} for Sym⁴Δ (motivic weight w=44, so the dual's critical
  strip mirrors around w+1=45), the *standard* recipe for a self-dual
  even-weight motive with Hodge types h^{p,w-p} predicts critical integers
  at m ∈ {12, 23, 34} together with the "extra" edge points tied to the
  middle Hodge type (22,22) requiring separate sign-of-functional-equation
  bookkeeping (the (22,22) Hodge piece is the delicate one, since it does
  not force a pole in either Γ-factor by parity, and Deligne's own
  discussion of the symmetric-square case addresses exactly the analogous
  central-Hodge-piece subtlety). **I am flagging this reconstruction as
  MY OWN derivation from stated general principles, not a literature quote**
  — it should be cross-checked numerically/independently before the
  experiment relies on it as ground truth. The safest literature-anchored
  fact is Zagier's own claim (next item) that he *computed* Sym⁴Δ's critical
  values directly (n ≤ 4 case) — that computation, if the original 1970s
  Zagier source can be recovered in readable form, would settle the exact
  critical point list unambiguously; I could not extract it from the
  (garbled) Zagier PDF fetch attempted above.

### (c) Deligne's conjectured period at each critical point

**Source:** search synthesis explicitly giving the **general Deligne-type
conjectural shape** for Sym⁴ critical values (this exact formula shape
recurred, essentially verbatim, in the arxiv 0707.1335-derived summary and
independently in the "L(Sym^4 ... critical values ... pi^ table" search,
which cites the same general conjecture pattern as it appears
"Conjecture 3.1"/analogous numbering in Raghuram/Sturm-descended papers —
treated as cross-checked since two independent queries surfaced the same
formula unprompted):

> For a normalized weight-k Hecke eigenform φ and critical integer m for
> L_f(s, Sym⁴φ):
>
>   L_f(m, Sym⁴φ)  ~  (2πi)^{3m} · (c⁺(φ)c⁻(φ))³ · δ(ω)³     if m even
>   L_f(m, Sym⁴φ)  ~  (2πi)^{2m} · (c⁺(φ)c⁻(φ))³ · δ(ω)      if m odd
>
> (~ meaning "equal up to an explicit algebraic/rational number," the
> content of Deligne's conjecture), where c⁺(φ), c⁻(φ) are Deligne's own
> plus/minus periods for φ (with c⁺(φ)c⁻(φ) algebraically proportional to
> the Petersson norm ⟨φ,φ⟩, up to an explicit power of π — see Q3's
> Sturm/Zagier remark and the general c⁺c⁻~⟨f,f⟩ dictionary found
> independently), and δ(ω) is a sign/period correction depending on the
> parity ω of... [the exact dependency of δ(ω) was not further resolved in
> the accessible summaries — flagged as a secondary gap; likely tied to
> whether m is compared against the "plus" or "minus" eigenspace of complex
> conjugation composed with the sign of the functional equation, standard in
> this literature, but I did not verify its precise formula].
>
> **For Δ specifically:** since Δ has real Fourier coefficients and a
> 1-dimensional space of cusp forms, c⁺(Δ) and c⁻(Δ) are (up to a rational
> number) the classical Δ periods often written Ω⁺(Δ), Ω⁻(Δ), with
> Ω⁺(Δ)Ω⁻(Δ) ~ ⟨Δ,Δ⟩ (Petersson norm) up to an explicit rational multiple
> of a power of π (this power-of-π bookkeeping is exactly what Q3's
> Sturm/Zagier reference computes for Sym², and analogous conventions
> propagate to Sym⁴). **Zagier's 1977 conjecture is exactly this formula's
> specialization to φ = Δ**, phrased instead directly as "products of
> explicit rational numbers, powers of π, and the cube of ⟨Δ,Δ⟩" (matching
  the (c⁺c⁻)³ ~ ⟨Δ,Δ⟩³ shape above) — **cross-checked**: this
  ⟨Δ,Δ⟩³-power match between the general conjecture's (c⁺c⁻)³ term and the
  literature's plain-language description of Zagier's conjecture ("cube of
  the inner product of Δ") is an internal consistency check that is
  reassuring but was found across only the ONE Ibukiyama–Katsurada source
  (echoed in two separate search results, but both clearly describing the
  same paper/abstract) — so this should count as single-source for the
  precise "cube" exponent, even though it is corroborated as *structurally*
  consistent with the independently-sourced general (c⁺c⁻)³ conjecture
  formula.

### (d) PROVEN vs OPEN boundary — the most important deliverable

**Central fact, cross-checked across 3 independent search hits (direct
query, "Ramakrishnan Shahidi" query, and the "pi^ table" query, all
converging on the same paper):**

> **Ibukiyama, T. and Katsurada, H., "Exact critical values of the
> symmetric fourth L function and vector valued Siegel modular forms,"
> J. Math. Soc. Japan, Vol. 66, No. 1 (2014), pp. 139–160.
> DOI: 10.2969/jmsj/06610139.**
>
> This paper **proves Zagier's 1977 conjecture** on the exact critical
> values of L(Sym⁴Δ, s): "critical values are products of the same explicit
> rational numbers, powers of π, and the inner product of some vector valued
> Siegel modular form of degree two." Method: **Kim–Ramakrishnan–Shahidi
> lifting** (the symmetric-cube-based genus-2 Siegel lift of
> Ramakrishnan–Shahidi, Math. Res. Lett. 14 (2007), 315–332) + pullback
> formulas + differential operators preserving automorphy under restriction
> of domains. They also exhibit **a congruence between a lift and a
   non-lift** (a secondary, Eisenstein-congruence-flavored result, possibly
   analogous in spirit to the Δ/E₁₂ 691 story but for a different object —
   NOT independently confirmed to be the same 691; flagged as a loose end,
   worth checking directly against the paper if available).
>
> **Crucially — the abstract itself states the boundary directly:**
> "Furthermore, we show **the algebraicity** of the critical values of the
> symmetric fourth L-function of **any** elliptic modular form and give
> **some conjectures in the general case**."

**Reading of the proven/open boundary (synthesized from the above,
consistent across all three hits with no contradiction found):**

| Case | Status | Source |
|---|---|---|
| Sym⁴Δ (level 1, weight 12), **exact** critical values (precise rational number × power of π × ⟨Δ,Δ⟩³, matching Zagier's 1977 conjectured constants exactly) | **PROVEN** (2014, Ibukiyama–Katsurada) | J. Math. Soc. Japan 66(1) |
| Sym⁴ of a **general** elliptic (level-1/classical) modular form, critical values are algebraic numbers (i.e. Deligne's conjecture holds up to an unspecified rational factor, WITHOUT pinning down the exact rational constant) | **PROVEN** (algebraicity only, same 2014 paper) | same |
| Sym⁴ of a general modular form, the **exact** rational constant (matching a precise Zagier-type conjectural formula) | **OPEN / conjectural** ("give some conjectures in the general case" — the paper poses but does not prove the general exact-constant statement) | same, explicit abstract wording |
| Sym⁴ of **Hilbert modular forms** (totally real base field, not just ℚ) | Algebraicity results exist (Morimoto; refined/extended by later authors — "near-central non-critical value" algebraicity by a ScienceDirect-indexed 2021-era paper; a Semantic-Scholar-indexed Chen paper "On Deligne's conjecture for symmetric fourth L-functions of Hilbert modular forms") but this is a **different base field generalization**, not sharper than the ℚ/Δ result — treated as a parallel, not a strengthening | ScienceDirect S0022314X21001803; Semantic Scholar Chen paper (abstract not fully extracted — flagged, see below) |
| Sym⁶ (6th symmetric power), Hilbert modular forms | Proven in a 2021-era arXiv preprint (2110.06261) "extending the result of Morimoto based on a different approach" — mentioned only as context for how far this program has been pushed beyond Sym⁴ | arXiv abstract (2110.06261) |

**What remains OPEN (as directly and explicitly flagged by the primary
source's own abstract, not my inference):** the *exact* Deligne-conjecture
constant for Sym⁴ of a **general** (not level-1/not Δ) modular form. The
2014 paper proves **algebraicity** in general but proves the **precise
constant** only for Δ (via the specific Kim–Ramakrishnan–Shahidi lift
machinery, which uses special features — e.g. that Sym²Δ's Gelbart-Jacquet
lift interacts cleanly with genus-2 Siegel Eisenstein/pullback machinery at
level 1). **I could NOT determine from the accessible sources exactly which
additional critical points (if any) even for Δ itself remain outside the
paper's proof** — the abstract says "the ratio of these critical values are
as conjectured," which reads as **all** of Zagier's critical points for Δ
being covered, but I did not find explicit confirmation of "all N critical
points, here listed" with N given as a number. **This is the one sub-item
of Q4 I could not fully settle and am flagging rather than guessing:**
whether the 2014 Ibukiyama–Katsurada theorem covers literally every
Deligne-critical integer of Sym⁴Δ, or only a subset (e.g. only the "even"
or only the "positive" critical points), was not extractable from the
available abstract-level summaries; a from-source check of the actual paper
(not just its abstract) is needed before the experiment treats "all Sym⁴Δ
critical points are proven-exact" as a settled fact.

**A second, independent, more recent thread (also found, not yet
reconciled with the above):** arXiv search surfaced "On the standard
L-function for GSp₂ₙ×GL₁ and algebraicity of symmetric fourth L-values for
GL₂" (Springer, *Annales mathématiques du Québec*, DOI
10.1007/s40316-020-00134-6) — a different, apparently independent proof
route (via GSp₂ₙ×GL₁ Rankin-Selberg integrals rather than the Siegel
pullback/KRS-lift route) also establishing symmetric-fourth algebraicity.
I did not cross-check whether this covers the SAME critical points/cases as
Ibukiyama–Katsurada or extends them; flagged as a resource for the
experiment team to consult directly if the exact-constant question for
non-Δ forms becomes relevant.

---

## Q5. Published numerical values (VERIFICATION-TIER ONLY — do not consume as inputs)

- **ComputeL** (Tim Dokchitser's PARI/GP package,
  https://people.maths.bris.ac.uk/~matyd/computel/) is the standard tool for
  numerically evaluating motivic L-functions (arbitrary Gamma-factor
  configurations) to high precision, and has been used in at least one
  published example to numerically compute Sym² of a **weight-16 level-1**
  eigenform (not Δ/weight-12, but methodologically identical) against the
  Petersson-norm-based closed form, per an Iwasawa-theory-for-Sym²-modular
  forms paper (arXiv:1512.03678, found via search; not independently
  fetched/read in full).
- A genus-3 Siegel-modular-forms paper (arXiv:0805.2114, "On special values
  of spinor L-functions of Siegel cusp eigenforms of genus 3") is reported
  (via search summary) to contain **explicit numerical tables (their Tables
  6–7)** cross-checking theoretical vs. Dokchitser-computed L-values to
  ~1e-10–1e-15 precision, and the summary states "the computation of L(s, Δ)
  was already mentioned in the previous section" of that paper — suggesting
  it may contain a usable numerical anchor, but **I did not confirm this
  table contains Sym⁴Δ specifically** (as opposed to Δ's ordinary L-function
  or some other lift) — flagged, would need direct retrieval.
- **I did NOT find a directly published numerical table of L(Sym⁴Δ, s) at
  its critical points**, nor a published numerical value of the Sym⁴
  Petersson-period ratio, in any source reachable via the searches run in
  this pass. This is a genuine gap: **no numerical Sym⁴Δ critical-value
  table was located.** If the experiment needs a verification-tier numerical
  anchor, it will likely have to be computed fresh (e.g. via ComputeL/PARI,
  or Magma's L-series package, both of which were confirmed via search to
  support exactly this class of computation) rather than looked up.
- **Reminder per the task instructions:** even if such a table were found,
  it is verification-tier only — the experiment's computation must not
  consume literature numerical values as inputs, only use them (if at all)
  as an independent final check.

---

# EXPERIMENT-READY FACTS

**Formulas to implement:**

1. **Sym² = Ad⁰ for Δ exactly** (trivial nebentypus ⟹ trivial central-character
   twist): L(s, Δ, Ad⁰) = L(s, Sym²Δ), same Euler product, no correction
   factor. Safe to use either name interchangeably for Δ specifically.
2. **Hida/DFG congruence-number identity:** the ℓ-adic valuation of
   L^alg(1, Δ, Ad⁰) (L-value divided by the appropriate period, algebraic
   part) equals (up to the DFG exceptional-set caveat: ℓ ∤ N·k! = 12! for
   Δ, and an irreducibility condition on ρ̄_Δ mod ℓ, both automatically
   satisfiable/checkable for ℓ=691 since 691 is prime, large, and 691 ∤ 12!)
   the size of the congruence module, classically identified for Δ as the
   prime **691** (an Eisenstein, not cusp-cusp, congruence — Δ ≡ E₁₂ mod
   691). Diamond–Flach–Guo (2004) makes the Bloch–Kato/Tamagawa decomposition
   underlying this identity a **proven theorem** (Theorem 0.1, points s=0
   and s=1 of the adjoint motive A_Δ) for ℓ outside that exceptional set —
   this is the "GRH-strength-free, unconditional" rung the experiment can
   build Rung A on.
3. **Sym⁴Δ Deligne-type critical value formula** (general shape, specialized
   to Δ per Zagier 1977 / proven by Ibukiyama–Katsurada 2014):
     L(m, Sym⁴Δ) ~ (2πi)^{3m}·⟨Δ,Δ⟩³·(rational number)   if m even
     L(m, Sym⁴Δ) ~ (2πi)^{2m}·⟨Δ,Δ⟩³·(rational number)   if m odd
   with the **exact** rational constants at each critical m given by
   Zagier's 1977 conjectured table **as proven** by Ibukiyama–Katsurada
   (2014, *J. Math. Soc. Japan* 66(1), 139–160) — this is the "GRH-strength-
   free, unconditional, exact" rung for Rung B, PROVIDED the experiment only
   targets critical points actually covered by that 2014 theorem (see open
   point below).

**Open points to target (i.e., where the experiment could do something the
literature has NOT already nailed down as an exact proven constant):**

- Whether the Ibukiyama–Katsurada (2014) proof covers **every** Deligne-
  critical integer of Sym⁴Δ or only a subset — this was NOT resolved from
  abstract-level sources and is the single biggest unresolved factual
  question from this research pass. If any critical point is left out of
  their proof, that point is a live target.
- The **exact rational constant** for Sym⁴ critical values of a **general**
  (non-Δ, non-CM/dihedral) level-1 eigenform — explicitly flagged as open
  ("give some conjectures in the general case") by the 2014 paper's own
  abstract. Any other weight-k level-1 newform (e.g. weight 16, 18, 20, 22,
  26 — the other level-1 dimensions-1 spaces) is a natural next target using
  the identical machinery.
- The precise δ(ω) sign/parity correction factor in the general Sym⁴
  Deligne-conjecture formula was not fully pinned down in this pass (see Q4c)
  — worth nailing down from Raghuram–Shahidi's paper directly if the
  experiment's numerics depend on getting signs right.

**The two biggest normalization traps:**

1. **Motivic vs. analytic s-normalization shift.** Rank-n motive ↔
   automorphic-π dictionary carries a shift L(s+(n-1)/2, M) = L(s,π); for
   Ad⁰ (rank 3) this is a shift by exactly 1, and for Sym⁴ (rank 5) it would
   be a shift by 2. Every formula pulled from the literature must be checked
   for which convention (Deligne/motivic "critical integers near 0" vs.
   classical-analytic-number-theory "functional equation centered at 1/2 or
   at the middle of the critical strip") it is stated in before the
   experiment's code plugs in a value of s. Mixing conventions silently is
   the single most likely source of an off-by-a-power-of-π or off-by-a-
   twist-character error.
2. **Sym² vs Ad⁰ twist by central character**, and separately, **c⁺c⁻ vs
   ⟨f,f⟩ proportionality constant.** For Δ (trivial nebentypus) the Sym²/Ad⁰
   twist is harmless (item 1 above), but the *rational* proportionality
   constant between the Deligne periods c⁺(Δ)c⁻(Δ) and the Petersson norm
   ⟨Δ,Δ⟩ is convention-dependent across sources (some authors absorb powers
   of 2, π, or i into c⁺/c⁻ differently — this was flagged in Q3/Q4c as
   varying source-to-source) and was NOT pinned down to a single universally
   agreed exact constant in this research pass. The experiment should fix
   its OWN explicit convention for c⁺(Δ), c⁻(Δ) in terms of ⟨Δ,Δ⟩ (e.g. by
   directly following Ibukiyama–Katsurada's own convention if the full paper
   text can be obtained) rather than trusting an unstated "the same up to
   rational number" from a secondary summary.

**Unresolved / could not settle from sources (flagged, not guessed):**

- Exact even-symmetric-power critical-integer inequality (companion to the
  odd-case "r(k-1)+1 ≤ m ≤ (r+1)(k-1)" formula) — not extracted.
- Whether Ibukiyama–Katsurada's 2014 proof is exhaustive over all of Sym⁴Δ's
  critical points or partial.
- The precise δ(ω) factor definition in the general Sym⁴ Deligne formula.
- No numerical L(Sym⁴Δ, s) table was located in the literature (verification
  tier is empty for this specific quantity; would need fresh computation).
- Whether Hida's "adjoint class number formula" (#congruence module =
  L-value, not just "divides"/"same prime factors") is an exact equality or
  an equality-up-to-explicit-fudge-factor — only single-sourced (Hida's own
  notes), not independently cross-checked against a second author's
  restatement of the *exact* (as opposed to prime-divisibility-level)
  identity.
