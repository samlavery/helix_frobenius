# Beyond Endoscopy: Literature Scout Notes (retrieval only, July 2026)

Method note: PDF full text could not be extracted directly (WebFetch returns raw
FlateDecode binary for arXiv/IAS PDFs in this session); all claims below are sourced from
abstracts, author summaries, and secondary descriptions surfaced via web search, cross-checked
across multiple independent search results where possible. Anything not corroborated is
flagged NOT FOUND / UNVERIFIED rather than inferred. Treat formulas below as "as reported,"
not as independently re-derived from primary text — re-verify against the actual PDFs before
using any normalization in a numerical experiment.

---

## EXPERIMENT-READY FACTS (read this section first)

1. **No numerical instrumentation of Beyond Endoscopy sums was found anywhere in the
   literature**, published or preprint, 2004–2026. This is the single load-bearing negative
   result of this search (see §5). If your toolkit runs actual floating-point evaluation of
   the elliptic-term averages, smoothed orbital integrals, or the Poisson-dual sums, that
   appears to be unoccupied ground.

2. **The closest thing to "numerics" in the literature is a pedagogical research-projects
   document**, not a paper: Tian An Wong, "Analytic Experiments Beyond Endoscopy" (Williams
   College SMALL REU program notes, 2016).
   [PDF](https://web.williams.edu/Mathematics/sjmiller/public_html/ntprob19/BeyEndoSMALL2016.pdf)
   It lists three *proposed* student research projects (write the GL(3) regular-elliptic
   integral analogue of Altuğ's GL(2) formula; apply the approximate functional equation +
   Poisson summation and look for cancellation in the dominant term; show the non-elliptic and
   continuous-spectrum contributions vanish or cancel in the limit) — it is a to-do list for
   REU students working through the theory by hand, not a report of executed numerical
   experiments, and does not contain plots, computed values, or code. Do not cite this as
   "numerics were tried."

3. **The one concrete, fully worked, GL(2)/Q instance with pinned normalizations is Altuğ's
   trilogy** (Compositio 2015 / Amer. J. Math. 2017 / J. Inst. Math. Jussieu 2020) — see §3 and
   §6 for the reconstructed shape of the sum. This is the cleanest target for direct numerical
   evaluation, but the exact normalization constants (volume-of-tori factors, the truncation
   parameter in the approximate functional equation, the precise archimedean orbital integral)
   must be pulled from the primal PDFs (§7 lists exact arXiv IDs) — this scout could not
   extract them from PDF text in this session, only from abstracts/secondary description.

4. **The literature's own diagnosis of where the sums die is consistent across sources**: it is
   the **elliptic terms** — orbital integrals over regular elliptic conjugacy classes, weighted
   by volumes of the corresponding elliptic tori (arithmetically: class-number-like factors),
   combined with the **archimedean place**, where the orbital integral itself has singularities
   that must be smoothed by inserting the approximate functional equation for the L-function
   before Poisson summation can be applied. This combination (irregular arithmetic weights ×
   analytic singularities at the archimedean place) is what every source names as "the
   trouble," from Altuğ's own abstract through Sakellaridis's 2022 survey. See §3–4.

5. **Active present-tense front line (2024–2026) is the ramified-GL(2)/Q and GL(3)/Q
   extensions** of Altuğ's method — a running series by Yuhao Cheng (parts 1–4, 2025–2026) and
   a new 122-page GL(3)/Q Poisson summation paper by Taiwang Deng and Malors Espinosa (2026).
   These are the most current statements of exactly which sums remain unresolved; see §4 and §7.

6. **Structural reframing, not analytic attack**: Ben-Zvi–Sakellaridis–Venkatesh "Relative
   Langlands Duality" (2023 circulated / arXiv:2409.04677, Sept 2024) reframes the whole program
   in terms of hyperspherical Hamiltonian varieties and period/L-function duality. It is a
   conjectural organizing framework, not a new analytic technique for evaluating the hard sums
   — no claim there that it resolves the Altuğ-type obstruction. Confirm this framing is
   accurate before citing it as "the current paradigm supersedes the trace-formula obstruction";
   this scout found it described as complementary/structural rather than a replacement for the
   trace-formula computations.

---

## 1. Founding proposals

**Langlands, "Beyond Endoscopy"**, in *Contributions to Automorphic Forms, Geometry, and
Number Theory* (Shalika volume), Johns Hopkins University Press, Baltimore, 2004, pp. 611–697.
Author's preferred version (differs slightly from the Press-edited published version, which
removed some footnotes) hosted at IAS:
[PDF](https://publications.ias.edu/sites/default/files/beyond-endoscopy_rpl_6.pdf),
[IAS page](https://publications.ias.edu/rpl/paper/91).

- Core idea (via secondary description, Herman and others summarizing Langlands): take a
  cuspidal automorphic representation π and its L-function L(s, π, r); the order of the pole at
  s = 1 is detected via the residue of the **logarithmic derivative** of L(s, π, r). Because
  studying a single π directly is hard, Langlands proposes summing this quantity over the
  *full automorphic spectrum* (using the trace formula) so that the average detects which
  π admit a pole — i.e., which π are functorial transfers from a smaller group H.
- Following an observation attributed to Sarnak (per secondary source), the resulting sum
  over primes arising from the logarithmic derivative is harder to analyze than the naive
  picture suggests — NOT FOUND: the exact statement/location of Sarnak's observation within
  the primary text; only referenced secondhand.
- The stable trace formula, weighted by these L-function residues, is the proposed object; per
  Herman's summary this is generalized so that stable multiplicities of representations are
  weighted by the order of poles of the relevant L-function. **UNVERIFIED**: could not confirm
  the exact formula for this weighting from primary text in this session.

**Frenkel–Langlands–Ngô, "Formule des traces et fonctorialité: le début d'un programme,"**
Ann. Sci. Math. Québec 34 (2010), no. 2, 199–243. arXiv:1003.4578
([abs](https://arxiv.org/abs/1003.4578), [pdf](https://arxiv.org/pdf/1003.4578)); also
[IAS page](https://publications.ias.edu/node/93).

- Constructs a family of integral operators on the space of automorphic forms whose
  eigenvalues are expressed in terms of L-functions of automorphic representations, and begins
  analyzing the traces of these operators via the orbital (geometric) side of the **stable**
  trace formula.
- Key structural claim (per abstract/secondary description): the most interesting part of the
  orbital side — corresponding to regular conjugacy classes — is a sum over a
  finite-dimensional vector space over the global field called the **Steinberg–Hitchin base**,
  which can be analyzed via the **Poisson summation formula**.
- Main result stated in the abstract's summary: the **leading term (value at 0) of the dual
  sum** (i.e., the Poisson-dual side) is precisely the **dominant term of the trace formula**,
  i.e., the contribution of the trivial representation — giving hope that the full Poisson
  summation would reveal the functoriality-predicted patterns in the remaining terms.
- Scope note: this first article treats number fields and function fields of curves over
  finite fields only; the authors state intent to treat algebraic curves over C in parallel
  (companion geometric program) — realized partly in Frenkel–Ngô, "Geometrization of trace
  formulas," Bull. Math. Sci. 1 (2011), no. 1, 129–199 (NOT independently verified in this
  session, cited via secondary summary only).

---

## 2. The proven instance: Venkatesh

**Venkatesh, "Limiting Forms of the Trace Formula,"** PhD thesis, Princeton, 2002.
[PDF (Stanford mirror)](http://math.stanford.edu/~akshay/research/thesis.pdf),
[PDF (IAS mirror)](https://www.math.ias.edu/~akshay/research/thesis.pdf).
Published as: "'Beyond endoscopy' and special forms on GL(2)," J. Reine Angew. Math. 577
(2004), 23–80. Paper PDF also at
[math.ias.edu/~akshay/research/be.pdf](https://www.math.ias.edu/~akshay/research/be.pdf).

- What was proven (per thesis abstract, as summarized in search results): the first
  nontrivial case of Langlands' limiting process is carried out unconditionally on GL(2),
  giving an elementary classification of cusp forms π on GL(2) for which the **symmetric
  square L-function L(s, π, Sym²) has a pole** — this pole detects exactly the forms that are
  automorphic inductions of Hecke Grössencharakters from a quadratic extension (dihedral
  forms). Described elsewhere as "one of the simplest cases of the pipe-dream Langlands
  proposes."
- Key analytic device (per secondary description, corroborated across two independent search
  summaries): NOT the Arthur–Selberg trace formula directly, but a **relative trace formula** —
  specifically a variant, for PGL(2), of the **Kuznetsov–Bruggeman–Miatello formula**. So the
  device is Kuznetsov (relative trace formula) + Poisson summation, matching the question's
  hypothesis. NOT FOUND: an explicit primary-text confirmation of exactly how Poisson summation
  enters alongside Kuznetsov (only the "Kuznetsov trace formula as main tool" framing was
  corroborated).
- Why it didn't extend (per Zhaolin Li, arXiv:2410.15627, describing the state of the art —
  see §3): "the original idea of weighting by logarithmic derivatives of L-functions is now
  recognized as particularly challenging to implement" beyond this case, and Venkatesh's success
  is characterized as one of only a small number of successes of the whole program. NOT FOUND:
  a first-person statement by Venkatesh himself (in the thesis or the JRAM paper) diagnosing
  exactly why the Sym² method does not generalize to Sym³, Sym⁴, or to GL(n) — only
  third-party framing was retrieved.
- Side results in the same thesis (per abstract): a converse theorem derived by the same
  method, and a sharper-than-Duke bound on the dimension of weight-1 forms, generalized to
  arbitrary number fields.

---

## 3. Altuğ's series — where exactly the sums get hard

**S. Ali Altuğ, PhD thesis**, "Beyond Endoscopy via the Trace Formula," Princeton, 2013.
NOT FOUND: direct link retrieved in this session.

**Part I**: "Beyond endoscopy via the trace formula: I. Poisson summation and isolation of
special representations," Compositio Math. 151 (2015), no. 10, 1791–1820. arXiv:1506.02218
([abs](https://arxiv.org/abs/1506.02218), [pdf](https://arxiv.org/pdf/1506.02218)).

Abstract (retrieved in full via WebFetch on the arXiv abstract page):
> "With analytic applications in mind, in particular Beyond Endoscopy, we initiate the study
> of the elliptic part of the trace formula. Incorporating the approximate functional equation
> to the elliptic part we control the analytic behavior of the volumes of tori that appear in
> the elliptic part. Furthermore by carefully choosing the truncation parameter in the
> approximate functional equation we smooth-out the singularities of orbital integrals.
> Finally by an application of Poisson summation we rewrite the elliptic part so that it is
> ready to be used in analytic applications, and in particular in Beyond Endoscopy."

**Part II**: "Beyond Endoscopy via the trace formula – II: Asymptotic expansions of Fourier
transforms and bounds towards the Ramanujan conjecture," Amer. J. Math. 139 (2017), no. 4,
863–913. arXiv:1506.08911
([abs](https://arxiv.org/abs/1506.08911), [pdf](https://arxiv.org/pdf/1506.08911)).
- Per abstract/secondary summary: continues by applying Poisson summation to the elliptic part,
  then studies the remaining terms by computing **Fourier transforms of the (now-smoothed)
  orbital integrals**, obtaining exact asymptotic expansions. As an application, recovers
  (via the Arthur–Selberg trace formula) **Kuznetsov's bound** that the trace of the p-th Hecke
  operator on cuspidal automorphic representations is O(p^{1/4}) — i.e., a Ramanujan-type bound
  falls out as a corollary of the same machinery.
- NOT FOUND in this session: which specific Fourier transforms (of which orbital integral, at
  which place) are computed; the exact singular-series structure. Needs primary-text
  extraction.

**Part III**: "Beyond Endoscopy via the trace formula – III: The standard representation," J.
Inst. Math. Jussieu 19 (2020), no. 4, 1349–1387. arXiv:1512.09249
([abs](https://arxiv.org/abs/1512.09249), [pdf](https://arxiv.org/pdf/1512.09249)).
- Per secondary summary (corroborated across two searches): finalizes the asymptotic expansion
  of the beyond-endoscopic averages for the **standard L-function** attached to weight-k ≥ 3
  cusp forms on GL(2) over Q, restricted to ramification only at the infinite place. This is
  presented as **the first full execution of Beyond Endoscopy via the Arthur–Selberg trace
  formula exactly as Langlands originally proposed** (as distinct from Venkatesh's relative
  trace formula route). As an application it reproves analytic continuation of L(s, Δ)
  (Ramanujan's Δ).
- Method (per secondary summary): expresses volume-of-tori factors as values of Hecke
  L-functions, and uses the approximate functional equation strategically so that the
  **archimedean orbital integral's singularities** can be overcome — this is stated to be
  *necessary* before Poisson summation is applicable. Contains explicit sections titled
  "Archimedean analysis" and "Non-Archimedean analysis" (confirmed structurally, content
  not extracted).

**Named bottleneck, as consistently reported across all secondary sources for this trilogy**:
the elliptic part of the trace formula involves averages of orbital integrals weighted by
arithmetic data (volumes of tori — essentially class-number-like quantities) *varying
irregularly across the family* being summed, layered on top of the orbital integrals'
**intrinsic singularities at the archimedean place**. Both must be tamed simultaneously: the
approximate functional equation (i.e., truncating the L-function's defining Dirichlet series
at a height tied to the conductor) is the tool that does both jobs at once — regularizing the
archimedean singularity and making the resulting sum amenable to Poisson summation. This is
NOT the "singular series" in the classical circle-method sense; it is closer to your toolkit's
framing of "smooth-entry windows with growth envelopes" — the approximate functional equation
plays the role of the smoothing window. **This parallel (approximate functional equation ~
smooth truncation with growth envelope) is this scout's own observation for relevance framing,
not a claim found in the literature — flag it as such if it goes in a report.**

Sym² / higher-representation obstruction: a 2025 note ("A note on Poisson summation for
GL(2)," arXiv:2510.02273 — NOT independently fetched, only summarized via search) reportedly
explains that the standard representation is tractable partly *because* it is 1-dimensional in
an essential sense (any rep of GL(1) is 1-dimensional), whereas Sym² and higher live in
higher-dimensional representation spaces r, and "the pole structure of L(s,π,r) becomes
representation-dependent and more complex" — this is offered as the reason Altuğ's exact
method does not simply transplant to Sym². **This is a paraphrase from search-result text, not
a verified quotation from the primary paper — treat as a plausible but unverified
characterization.**

---

## 4. Since 2015 — extensions, and what's identified as the current bottleneck

**GL(n) smoothing extension**: González, Kwan, Miller, Van Peski, Wong, "On smoothing
singularities of elliptic orbital integrals on GL(n) and Beyond Endoscopy," J. Number Theory
(2018-ish; exact volume NOT FOUND in this session). arXiv:1608.05938
([abs](https://arxiv.org/abs/1608.05938), [pdf](https://arxiv.org/pdf/1608.05938)).
Full abstract (retrieved via WebFetch):
> "Recent work of Altuğ continues the preliminary analysis of Langlands' Beyond Endoscopy
> proposal for GL(2) by removing the contribution of the trivial representation to the trace
> formula using a Poisson summation formula. We show that Altuğ's method of smoothing real
> elliptic orbital integrals by an approximate functional equation extends to GL(n). We also
> discuss the case of an arbitrary reductive group, and remaining obstructions for applying
> Poisson summation."
- Confirms the smoothing step (real-place approximate-functional-equation trick) generalizes
  mechanically to GL(n) and to general reductive groups, but **explicitly states unspecified
  "remaining obstructions for applying Poisson summation"** persist beyond the smoothing step
  itself — i.e., smoothing the singularity is necessary but not sufficient; the Poisson
  summation / duality step is where the general-G obstruction lives. NOT FOUND: the precise
  nature of those remaining obstructions from primary text in this session.

**Rankin–Selberg**: Herman, "Beyond endoscopy for the Rankin-Selberg L-function," arXiv:1003.0462
([pdf](https://arxiv.org/pdf/1003.0462)) — extends the trace-formula-limit idea to Rankin–Selberg
L-functions. NOT independently examined for obstruction detail in this session.

**Asai L-function**: "Quadratic Base Change and the Analytic Continuation of the Asai
L-function: A new Trace formula approach," arXiv:1008.3921
([pdf](https://arxiv.org/pdf/1008.3921)) — shows a simple pole at s=1 of the Asai L-function
detects base change. NOT independently examined for obstruction detail.

**Arthur's r-trace formula program**: James Arthur, "Problems Beyond Endoscopy," in
*Representation Theory, Number Theory, and Invariant Theory* (Conf. in honor of Roger Howe's
70th birthday), Progr. Math. 323, Birkhäuser, 2018, pp. 23–46.
[PDF](https://www.math.toronto.edu/arthur/pdf/Arthur.pdf) (ResearchGate mirror returned 403 in
this session; use the math.toronto.edu link instead).
Companion: "A stratification related to characteristic polynomials," Adv. Math. 327 (2018),
425–469 (NOT independently fetched).
- Per secondary summary: Arthur frames the central difficulty as **absorbing the nontempered
  characters in the automorphic discrete spectrum of G into the geometric expansion of the
  stable trace formula SG(f)** — i.e., the spectral side has nontempered pieces (residual
  spectrum, Eisenstein contributions) that must be matched against geometric data before a
  clean r-trace formula (spectral side weighted by L-function data) can be established. Notes
  that Altuğ's approach truncates the left-hand side specifically **to avoid confronting
  weighted orbital integrals** — a simplification Arthur flags as avoiding rather than solving
  part of the general problem.
- Follow-up: "A weighted invariant trace formula," Ann. Math. Québec (2022),
  [link](https://link.springer.com/article/10.1007/s40316-022-00200-1) — extends
  Finis–Lapid–Müller's continuity results for the coarse noninvariant trace formula to the
  refined and then invariant trace formula, builds weighted endoscopic/stable trace formulas
  with discrete spectral terms weighted by L-functions via "basic functions," and states that
  meromorphic continuation of these weighted formulas would yield genuine r-trace formulas —
  framed as a **precursor** to, not yet an achievement of, the r-trace formula. Also
  introduces a **weighted form of the Langlands–Shelstad transfer conjecture**, generalizing
  Arthur's weighted fundamental lemma — this is new unproven conjectural machinery, not a
  closed result. NOT FOUND: author names for this 2022 paper in this session (search results
  described it only relative to Arthur's essay; could not confirm if Arthur himself or another
  author wrote it — flag for verification).

**Ngô's Hankel-transform / monoid program**: B.C. Ngô, "Hankel transform, Langlands
functoriality and functional equation of automorphic L-functions," Japanese J. Math. (2019),
[link](https://link.springer.com/article/10.1007/s11537-019-1650-8); NSF mirror:
[PDF](https://par.nsf.gov/servlets/purl/10182563).
- Per secondary summary: surveys automorphic-L-function theory and endoscopy, reviews
  Langlands' Beyond Endoscopy idea as "constructing a limiting form of the trace formula whose
  spectral development is weighted by numbers related to poles of automorphic L-functions,"
  and Ngô's own contribution is attempting, in full generality, the construction of an
  **"L-monoid"** and a kernel conjectured to be the **Hankel kernel** governing the nonabelian
  Fourier transform needed for functional equations.
- Related: reductive/Vinberg-type monoid resolution work connecting to Braverman–Kazhdan's
  conjecture (search surfaced "On the resolution of reductive monoids and multiplicativity of
  γ-factors," ResearchGate — NOT independently fetched) — a version of Braverman–Kazhdan
  suitable for archimedean spherical representations, feeding into the trace formula.
  Motivated explicitly by Ngô's suggestion to combine **nonabelian Fourier transforms** with
  the trace formula to prove functional equations of general Langlands L-functions.

**Sakellaridis' relative program**: Y. Sakellaridis, "Transfer operators and Hankel transforms
between relative trace formulas, I: character theory" and "II: Rankin-Selberg theory," Adv.
Math. 394 (2022), Paper Nos. 108010 and 108039.
arXiv I: [1804.02383](https://arxiv.org/pdf/1804.02383);
arXiv II: [1805.04640](https://arxiv.org/pdf/1805.04640).
Also: "Beyond Endoscopy for the Relative Trace Formula II: global theory," arXiv:1402.3524
([pdf](https://arxiv.org/pdf/1402.3524)).
- Reframes functoriality-via-poles as a special case of a broader conjecture: replace reductive
  groups with **spherical varieties**, and the trace formula with the **relative trace
  formula**; "transfer operators" generalizing endoscopic transfer factors are constructed via
  Fourier/Hankel-type transforms, with matching/fundamental-lemma/character-transfer properties
  expected of any trace-formula comparison.

**Survey with explicit bottleneck language**: Y. Sakellaridis, "Local and global questions
'beyond endoscopy'," for the Proc. 2022 IHES Summer School on the Langlands program (published
~2022 per AMS). arXiv:2310.02438
([html](https://arxiv.org/html/2310.02438)).
- Per WebFetch summary of this survey: identifies the core bottleneck as the **"difficult
  analytic expressions that arise after inserting L-functions into the trace formula"**, states
  that brute-force techniques (i.e., Altuğ-style direct analysis) **"don't scale to higher rank
  cases,"** and that the actual computations involve managing geometric expressions —
  particularly **logarithmic derivatives of L-functions** — that are "prohibitively difficult"
  in general. This is the closest thing found to an explicit statement of *current consensus*
  on the bottleneck (2022, from a leading practitioner, for a summer-school audience).
- Open problems flagged in that survey per the same summary: explicit transfer operators for
  higher rank (beyond SL2); D. Johnstone's work generalizing Gelfand–Graev–Piatetski-Shapiro
  formulas to higher rank (more complete when n is prime); Johnstone & Z. Luo on transfer
  operators for symmetric-power representations Symⁿ: GL(2) → GL(n+1); and the relationship
  between beyond-endoscopy methods and symplectic/quantization geometry described as "largely
  unexplored" as of that writing. NOT FOUND: primary-text confirmation of these exact framings;
  relayed via WebFetch summary of the HTML page, not independently spot-checked line by line.

**Structural reframing (2023/2024)**: D. Ben-Zvi, Y. Sakellaridis, A. Venkatesh, "Relative
Langlands Duality." Circulated 2023; posted arXiv:2409.04677 (Sept 2024),
[abs](https://arxiv.org/abs/2409.04677) — 451 pages per secondary description.
- Proposes a duality pairing a Hamiltonian G-variety with a dual-group Hamiltonian variety,
  such that the "period" on one side matches the "L-function" on the dual side — described as
  an arithmetic analogue of electric–magnetic duality (Kapustin–Witten's TQFT interpretation of
  geometric Langlands duality; Gaiotto–Witten boundary conditions). Basic objects are
  "hyperspherical varieties." Double-dual is conjectured to return the original variety
  (period/L-function roles swap).
- Precursors: 2022 ICM talk (Sakellaridis and/or Venkatesh — NOT FOUND which exactly), 2022
  Arizona Winter School lectures, Ben-Zvi's Spring 2021 graduate course notes.
- Explicit search for a stated connection between this paper and resolving the Beyond-Endoscopy
  analytic bottleneck came back empty: **this is a structural/organizing framework, not a claim
  to have solved the archimedean-orbital-integral or elliptic-terms problem.** Treat it as
  orthogonal context, not as superseding §3–4's obstruction.

**2018–2025, sums actually being attacked (the searched names)**:
- Getz–Hahn: co-authored the textbook *An Introduction to Automorphic Representations: With a
  View Toward Trace Formulae*, GTM 300, Springer, 2024 — pedagogical/foundational, not itself
  a new attack on the bottleneck (per search result). Getz separately has work on
  Braverman–Kazhdan local functional equations relevant to trace-formula kernels (title/venue
  NOT FOUND precisely in this session).
- Emory, Espinosa (Lara), Kundu, Wong, "Beyond Endoscopy via Poisson Summation for GL(2,K),"
  arXiv:2404.10139 ([pdf](https://arxiv.org/pdf/2404.10139)). Generalizes Altuğ's Part I to a
  class of totally real number fields K, cancelling trivial + special representation
  contributions via additive Poisson summation on the elliptic terms. Paper structure includes
  sections "The Main Setup," "Manipulation of the Regular Elliptic Part," "The Approximate
  Functional Equation," "Smoothing the Singularities" — i.e., replays Altuğ's exact recipe over
  a general totally real field.
- Yuhao Cheng, **"Beyond endoscopy for GL2 over Q with ramification," parts 1–4** (2025–2026,
  very recent/live):
  - Part 1: "Poisson summation," arXiv:2505.18967 ([abs](https://arxiv.org/abs/2505.18967)) —
    generalizes isolation of special representations in the elliptic part to the *ramified*
    setting (Altuğ's original work restricted ramification to the infinite place only),
    described as "resolving a problem open for over a decade."
  - Part 2: "bounds towards the Ramanujan conjecture," arXiv:2507.09655.
  - Part 3: "contribution of the elliptic part," arXiv:2508.07167.
  - Part 4: "contribution of non-elliptic parts," arXiv:2605.20719 (note: this arXiv ID's date
    stamp, 2605, is later than "today" in the CLAUDE.md session date of 2026-07-02 by
    calendar-month convention if arXiv IDs encode YYMM — **flag this as a possible typo or a
    genuinely very recent/forthcoming preprint; not independently confirmed to exist/resolve**).
  - This is the most active, most current front line of exactly-Altuğ's-program extension.
- Taiwang Deng, Malors Espinosa, "Beyond Endoscopy for GL(3,Q): Poisson Summation,"
  arXiv:2603.21506, 122 pages ([pdf](https://arxiv.org/pdf/2603.21506) — metadata only
  extracted; full text not retrievable as text in this session). This is the first GL(3) case
  of the full Altuğ-style program (as opposed to the GL(n) *smoothing-only* extension of
  §4/González et al.). NOT FOUND: what specific new obstruction GL(3) introduces beyond
  smoothing (higher-rank torus volumes? multiple archimedean K-Bessel-type transforms?) — needs
  primary-text extraction.
- Also found: "A GL(3) converse theorem via a 'beyond endoscopy' approach,"
  arXiv:2401.04037 — a related but distinct GL(3) beyond-endoscopy-flavored result (converse
  theorem, not full functoriality detection). NOT independently examined.
- Search also surfaced Qi Zhi, "On the Fourier Transform of Regularized Bessel Functions on
  Complex Numbers and Beyond Endoscopy Over Number Fields," IMRN (2021) — suggests the
  archimedean-place K-Bessel/regularized-Bessel Fourier transform is indeed treated as a
  distinct hard sub-problem worth its own paper, corroborating §3's framing that the
  archimedean orbital-integral transform is a genuine bottleneck, not just bookkeeping.
- Names searched with **no results found** in this session specifically attacking the analytic
  sums: **Johnstone** (found only as referenced within Sakellaridis's survey, no standalone
  paper retrieved), **Hahn** (only the textbook), **Espinosa** appears (Emory–Espinosa–Kundu–
  Wong and Deng–Espinosa), **Chen** — NOT FOUND as a distinct beyond-endoscopy author in this
  search.

---

## 5. Numerics — the negative result

Explicit, repeated searches for "numerical computation," "SageMath," "PARI," "numerically
analyzed," "visualize pole," "smoothing test function experiment" combined with "beyond
endoscopy" across 2015–2026 window turned up:

- **No paper that reports an actual floating-point/computer-algebra computation of the
  elliptic-term averages, the Poisson-dual sums, or pole-detection quantities.**
- **No plots or visualizations of pole detection.**
- One search result's phrasing ("the elliptic part, although numerically analyzed, was not
  treated in earlier work") appears to be this scout's own search-summary artifact/misreading
  rather than a verified claim from a primary source — **do not rely on this phrase**; it could
  not be traced back to a specific paper or quotation on recheck, and reads as ambiguous
  auto-generated summary text rather than a sourced fact. Treat as NOT FOUND / retracted.
- The Wong "Analytic Experiments" document (§ EXPERIMENT-READY FACTS, item 2) is REU
  project-proposal prose, explicitly framed as suggested future student work, not results.
- The GKMVW paper (arXiv:1608.05938) does involve the **Kronecker symbol** in its expression of
  GL(2) orbital integrals (per its abstract/summary) — the Kronecker symbol is trivially
  computable in SageMath/PARI, which is a strong hint that instrumenting Altuğ's or GKMVW's
  formulas numerically would be mechanically straightforward (no exotic special functions
  needed beyond the archimedean K-Bessel-type transform), but **no source claims this was ever
  actually done**.

**Conclusion for relevance filtering**: numerically instrumenting the Beyond-Endoscopy elliptic
sums — testing smoothings, visualizing where pole-detection succeeds or fails as a function of
truncation parameter, height, or conductor — appears to be genuinely new ground as of this
search. This is consistent with the field's own self-description (Sakellaridis 2022) as
analytically bottlenecked rather than computationally explored.

---

## 6. Toward an experiment-ready sum (GL(2)/Q, Altuğ Part I–III route)

**Primary-text extraction failed in this session** (WebFetch returned only raw PDF binary/
FlateDecode streams for the arXiv and IAS PDFs tried: 1506.02218, 1512.09249, 1003.4578,
beyond-endoscopy_rpl_6.pdf, 2603.21506). What follows is the *shape* of the target sum as
reconstructed from abstracts and secondary description only — **every normalization constant
below is UNVERIFIED and must be pulled from primary text (or an HTML-rendered arXiv mirror, or
a PDF-to-text tool) before any numerical code is written.** Treat this as a map of what to look
for, not a formula to implement directly.

Shape of the target (GL(2)/Q, standard representation, Altuğ Part III):
- Base object: the Arthur–Selberg trace formula for GL(2)/Q, restricted to its **elliptic
  part** — a sum over regular elliptic conjugacy classes (equivalently, over positive
  discriminants / real quadratic orders, since elliptic elements of GL(2,Q) correspond to
  elements generating real quadratic subalgebras) of (orbital integral) × (volume of the
  associated elliptic torus, i.e., a **class-number × regulator**-type factor).
- Weighting: this elliptic sum is convolved against a **test function** built from the
  **approximate functional equation** for the L-function L(s, π, r) being probed (standard
  L-function for Part III) — concretely, this looks like truncating the Dirichlet series for
  L(s,π) (or its logarithmic derivative) at a length tied to a parameter X (playing the role of
  "analytic conductor" or height), which is exactly the "truncation parameter" the abstract
  says is "carefully chosen" to smooth the archimedean orbital integral's singularity.
- Poisson step: the resulting sum (over discriminants, weighted by the smoothed orbital
  integral × truncated L-series) is Poisson-summed; the dual sum's leading term (per the
  FLN structural claim in §1, echoed for the GL(2) elliptic case) should reproduce the trivial-
  and special-representation contributions, and the **remaining dual terms are Part II's
  object** (Fourier transforms of the smoothed orbital integrals, yielding the Kuznetsov-type
  p^{1/4} bound as a byproduct).
- **Normalization traps to check explicitly against primary text before coding**:
  1. Exact definition of "volume of the elliptic torus" — is it literally the class number
     h(D) of the order of discriminant D, or h(D) times a regulator/unit factor (real quadratic
     orders have nontrivial unit groups, unlike imaginary quadratic)? This is the single most
     likely silent-bug source (cf. your team's own lattice-MC pitfall precedent of missing a
     structural factor).
  2. The precise truncation parameter X in the approximate functional equation — Altuğ "
     carefully chooses" it; the choice is tied to the conductor/weight k of the cusp form being
     tested and is likely NOT a free parameter you can pick arbitrarily without breaking the
     cancellation.
  3. Whether the sum is over **all** discriminants D or only fundamental discriminants, and how
     non-fundamental D (orders vs. maximal orders) are folded in or excluded.
  4. The exact archimedean orbital integral being smoothed — likely a K-Bessel function
     evaluated at an argument depending on D and the weight k; Qi Zhi's 2021 IMRN paper (§4)
     on "regularized Bessel function Fourier transforms" suggests this is nontrivial enough to
     be its own paper, i.e., not a closed-form elementary function — get the exact definition
     before assuming an off-the-shelf `scipy.special.kv` call suffices.
  5. Normalization of the L-function itself (analytic vs. arithmetic normalization, i.e.,
     whether Satake parameters are normalized to |α_p|=1 or to the Ramanujan-conjectural
     unnormalized weight-k convention) — this is the single most common cross-paper
     normalization mismatch in this literature generally, not specific to Altuğ.
  6. Whether "s=1" in the pole-detection statement is in analytic normalization (functional
     equation s ↔ 1−s) or classical normalization (functional equation s ↔ k−s) — conflating
     these silently shifts every truncation length by a factor tied to k.

**Recommendation**: before writing any code, fetch arXiv:1512.09249 (Altuğ III) as HTML if an
HTML rendering exists (check `arxiv.org/abs/1512.09249` for an "HTML" toggle; older papers
sometimes lack one, in which case use a PDF-to-text tool locally, e.g. `pdftotext`, rather than
WebFetch, which only saw binary in this session) and extract Sections on "Archimedean
analysis" and the elliptic-part formula verbatim, plus Part I's Poisson summation formula
(Theorem/Proposition numbers not retrieved in this session) verbatim, before pinning constants.

---

## 7. Full reference list (arXiv IDs for direct retrieval)

| # | Reference | ID / link |
|---|---|---|
| 1 | Langlands, "Beyond Endoscopy" (2004) | [IAS PDF](https://publications.ias.edu/sites/default/files/beyond-endoscopy_rpl_6.pdf) |
| 2 | Frenkel–Langlands–Ngô (2010) | arXiv:1003.4578 |
| 3 | Venkatesh thesis (2002) | [Stanford mirror](http://math.stanford.edu/~akshay/research/thesis.pdf) |
| 4 | Venkatesh, JRAM 577 (2004) | [IAS mirror](https://www.math.ias.edu/~akshay/research/be.pdf) |
| 5 | Altuğ I, Compositio 151 (2015) | arXiv:1506.02218 |
| 6 | Altuğ II, Amer. J. Math 139 (2017) | arXiv:1506.08911 |
| 7 | Altuğ III, JIMJ 19 (2020) | arXiv:1512.09249 |
| 8 | González–Kwan–Miller–Van Peski–Wong, GL(n) smoothing | arXiv:1608.05938 |
| 9 | Herman, Rankin–Selberg | arXiv:1003.0462 |
| 10 | Asai L-function trace formula approach | arXiv:1008.3921 |
| 11 | Arthur, "Problems Beyond Endoscopy" (2018) | [PDF](https://www.math.toronto.edu/arthur/pdf/Arthur.pdf) |
| 12 | Arthur, "A weighted invariant trace formula" (2022) | Ann. Math. Québec, [link](https://link.springer.com/article/10.1007/s40316-022-00200-1) |
| 13 | Ngô, Hankel transform survey (2019) | [NSF PDF](https://par.nsf.gov/servlets/purl/10182563) |
| 14 | Sakellaridis, Transfer operators I | arXiv:1804.02383 |
| 15 | Sakellaridis, Transfer operators II | arXiv:1805.04640 |
| 16 | Sakellaridis, Relative trace formula II global | arXiv:1402.3524 |
| 17 | Sakellaridis, "Local and global questions beyond endoscopy" (2022/2023) | arXiv:2310.02438 |
| 18 | Ben-Zvi–Sakellaridis–Venkatesh, "Relative Langlands Duality" | arXiv:2409.04677 |
| 19 | Emory–Espinosa–Kundu–Wong, GL(2,K) | arXiv:2404.10139 |
| 20 | Cheng, GL2/Q ramification Part 1 | arXiv:2505.18967 |
| 21 | Cheng, Part 2 (Ramanujan bounds) | arXiv:2507.09655 |
| 22 | Cheng, Part 3 (elliptic part) | arXiv:2508.07167 |
| 23 | Cheng, Part 4 (non-elliptic parts) | arXiv:2605.20719 (date-stamp anomaly, verify) |
| 24 | Deng–Espinosa, GL(3,Q) Poisson summation | arXiv:2603.21506 |
| 25 | GL(3) converse theorem via beyond endoscopy | arXiv:2401.04037 |
| 26 | Qi Zhi, regularized Bessel FT, IMRN 2021 | NOT FOUND (arXiv ID not retrieved) |
| 27 | Wong, "Analytic Experiments Beyond Endoscopy" (REU notes, 2016) | [PDF](https://web.williams.edu/Mathematics/sjmiller/public_html/ntprob19/BeyEndoSMALL2016.pdf) |
| 28 | Li, Poisson/Kuznetsov on GL2 (2024) | arXiv:2410.15627 |
| 29 | "A Beyond Endoscopy Derivation of the Functional Equation for the Symmetric-Square L-Function" | arXiv:2606.15729 |
| 30 | "A note on Poisson summation for GL(2)" | arXiv:2510.02273 |
| 31 | Getz–Hahn, GTM 300 (2024) | Springer (no arXiv ID found) |

Note on items 20–24, 29, 30: several of these arXiv IDs (e.g. 2605.xxxxx, 2606.xxxxx,
2603.xxxxx) postdate this scout's own knowledge horizon assumptions and were surfaced purely by
live web search — they read as genuine very-recent/forthcoming preprints given the session's
stated current date of 2026-07-02, but their existence and content were **only confirmed via
search-result titles/snippets, not by successfully rendering full text**. Re-verify each
resolves to a real, retrievable arXiv page before citing in anything downstream.
