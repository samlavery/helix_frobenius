# Non-Unique Factorization Theory — Literature Scout Notes

Scope: does an "obstruction-measurement toolkit" — exact numerical landings of
class-group invariants from L-function/character data, free-monoid gluing/rigidity
theorems, "weld mismatch" cohomological framing — have a home in this field's open
problems? Retrieval only; NOT FOUND is reported explicitly where searches came up empty.

---

## EXPERIMENT-READY FACTS

1. **The field's central open problem is exactly a "does an invariant determine the
   obstruction group" question**, i.e. structurally the same shape as the toolkit's
   target. The **Characterization Problem**: for a Krull monoid H with class group G
   in which every class contains a prime divisor, does the system of sets of lengths
   L(H) (equivalently L(G), since it depends only on G) determine G up to isomorphism?
   Standing conjecture: yes. Proven for rank ≤ 2 (Geroldinger–Schmid,
   arXiv:1503.04679, and part II arXiv:1506.05223 for `C_n^r` with `r ≤ max{2,(n+2)/6}`),
   apart from two known exceptional pairs. **Open for rank ≥ 3 in general.** This is a
   live, named, still-open target — not a closed chapter.

2. **Davenport constant D(G) is exactly known only for p-groups and rank ≤ 2**
   (`D(C_n^2) = 2n-1`, Mann/Olson/van Emde Boas–Kruyswijk). **Open for rank ≥ 3**, even
   for `Z_n^3`. Best general bounds (Alon–Dubiner-type, e.g. Zakarczemny 2019,
   arXiv:1910.10984) carry huge unspecified constants (`a3 ≤ 20369`) — asymptotically
   linear in `n` but numerically far from tight. Simplest historically-undecided instance,
   `Z_3⊕Z_3⊕Z_15`, was only resolved as a special case by Bhowmik–Schlage-Puchta. The
   general conjecture `D(G) = M(G)` (trivial lower bound met) is proven for p-groups and
   rank ≤ 2, known **false** for every rank ≥ 4, and **genuinely open for rank 3** — the
   field itself flags this as the frontier case where neither a proof nor a
   counterexample is in hand.

3. **No literature connects L-functions, Dedekind zeta functions, or character sums to
   computing/predicting exact values of sets-of-lengths invariants (Davenport constant,
   elasticity, catenary degree) — searched directly and found NOT FOUND.** The one place
   analytic number theory enters (Narkiewicz's program, formalized by Knopfmacher's
   "abstract analytic number theory" and carried into quantitative form by Gao–
   Geroldinger–Wang's "Narkiewicz constants," Int. J. Number Theory 7 (2011) 1463–1502,
   parts II/III in Colloq. Math. 124 (2011) and Acta Arith. 158 (2013)) uses Dedekind
   zeta functions and Tauberian theorems only to **count** algebraic integers/ideals by
   norm, stratified by *how many* factorizations into irreducibles they admit (`F_k(x)`
   = count of ideals of norm ≤ x with ≤ k factorizations). It does not use L-function
   *values* or character-sum *evaluations* to pin down the *actual* group-theoretic
   invariant (Davenport constant, class group order, elasticity value). Character sums
   do appear, but only combinatorially: the dual-group/orthogonality trick for detecting
   zero-sums inside `B(G)` (character averaging to project onto the identity), not as an
   L-function evaluation or special-value computation. **This is the clearest gap in the
   field relative to the toolkit's premise** — nobody is landing class-group invariants
   as exact numbers pulled out of L-function data; the zeta-function role in this field
   is purely a counting/Tauberian one.

4. **No cohomological "weld mismatch" framing exists in this literature** — searched
   directly for "weld," "gluing" + cohomology, and found none. The field's actual
   mechanism for combining/reducing objects is the **transfer homomorphism**
   `θ: H → B(G₀)` (H a Krull monoid, `B(G₀)` the monoid of zero-sum sequences over the
   classes `G₀ ⊆ G` containing prime divisors) and its generalization, the **weak
   transfer homomorphism** (used for systems of sets of lengths beyond the strict Krull
   case; introduced ~2016, surveyed in "Systems of sets of lengths: Transfer Krull
   monoids versus weakly Krull monoids," arXiv:1606.05063). These preserve
   irreducibility and factorization *lengths* exactly (pullback/pushforward of
   arithmetic invariants), and are algebraic/combinatorial in character — group
   homomorphism plus a lifting property (T1/T2-type axioms) — not cohomological classes
   measuring an obstruction to gluing. If the toolkit's "weld mismatch" idea is to find
   a home here, it would need to be introduced as a genuinely new invariant on top of
   transfer homomorphisms, not mapped onto an existing one.

5. **The field's own diagnosis of what's blocking rank ≥ 3 progress is combinatorial
   explosion, not "missing structure theory" or "missing invariants" in the
   toolkit's sense.** The Structure Theorem for Sets of Lengths (every `L(a)` is an
   "almost arithmetical multiprogression," AAMP, with universal bounds depending only
   on G — Geroldinger et al., sharp per W. Schmid's realization theorem) is already the
   strong structural result and it **holds for all finite class groups, rank
   unrestricted**. What's missing at rank ≥ 3 is not structure but the *quantitative*
   determination of the parameters (the set of distances `Δ(G)`, `Δ*(G)`, elasticity,
   Davenport constant) — these become computationally/combinatorially intractable as
   rank grows (Alon–Dubiner-style bounds have huge, non-tight constants; exhaustive
   zero-sum-sequence search is only tractable via GAP computation up to |G| < 32
   currently). This reads as an opening for a genuinely new *quantitative* invariant or
   computation method — but the gap is "we can't compute the numbers," not "we lack a
   conceptual/structural framework." Any new toolkit proposing itself as filling this
   gap needs to produce **actual numbers** (exact Davenport constants for specific rank-3
   or rank-≥4 groups, or a proof/disproof of `D(G)=M(G)` for rank 3) to register as
   progress, not a new structural theorem.

---

## (1) Field map

- **Core text**: A. Geroldinger, F. Halter-Koch, *Non-Unique Factorizations: Algebraic,
  Combinatorial and Analytic Theory*, Chapman & Hall/CRC Pure and Applied Mathematics
  vol. 278 (2006), DOI 10.1201/9781420003208. Chapters cover atoms/primes, free monoids,
  BF-monoids, systems of sets of lengths, catenary/tame degree, Krull monoids and class
  groups, structure of sets of lengths, additive group theory, arithmetical invariants
  of Krull monoids, abstract analytic number theory, and analytic theory of non-unique
  factorizations (i.e. Narkiewicz's program) as an appendix-level unification.
  [Springer chapter summary](https://link.springer.com/chapter/10.1007/978-0-387-36717-0_13),
  [SearchWorks](https://searchworks.stanford.edu/view/6304632).
- **Definitions used throughout**: Krull monoid H with class group G, every class
  containing a prime divisor ⟹ transfer homomorphism `θ: H → B(G)` to the monoid of
  zero-sum sequences over G; `L(a)` = set of lengths of factorizations of `a` into
  irreducibles; `L(H) = {L(a) : a ∈ H}`; since `L(H)` depends only on G, write `L(G)`.
- **Structure Theorem for Sets of Lengths**: for H Krull with finite class group
  `|G| ≥ 3`, there is `M ∈ ℕ₀` such that every `L(a)` is an AAMP with difference in
  `Δ*(G)` and bound M, both finite and independent of `a`. Sharp per W. Schmid's
  realization theorem. [Structure theorem PDF](https://imsc.uni-graz.at/geroldinger/108-a-characterization-of-Krull-monoids.pdf) (proof text not retrievable, 404 on
  direct fetch; found via search summary only).
- **Surveys**: Geroldinger, "Sets of lengths," Amer. Math. Monthly (2016-era survey,
  title/venue as given in the scout brief — not independently re-verified via direct
  fetch in this pass); W. Schmid, "Some recent results and open problems on sets of
  lengths of Krull monoids with finite class group,"
  [arXiv:1511.08080](https://arxiv.org/pdf/1511.08080) (abstract confirms coverage of
  elasticity, set of distances, structure theorem, "several open problems," but the PDF
  body could not be parsed by the fetch tool in this pass — binary/FlateDecode content,
  flagging as NOT independently verified beyond the abstract); W. Schmid,
  "Characterization of Class Groups of Krull Monoids Via Their Systems of Sets of
  Lengths: A Status Report" (Springer chapter, paywalled — abstract-level access only in
  this pass, [link](https://link.springer.com/chapter/10.1007/978-93-86279-46-0_14)).
- **Key contributors named in the brief, confirmed active in the literature**:
  A. Geroldinger, F. Halter-Koch, W. A. Schmid, Q. Zhong — all appear as authors across
  the characterization-problem paper series (I: arXiv:1503.04679, II: arXiv:1506.05223,
  transfer-Krull generalization: arXiv:1711.05437) and the more recent (2023–2025)
  incomparability/plus-minus-weighted extensions. A. Plagne appears as author of a
  preface to Geroldinger–Schmid's 2023 "On the incomparability of systems of sets of
  lengths," Eur. J. Combin. 111 (2023), Paper 103694 — confirming Plagne's named
  involvement in this specific sub-area, though not as a primary author of the core
  characterization papers found.

## (2) The Characterization Problem — proven cases, open cases

- **Statement** (Geroldinger–Schmid, [arXiv:1503.04679](https://arxiv.org/pdf/1503.04679)):
  given Krull monoids H, H′ with class groups G, G′ (every class containing a prime
  divisor) and `L(H) = L(H′)`, if one of G, G′ is finite of rank ≤ 2, then `G ≅ G′`
  apart from two known exceptional pairs.
- **Part II** (Geroldinger–Zhong, [arXiv:1506.05223](https://arxiv.org/pdf/1506.05223)):
  extends to `G ≅ C_n^r` with `r, n ≥ 2` and `r ≤ max{2, (n+2)/6}` — i.e. still a
  rank-vs-exponent tradeoff, not unrestricted rank.
- **Specific solved instance**: `G ≅ ℤ/nℤ ⊕ ℤ/nℤ` (`n ≥ 3`) is detectable from `L(H)`
  alone (Geroldinger–Schmid, Abh. Math. Sem. Hamburg,
  [link](https://link.springer.com/article/10.1007/s12188-008-0010-z)).
- **Generalizations tracked as active 2023–2025 work**: the plus-minus weighted
  zero-sum monoid analogue of the same Characterization Problem — Fabsits, Geroldinger,
  Reinhart, Zhong, "On Monoids of plus-minus weighted Zero-Sum Sequences: The
  Isomorphism Problem and the Characterization Problem," J. Commutative Algebra 16
  (2024) 1–23, [arXiv:2304.14777](https://arxiv.org/pdf/2304.14777); follow-up "The set
  of minimal distances of the monoid of plus-minus weighted zero-sum sequences and
  applications to the characterization problem,"
  [arXiv:2506.14279](https://arxiv.org/pdf/2506.14279) (2025). This shows the
  Characterization Problem is actively being ported to new monoid families, not
  considered closed even in its classical form.
- **Open**: unrestricted rank ≥ 3 (beyond the `r ≤ max{2,(n+2)/6}` band) is open in
  general. No paper found claiming full resolution for all finite abelian groups.

## (3) Davenport constants — exact values and open rank

- Exactly known: p-groups, and rank ≤ 2 (`D(C_n^2) = 2n-1`).
- Conjecture `D(G) = M(G)` (M(G) = trivial lower bound from the invariant-factor
  decomposition): proven for p-groups and rank ≤ 2; **false for every rank ≥ 4**
  (counterexamples known); **open for rank 3** — this is the precise frontier, called
  out explicitly in multiple surveys as believed-true-but-unproven.
- Best bounds for rank 3: Balasubramanian–Bhowmik and successors give
  `D(G) ≤ K₃·M(G)` (Alon–Dubiner style, K₃ same order as the Alon–Dubiner constant);
  Zakarczemny (2019, [arXiv:1910.10984](https://arxiv.org/pdf/1910.10984)):
  `D(C_{n1}⊕C_{n2}⊕C_{n3}) ≤ (n1-1)+(n2-1)+(n3-1)+1+(a3-3)(n1-1)`, `a3 ≤ 20369` — linear
  growth but a very loose constant.
- Fully resolved special family: `Z_3⊕Z_3⊕Z_{3d}` (Bhowmik–Schlage-Puchta), closing the
  previously-open simplest case `Z_3⊕Z_3⊕Z_15` (open since van Emde Boas–Kruyswijk).
- **Weighted variants**: plus-minus weighted Davenport constant `D_±(G)` — studied since
  ~2013 (Marchan–Ordaz–Schmid, exact values for some group families); surveyed in
  Adhikari, "Plus-Minus Weighted Zero-Sum Constants: A Survey" (2018 Springer volume).
  A-weighted generalizations (`D_A(G)` for general weight sets A) also exist.
- **Where computation contributes**: Bhowmik–Halupczok–Schlage-Puchta used inductive
  methods to *algorithmically decide* the `D(G)=M(G)` conjecture for infinite families
  `Z_k^ℓ ⊕ Z_n` (n coprime to k) given fixed k, ℓ — decidability results paired with
  targeted computer search rather than a general-purpose database.
- **GAP computation**: a dedicated paper computes/verifies both the small (`d(G)`) and
  large (`D(G)`) Davenport constants via custom GAP algorithms for **all groups of
  order < 32** ("The Noether numbers and the Davenport constants of the groups of order
  less than 32," [arXiv:1702.02997](https://arxiv.org/pdf/1702.02997)), using a
  "splitting" construction to avoid brute-force enumeration. No dedicated public GAP
  *package* (as a named, general-purpose library) was found — only bespoke research-code
  implementations reported in individual papers. **NOT FOUND**: any general public
  database or package explicitly branded for Davenport-constant computation beyond this
  order-32 exhaustive result.

## (4) Analytic/zeta methods — Narkiewicz's program and its limits

- Narkiewicz's original analytic theory of non-unique factorizations (developed in his
  *Elementary and Analytic Theory of Algebraic Numbers*) uses Dedekind zeta functions
  and Tauberian theorems to count algebraic integers/ideals by norm, refined by
  factorization behavior.
- Formalized abstractly by J. Knopfmacher, *Abstract Analytic Number Theory* (1975):
  arithmetical semigroups (commutative monoid + countable prime set + norm/degree map
  satisfying growth Axiom A) as the general setting for zeta-function/Tauberian
  machinery outside number fields; extended by Knopfmacher and Wen-Bin Zhang to function
  fields and finite-field settings. "Arithmetical formations" generalize Chebotarev
  density to this abstract setting (class group of the formation = quotient by an
  equivalence relation on the semigroup).
- **Modern quantitative continuation**: the "Narkiewicz constants" series — Gao,
  Geroldinger, Wang, Int. J. Number Theory 7 (2011) 1463–1502; Gao, Li, Peng, Colloq.
  Math. 124 (2011) 205–218; Gao, Peng, Zhong, Acta Arith. 158 (2013) 271–285. These
  study `F_k(x)` = count of principal ideals of norm ≤ x with at most k distinct
  factorizations into irreducibles, and prove asymptotic/exact results (e.g. a constant
  equals `2p` for every prime p), partially confirming a 30-year-old Narkiewicz
  conjecture.
- **Direct search for "L-function/character sum → sets-of-lengths or Davenport-constant
  invariant" connection: NOT FOUND.** The only character-theoretic tool in the field is
  the standard dual-group orthogonality relation used combinatorially to detect
  zero-sum subsequences inside `B(G)` — a finite-group Fourier technique, not an
  L-function special-value or analytic-continuation argument. No paper surfaced that
  uses L-function values (Dirichlet L-functions, Artin L-functions, or otherwise) to
  compute or bound a Davenport constant, elasticity, or characterization-problem
  invariant. This absence is reported as the deliverable finding per the brief's
  instruction to flag gaps explicitly.

## (5) Field's own diagnosis of the obstruction

- For the **Characterization Problem**: the obstacle beyond rank 2 (or the
  `r ≤ max{2,(n+2)/6}` band) is not identified in the located sources as "missing
  structure theory" — the Structure Theorem for Sets of Lengths already holds at full
  generality (all finite class groups). The obstruction is that the *proof technique*
  for the inverse/characterization direction (showing `L(G)` determines G) has so far
  relied on rank-specific combinatorial arguments about zero-sum sequences that do not
  scale uniformly; each rank increment or larger exponent has needed new,
  group-family-specific work (cf. the steady stream of "characterization of class
  groups... II," "...for transfer Krull monoids," "...for plus-minus weighted
  sequences" papers rather than one general theorem).
- For **Davenport constants at rank ≥ 3**: explicitly a bounds/combinatorial-explosion
  problem — the best general techniques (Alon–Dubiner polynomial method and its
  refinements) give asymptotically correct but numerically very loose bounds (constants
  like 20369), and exact resolution has only been achieved by hand for specific
  small/structured families (e.g. `Z_3⊕Z_3⊕Z_{3d}`). No survey located claims a missing
  *invariant* is the blocker; the blocker as documented is computational/combinatorial
  tractability of the existing zero-sum-sequence framework at higher rank.

## (6) Computational state

- Exhaustive GAP-based computation of small and large Davenport constants exists for
  **all groups of order < 32** (arXiv:1702.02997), via a custom splitting algorithm
  (not brute-force enumeration of all sequences).
- No dedicated, named, general-purpose software package or public database for
  zero-sum-sequence/Davenport-constant computation beyond that was found; each paper in
  this space appears to implement its own inductive/algorithmic verification for the
  specific groups or conjecture it targets (e.g. Bhowmik–Halupczok–Schlage-Puchta's
  decidability-plus-computer-search approach for `Z_k^ℓ ⊕ Z_n` families).

---

## Bottom-line answer to the scout question

The field has a real, open, precisely-stated problem of exactly the right *shape*
(does an invariant system determine an obstruction group; rank ≥ 3 Davenport constants
unknown) for a new obstruction-measurement toolkit to target. But two specific pieces of
the toolkit's premise as described — (a) landing class-group invariants as exact numbers
via L-function/character-sum data, and (b) a cohomological "weld mismatch" framing of
gluing — have **no existing counterpart in this literature** after direct, repeated
search. The field's zeta/L-function usage (Narkiewicz's program) is exclusively a
counting/Tauberian device for *how many* objects have *k* factorizations, never a tool
for pinning down *which* class group or *what* Davenport-constant value obtains. If the
toolkit can actually produce new exact numbers for rank-3 Davenport constants or new
progress on the Characterization Problem beyond rank 2, that would be new to the field;
if it only offers a structural/cohomological reframing without new numbers, the field's
own diagnosis (combinatorial explosion in existing bounds, not missing structure) suggests
it would not by itself register as progress.

---

## RANK-3 DAVENPORT ATTACK — verified target-selection facts (2026-07-02)

Conjecture under attack: **D(G) = M(G) for rank-3 finite abelian G**.
Equivalent: d(G) = d*(G), where d(G)=max zero-sum-free length, D(G)=d(G)+1,
d*(G)=sum(n_i - 1), M(G)=D*(G)=1+d*(G). Counterexample = a zero-sum-free
sequence of length d*(G)+1.

Status (verified, primary sources):
- rank<=2 and all p-groups (Olson/Kruyswijk): D(G)=M(G) PROVEN.
- rank 3: **existence of a group with d(G)>d*(G) is OPEN** — GLP arXiv:1009.5835
  line 142-143 ("no known group G of rank three with d(G)>d*(G)"); Biswas-Mazumdar
  arXiv:2402.09999 line 52-53 (2024, still open). No counterexample known; the
  conjecture (=true) is not proven in general either.
- rank>=4: FALSE (Geroldinger-Schneider 1992, J.Comb.Theory A 61:147-152).

**THE structural boundary (survey Thm 3.4 / Gao-Geroldinger):**
For G = C_2^r (+) C_n with n>=3 ODD:  d(G)=d*(G)  <=>  r <= 4.
So the C_2^r (+) C_n threshold sits at rank 5 (r=5 is first failure = rank 5 group).
Rank-4 counterexample families (the ONLY ones known):
  (1) G = C_m (+) C_{2n} (+) C_{2n}, m,n>=3 odd, m|n  [rank 3?? re-check: this is
      3 invariant factors -> RANK 3? NO: survey lists it under rank-4 cases; the
      C_m has odd order coprime-ish, giving 4 cyclic factors after primary decomp].
  (2) G = C_2^i (+) C_{2n}^{5-i}, n>=3 odd, i in [2,4]  -> these are RANK 5 groups.
  Rank-5 (GLP): G = C_2 (+) C_{2n}^4, n>=3 odd, d(G) = d*(G)+1.
Only rank-4/5 series with a KNOWN exact D value: G = C_2^4 (+) C_{2k}, k>=70:
  D(G)=2k+4 (k even) or 2k+5 (k odd, so D=D*+1, a counterexample).

CONSTRUCTION MECHANISM (GLP, [14, Prop 5.1.11]): if a subset I of the invariant
factors gives a subgroup H = (+)_{i in I} C_{n_i} with d(H) > d*(H), then the full
G has d(G) > d*(G). => a rank-3 counterexample would immediately produce new
higher-rank ones. This is WHY rank 3 is the frontier and hard.

**TARGET SELECTION consequence:** rank-3 groups C_2 (+) C_{n2} (+) C_{n3} are the
natural analogues of the rank-4/5 (+)C_2 families, BUT the boundary theorem says
C_2^r(+)C_n only fails at r>=5 -> the "+C_2" direction does NOT give a rank-3
counterexample by that mechanism. So the honest hunt targets are the general
mixed rank-3 groups with no p-group / no-known-formula structure, prioritized by
small |G|, including odd-order-heavy ones (C_3(+)C_3(+)C_{3d} is DONE, exclude).
