# Rung 3 scout: Darmon–Rotger / Darmon–Lauder–Rotger extraction

Sources cached in `tmp/rung3_pdfs/` (author-hosted PDFs, verified against real page counts —
do NOT reuse the arXiv IDs 1206.5691 / 1607.05204 tried first, those resolve to unrelated
short documents on arXiv and were discarded):

| File | Paper | Pages |
|---|---|---|
| `DR1_diagonal_gross_zagier.pdf` (+`.txt`) | Darmon–Rotger, *Diagonal cycles and Euler systems I: a p-adic Gross–Zagier formula*, Ann. Sci. ENS 47 (2014), 779–832. Source: `math.mcgill.ca/darmon/pub/Articles/Research/62.DR-Diagonal1/paper.pdf` | 47 |
| `DR2_HWA_BSD.pdf` (+`.txt`) | Darmon–Rotger, *Diagonal cycles and Euler systems II: BSD for Hasse-Weil-Artin L-functions*, JAMS 30 (2017), 601–672. Source: `web.mat.upc.edu/victor.rotger/docs/DR2.pdf` | 54 |
| `DLR_stark_points.pdf` (+`.txt`) | Darmon–Lauder–Rotger, *Stark points and p-adic iterated integrals attached to modular forms of weight one*, Forum Math. Pi 3 (2015), e8. Source: `people.maths.ox.ac.uk/lauder/papers/DLR.pdf` | 61 |
| `DLR2_gross_stark_units.pdf` (+`.txt`) | Darmon–Lauder–Rotger, *Gross-Stark units and p-adic iterated integrals attached to modular forms of weight one*, Ann. Math. Québec (2016). Source: `people.maths.ox.ac.uk/lauder/papers/DLR2b.pdf` | 27 |
| `lauder_efficient_rankin_padic.pdf` (+`.txt`) | Lauder, *Efficient computation of Rankin p-adic L-functions*, arXiv:1310.4421 | 19 |
| `fornea_gehrmann_plectic_stark_heegner.pdf` (+`.txt`) | Fornea–Gehrmann, *Plectic Stark-Heegner points*, arXiv:2104.12575 (Adv. Math. 414, 2023) | 31 |
| `fornea_gehrmann_polyquadratic.pdf` (+`.txt`) | Fornea–Gehrmann, *On the algebraicity of polyquadratic plectic points*, arXiv:2203.15998 (IMRN 2023) | 17 |
| `rivero_rotger_beilinson_flach.pdf` (+`.txt`) | Rivero–Rotger, *Beilinson-Flach elements, Stark units and p-adic iterated integrals*, arXiv:1806.10022 (Forum Math. 31, 2019) — downloaded but NOT read in this pass; cache only |

All `pdftotext -layout` conversions succeeded; use the `.txt` files for `grep`/line-numbered
lookup (line numbers below refer to these).

---

## 0. HOUSE COUNTERPARTS — reading DR/DLR against our own machinery

Framing note per the owner's directive: the target instrument is built FROM the house
codebase, with the DR/DLR formulas supplying the objects to compute and cross-check — not a
port of Lauder's pipeline. Each object below is paired with what it must interface with on our
side. House files grounded by direct read in this pass: `RequestProject/ClockStructure.lean`,
`RequestProject/BSDClocks.lean`, `tmp/jet_census.py`, `tmp/sha_unknown.py`.

**The house already names the target BSD statement DR/DLR are chasing.**
`RequestProject/BSDClocks.lean:197`, `EveryCentralJetHasSource (analyticOrder sourceRank : ℕ) :
Prop := analyticOrder = sourceRank` — "the order of central vanishing equals the number of
independent source directions." This is literally `r_an(E,ρ) = r(E,ρ)` from DR2/DLR (their
equation (1) in both papers, DR2_HWA_BSD.txt:41-45, DLR_stark_points.txt:71-74), stated as an
open `Prop`, never assumed — same posture the house holds toward GRH-strength statements per
CLAUDE.md. DR2's Theorem A proves an ISLAND of it (`ran=0 ⟹ r=0`, one direction, one rank);
Theorem D proves ANOTHER island (`ran≥2` with a p-adic non-vanishing hypothesis ⟹ `r≥2` via
two independent Selmer classes). **Read the whole DR/DLR/Fornea-Gehrmann corpus as a sequence
of partial certificates of `EveryCentralJetHasSource` at specific (analyticOrder, sourceRank)
pairs, obtained by a construction orthogonal to ours** (trace-down-a-tower of algebraic cycles,
vs. our direct measurement of the jet/regulator/obstruction identity). Same target, different
lever — worth stating exactly that way in any writeup, not as "weaker than" or "stronger than."

**Their p-adic logarithms of global points ↔ our canonical-height/jet instruments.**
`jet_census.py` computes `Reg = det(canonical height-pairing matrix on E(Q)/tors)` (the
Néron-Tate Gram determinant, `regulator()` in that file) and licenses it via
`BSDClocks.lean:181` `regulator_pos` (`H.PosDef → 0 < H.det`) — i.e. our regulator is an
ARCHIMEDEAN height pairing determinant. DLR's regulator `R_{g_α}(E,ρ_gh)` (Conjecture ES,
DLR_stark_points.txt:314-318) is the SAME kind of object one field up: a determinant of
`log_{E,p}` (p-adic formal-group logarithm) pairings instead of archimedean canonical heights,
built from a basis of `Hom_{G_Q}(V_ρ, E(H)_L)` instead of a basis of `E(Q)/tors`. The house
does not yet have a p-adic canonical height / p-adic regulator instrument — `jet_census.py`'s
`regulator()` and `canonical_height_naive`/`canonical_height_shifted` are the archimedean
analogue and the natural scaffold to extend: a house p-adic regulator function would take the
SAME shape (Gram determinant of a height pairing) but with `log_{E,p}` in place of the real
Néron-Tate pairing, over a basis of points defined over the Artin-representation field `H`
rather than over `Q`. `regulator_pos`/`regulator_ne_zero` (positive-definiteness ⟹ nonvanishing)
is exactly the well-posedness fact DLR needs for their regulator determinant to be meaningful,
but DLR's p-adic pairing is NOT known to be positive-definite in the same sense (it's valued in
`C_p`, no natural order) — this is a genuine gap, not a restatement: **the house's
`regulator_pos` proof technique (Gram-matrix positive-definiteness) does not transfer to the
p-adic regulator without a p-adic substitute for positive-definiteness**, flag this explicitly
if building a p-adic regulator instrument — nonvanishing there is currently an ANALYTIC
hypothesis to be numerically checked (their "for some choice of test vectors" clause), not a
theorem, in every example read above.

`sha_unknown.py` is the closer cousin: it is a first-determination-AT-SCALE instrument (goes
past tabulated LMFDB range using self-contained, frozen, gated machinery) with an independent
theorem-backed exact cross-check (Tunnell's integer) pre-committed BEFORE any Sha claim. DLR's
program is exactly this shape one level up: use a self-contained p-adic-analytic computation
(the iterated integral, computable from q-expansions alone, no L-function library) to predict
a global-point regulator, and cross-check it against an independently-obtained algebraic answer
(the points found by classical descent). **The house's discipline of "theorem-backed exact
cross-check, pre-committed, gates the claim" (Tunnell in `sha_unknown.py`) is the right frame
for how a DR/DLR-based instrument should treat its own regulator predictions**: never report a
p-adic regulator match as a "new" rank-2 point unless an independent classical-descent
computation (Magma-equivalent) already pins the point down — this is in fact what DLR
themselves do (see the normalization-trap item 5 below: global side is always found first by
descent in their own examples), so the house's existing discipline and DLR's actual practice
already agree; make that agreement explicit rather than importing DLR's aspirational
"constructive alternative to BSD" framing (DLR_stark_points.txt:48-52) uncritically.

**Their iterated-integral ratio identity ↔ our exact-landing discipline.**
Conjecture ES's content (DLR_stark_points.txt:352, `∫f̆·h̆ = det(R_{g_α}) / log_p(u_{g_α})`) is
an equality between two independently-computable p-adic numbers, checked to N digits of
precision in every worked example (20-30 digits throughout §3-§5). This is structurally
IDENTICAL to the house's `distinguishedPointLaw` (`BSDClocks.lean` via `ClockStructure.lean:138`,
`value = period * reg * obstruction / torsion`) checked via `integer_landing_unique`
(`ClockStructure.lean:156-166`: two integers each within 1/2 of the same real number are equal)
and its BSD-specific form `jet_measurement_sound` (`BSDClocks.lean:163-167`, identical shape,
specialized to a `GeneralizedCohomology.DistinguishedPoint`). The house's discipline is:
**the landing is an IDENTIFICATION only when the precision beats the half-integer margin** —
DLR's practice of quoting 20-30 exact matching digits mod `p^{20..30}` is doing the same job
informally but for a general p-adic number (not an a priori integer), so `integer_landing_unique`
does NOT directly apply to their setting as stated (there is no integer being landed on the
right-hand side of Conjecture ES — both sides are transcendental p-adic numbers, and the
"landing" is agreement of a power series to a stated p-adic precision, i.e. `x ≡ y mod p^k` for
large stated `k`, not `|x - o| < 1/2` for integer `o`). **If a house instrument re-does one of
these identities, the honest license to reach for is a generalization of
`integer_landing_unique` to "two p-adic-precision-bounded reals with matching digits to
precision `p^{-k}` for `k` large relative to accumulated error are equal" — this generalization
does not yet exist in `ClockStructure.lean` and would need to be stated and proved (or the
p-adic precision loss bookkeeping from Lauder's algorithm, section 3 below, would need to be
formalized as an explicit error bound before any such lemma could license a specific numerical
match).** This is a genuine, nameable gap between the house's integer-landing machinery and
what a DR/DLR instrument's landings actually look like — worth flagging to whoever designs the
formal license for this instrument, rather than silently reusing `integer_landing_unique`'s name
for a different kind of closeness statement.

Directly relevant to the in-flight build (task #40, "RHS assembly and anchor gate," matching
DLR's 26b/52b eq. 79-80 to 20 digits): the anchor gate there is checking p-adic-precision
agreement of a REAL/RATIONAL-valued determinant against a power series, not an integer landing
— so its formal license, if one is written, should NOT cite `integer_landing_unique` directly;
it needs the generalization described above (or an explicit, separately-argued error bound on
each of the two sides being compared, sufficient to conclude equality from N-digit agreement
without invoking a not-yet-existing lemma).

**Their trace-down-the-tower constructions ↔ the house harmonization arc (capitulation/Iwasawa
pattern).** DR1's diagonal cycle `Δ_{f,g,h}` lives in the triple product of Kuga-Sato varieties
(a variety fibered over the modular curve, strictly "up a dimension" from the curve itself), and
its p-adic Abel-Jacobi image is what supplies the source for the central jet (Theorem 1.3). DR2's
whole point is to interpolate this construction IN A HIDA FAMILY (varying `p`-adically over
weight space) and then specialize back down to weight `(2,1,1)` to read off a Selmer class on
the actual elliptic curve `E/Q` (DR2_HWA_BSD.txt:299-345, the `κ(f,g,h) ∈ H¹(Q,V_{f,g,h})`
construction, explicitly described as "falling somewhat short" of the ideal fully-interpolated
class). This up-then-down movement — construct in a bigger ambient family/variety, then trace
or specialize down to the object of actual interest — is EXACTLY the shape of the house's
capitulation/Iwasawa pattern in the harmonization arc (per team-lead's framing). CONFIRMED
by direct grep of every file in `RequestProject/` (69 files, full listing checked): no theorem
or file literally named "capitulation" or "Iwasawa" exists yet in the house Lean codebase — this
pattern is not yet formalized as a standalone lemma. The nearest existing house anchor is
`BSDClocks.lean:169-171`'s own cross-reference: `EveryCentralJetHasSource` is explicitly called
"the mirror of `SourceHolonomy.Exhaustive`, at the center" — i.e. `RequestProject/SourceHolonomy
.lean` is the house's OTHER named source-completeness statement (at the critical-line weld
rather than the BSD center), and is the most likely conceptual home for a general "source lives
one dimension up, comes down by trace" lemma if/when one is written. `GeneralizedCohomology.lean`
(imports `DistinguishedPoint` and is where `ClockStructure.integer_landing_unique` gets used,
per `GeneralizedCohomology.lean:77`) is the other natural candidate. Treat "capitulation/Iwasawa
pattern" as a NAMING the team lead is introducing for this session, to be formalized fresh
against `SourceHolonomy.lean` / `GeneralizedCohomology.lean`, not as a lemma that already exists
under another name — a targeted read of those two files is the correct next step before writing
new Lean, not a further grep.
The A4/S4/A5 exotic constructions in DLR §5 (section 4 below) are the cleanest instance of this
pattern rendered fully explicit: `r(E,Ad_g) = rank(E(M)) − rank(E(Q))`, i.e. the source lives
"up the tower" at the quartic/sextic field `M` and comes down to `Q` by an EXACT trace/induction
identity (`Ad_g = Ind_M^{G_Q} sgn − sgn` etc., DLR_stark_points.txt:2634-2641) — this is a fully
elementary, non-p-adic, PROVEN piece of group theory (Artin formalism for the rank, not just the
L-function) sitting underneath the conjectural p-adic regulator identity. If the house's
capitulation/Iwasawa pattern has a general "rank up the tower minus rank down the tower equals
rank of the induced-minus-trivial piece" lemma, THIS is the DR/DLR object it should be tested
against first — it is elementary enough to be a clean unit test before touching any p-adic
machinery.

**Their ordinary projections ↔ our smooth-entry/never-clip method laws.**
`jet_census.py`'s stated house law (line 29-32 of that file) is "smooth entry (the
incomplete-Gamma kernel decays past machine precision); tier everything; integer landing only
within 1/2 with a stated margin" — i.e. never truncate a series or projector in a way that
introduces an uncontrolled discontinuity; every truncation must be justified by an explicit
decay bound. Hida's ordinary projector `e_ord = lim U_p^{n!}` and Lauder's finite-matrix
truncation of it (section 3 below: the Katz-basis truncation to `ℓ` elements is valid only
because the target form is provably `p/(p+1)`-overconvergent, so its Katz coefficients decay
p-adically and vanish mod `p^m` past the first `ℓ` terms — lauder_efficient_rankin_padic.txt:
354-359) is STRUCTURALLY the same discipline: a projector/limit is replaced by a finite
computation only after proving the tail is provably below the target precision, never by ad hoc
truncation. **This is a real match, not just an analogy** — a house implementation of the
ordinary-projection step should hold itself to the same "prove the decay bound before truncating"
standard already codified in `jet_census.py`'s docstring, and Lauder's overconvergence argument
(the `U_p`-once "improve overconvergence" pre-step, lauder_efficient_rankin_padic.txt:316-319)
is the direct model for how to state that decay bound rigorously in this specific setting.

---

## 1. DARMON–ROTGER I & II: what is actually PROVEN

### DR1 (2014) — the p-adic Gross-Zagier formula for diagonal cycles

**Setting.** `f ∈ S_k(N_f,χ_f)`, `g ∈ S_ℓ(N_g,χ_g)`, `h ∈ S_m(N_h,χ_h)` normalized eigenforms,
`χ_f χ_g χ_h = 1`. Weight triple `(k,ℓ,m)` **balanced** iff largest weight < sum of other two.
Hypothesis H: local root numbers `ε_v = +1` at all finite `v | N` (DR1_diagonal_gross_zagier.txt:90-102).
Under H, `ε = -1` exactly when balanced, forcing `L(f,g,h,s)` to vanish to odd order at the
center `c=(k+ℓ+m-2)/2` in the balanced case.

**Theorem 1.3** (DR1_diagonal_gross_zagier.txt:252-271), the proven result:
for `(x,y,z) ∈ Σ_bal` (classical balanced points of three Hida families `f,g,h`),
```
L_p^f(f,g,h)(x,y,z) = (-1)^t · E(f,g,h) / (t! · E_0(f) E_1(f)) · AJ_p(Δ)(η_f^{u-r} ⊗ ω_g ⊗ ω_h)
```
where `t := (ℓ+m-k)/2 ≥ 0`, `Δ = Δ_{k,ℓ,m}` is the generalized Gross-Kudla-Schoen diagonal
cycle in `E^{k-2}×E^{ℓ-2}×E^{m-2}` (Kuga-Sato triple product), `AJ_p` is the p-adic Abel-Jacobi
map, and
```
E(f,g,h) = (1-β_f α_g α_h p^{-c})(1-β_f α_g β_h p^{-c})(1-β_f β_g α_h p^{-c})(1-β_f β_g β_h p^{-c})
E_0(f) = 1 - β_f² χ_f^{-1}(p) p^{1-k}
E_1(f) = 1 - β_f² χ_f^{-1}(p) p^{-k}
```
(`α_f,β_f` = roots of `x² - a_p(f)x + χ_f(p)p^{k-1}`, `α_f` the p-adic unit). This is an
UNCONDITIONAL THEOREM — it relates a p-adic Abel–Jacobi image of an actual algebraic cycle to
a Garrett-Rankin p-adic L-value outside the classical interpolation range. No GRH/RH input;
not circular (the cycle is constructed independently of the L-value it's compared to).

**Direct BSD-adjacent corollary stated in DR1's intro** (DR1_diagonal_gross_zagier.txt:311-316,
labeled "I. Euler system of diagonal cycles"):
```
L(E, ρ1 ⊗ ρ2, 1) ≠ 0  ⟹  Hom_{G_Q}(ρ1 ⊗ ρ2, E(Q̄)⊗C) = 0
```
for E/Q elliptic, ρ1,ρ2 odd irreducible 2-dim Artin reps with `ρ1⊗ρ2` self-dual (det=1). This
is proved in the sequel DR2, not DR1 itself — DR1 only states it as the target application.

### DR2 (2017) — the actual BSD-rank statements: PROVEN Theorems A, B, C, D

Setting: `f∈S_2(N_f)` (weight 2, gives E/Q), `g∈S_1(N_g,χ)`, `h∈S_1(N_h,χ⁻¹)` (weight 1,
give Artin reps `ρ1,ρ2`), `ρ = ρ1⊗ρ2`, `L(E,ρ,s) = L(f,g,h,s)` (Garrett triple product).
Standing assumption: `gcd(N_f, N_g N_h)=1` ⟹ all local signs +1 ⟹ global sign +1 ⟹
`r_an(E,ρ)` even (DR2_HWA_BSD.txt:63-66).

**Theorem A** (rank 0, PROVEN, DR2_HWA_BSD.txt:68):
```
L(E,ρ,1) ≠ 0  ⟹  E(H)_ρ = 0
```
where `E(H)_ρ := Hom_{G_Q}(V_ρ, E(H)⊗L)`. Corollaries: BSD-rank-0 over ring class fields of
real AND imaginary quadratic fields (Corollary A1, DR2_HWA_BSD.txt:76), and over non-real
quintic `A5`-fields (Corollary A2, DR2_HWA_BSD.txt:96-98) — **this real-quadratic / quintic
reach is the point**: it extends beyond Heegner-point / Gross-Zagier territory because the
proof makes NO use of CM points (DR2_HWA_BSD.txt:82).

**Theorem B** (the rank-≥2 mechanism, PROVEN, DR2_HWA_BSD.txt:253):
```
If L(E,ρ,1) = 0  AND  L_p^{g_α}(f̆,ğ*,h̆) ≠ 0 for some test vectors,
then  dim_{L_p} Sel_p(E,ρ) ≥ 2.
```
`L_p^{g_α}` is the Garrett-Hida p-adic L-function of the triple `(f,g,h)` of weights `(2,1,1)`,
evaluated at the point `(x_0,y_0,z_0)` of weight `(2,1,1)` which lies OUTSIDE its own region
of classical interpolation (interpolation range needs `ℓ ≥ k+m`; here `ℓ=1 < 2+1=k+m`) — exact
analogue of DR1's mechanism, one level down in weight. Defined explicitly at
DR2_HWA_BSD.txt:229: `L_p^{g_α}(f̆,ğ*,h̆) := ğ*(e_ord(d^{-1}f̆^{[p]} × h̆_α))`.

**Theorem C** (the crystalline-iff-vanishing hinge, PROVEN, DR2_HWA_BSD.txt:357):
```
The generalized Kato class κ(f,g_α,h_α) is crystalline at p  ⟺  L(E,ρ,1) = 0.
```
This is the actual engine: when `L(E,ρ,1)≠0` the class is NOT crystalline, forcing (via
Poitou-Tate) triviality of `E(H)_ρ` — proving Theorem A. When `L(E,ρ,1)=0`, four "generalized
Kato classes" `κ(f,g_α,h_α), κ(f,g_α,h_β), κ(f,g_β,h_α), κ(f,g_β,h_β) ∈ H¹(Q,V_{fgh}(N))`
(DR2_HWA_BSD.txt:343) land in the Selmer group and become candidates for rank-2 sources.

**Theorem D** (PROVEN — the exact rank-2 linear-independence statement, DR2_HWA_BSD.txt:387-389):
```
If L(E,ρ,1)=0 and L_p^{g_α}(f̆,ğ*,h̆) ≠ 0 for some test vectors, there exist G_Q-equivariant
projections j_α, j_β : V_{fgh}(N) → V_p(E)⊗V_ρ such that the classes
  κ_αα = j_α(κ(f,g_α,h_α))   and   κ_αβ = j_β(κ(f,g_α,h_β))
are LINEARLY INDEPENDENT in Sel_p(E,ρ).
```
This is the rank-2 analogue of Gross-Zagier's single Heegner point: **two** canonical Selmer
classes, constructed unconditionally (given the p-adic L-value non-vanishing hypothesis, which
is checkable), proved independent. Theorem D ⟹ Theorem B directly.

**What is explicitly NOT proven / left conjectural in DR2:**
- Theorem D gives Selmer classes, not Mordell-Weil points — the conjectural expression of
  `καα, καβ` as explicit p-adic combinations of GLOBAL POINTS is exactly the content handed
  to [DLR] and [DR15] (DR2_HWA_BSD.txt:262-267). This is precisely the bridge to Rung 3.
- Finiteness of the Selmer group / Sha is NOT obtained by this method (DR2_HWA_BSD.txt:368-370)
  — contrast with Kato (Beilinson elements) and Lei-Loeffler-Zerbes (Beilinson-Flach elements)
  where finiteness IS known.
- The `ρ = 1 ⊕ Ad⁰(ρ_g)` "adjoint" scenario (g,h dual to each other): a nontrivial class in
  `Sel_p(E/Q)` is expected to force `rank E(Q) ≥ 2` but ONLY under the further hypothesis that
  Ш(E/Q) is finite (DR2_HWA_BSD.txt:400-405) — flagged explicitly as non-trivial/open.
- Comparison to Skinner-Urban's Theorem B (also proves Sel rank ≥2 for even order ≥2 vanishing):
  "little overlap... very different methods" (DR2_HWA_BSD.txt:268-273) — SU needs no auxiliary
  p-adic-L nonvanishing hypothesis but applies to a different representation class.

---

## 2. DARMON–LAUDER–ROTGER: the Elliptic Stark Conjecture — exact formula

### Setup and hypotheses (DLR_stark_points.txt:140-260)

`ρ_gh := ρ_g ⊗ ρ_h` (both odd 2-dim Artin, self-dual: `χ:=det(ρ_g)⁻¹=det(ρ_h)`).
- **Hypothesis A**: local root numbers all +1 ⟹ `L(E,ρ_gh,s)` vanishes to even order at s=1.
- **Hypothesis B**: `L(E,ρ_gh,1)=0` (so order ≥ 2 given A).
- **Hypothesis C** (classicality of `g_α`): the natural inclusion
  `M_1(Np,χ)_{C_p}[g_α*] ↪ S_1^{oc,ord}(N,χ)[[g_α*]]` is an isomorphism — this is the technical
  substitute for Coleman's classicality theorem at weight 1, and it is explicitly flagged: for g
  a REGULAR cusp form (`α_g≠β_g`) it usually holds by Cho-Vatsal / Bellaïche-Dimitrov criteria;
  for g IRREGULAR cusp form it is NOT expected to hold at all.

### The p-adic iterated integral (the computable object)

```
∫_γ̆ f̆·h̆ := γ̆(e_{g_α*} e_ord(F̆ · h̆))     [DLR_stark_points.txt:279]
```
where `F̆ = d^{-1}f̆` is the overconvergent primitive of `f̆` (Serre operator `d=q d/dq` inverted),
`e_ord` Hida's ordinary projector, `e_{g_α*}` projection onto the `g_α*` generalized eigenspace.
This is `I_p^0 : S_2(Np)_L[f] × M_1(Np,χ)_L^∨[g_α] × M_1(Np,χ)_L[h] → C_p` (eq. 6).

### Conjecture ES (Elliptic Stark Conjecture) — exact statement (DLR_stark_points.txt:345-357)

Assume A, B, C (so `r_an(E,ρ_gh) ≥ 2`). If `r(E,ρ_gh) > 2` the trilinear form `I_p^0` is
identically zero. **Otherwise** there exist test vectors with
```
∫_γ̆ f̆·h̆  =  det(R_{g_α}(E,ρ_gh)) / log_p(u_{g_α})
```
— **THE CENTRAL FORMULA.** Numerator: determinant of the 2×2 "regulator matrix"
`R_{g_α}(E,ρ_gh) = [[log_{E,p}(Φ1(v1)), log_{E,p}(Φ1(v2))],[log_{E,p}(Φ2(v1)), log_{E,p}(Φ2(v2))]]`
built from a basis `(Φ1,Φ2)` of `Hom_{G_Q}(V_gh, E(H)_L)` and a `σ_p`-eigenbasis `(v1,v2)` of
the canonical 2-dim subspace `V_gh^{g_α} := V_g^{α_g} ⊗ V_h`. Denominator: `log_p` of a
**Gross-Stark unit** `u_{g_α} ∈ (O_{H_g}[1/p]^×)_L^{Ad_g}`, `H_g` = field cut out by the
3-dim adjoint `Ad_g = hom⁰(V_g,V_g)`, pinned down (up to scaling) by `σ_p(u_{g_α})=(α_g/β_g)u_{g_α}`
when `α_g/β_g ≠ ±1` (DLR_stark_points.txt:330-338).

**Rank (1,1) simplified case** (DLR_stark_points.txt:374-397): when `ρ_gh = ρ1⊕ρ2` with
`r(E,ρ1)=r(E,ρ2)=1` and the regulator is "factorisable" (frobenius eigenvalue condition),
```
∫_γ̆ f̆·h̆ = log_{E,p}(P1) · log_{E,p}(P2) / log_p(u_{g_α})
```
with `P1,P2` uniquely-determined (up to L×) global points satisfying `σ_p P1=α_gα_h P1`,
`σ_p P2 = α_gβ_h P2`. **This is the operationally central formula** — a ratio of two point-
logarithms and a unit-logarithm, all independently computable, equated to a p-adic iterated
integral computable from q-expansions alone.

### What is PROVEN vs CONJECTURAL (exact scope)

- **PROVEN**: Conjecture ES when g,h are BOTH binary theta series of a common imaginary
  quadratic field K in which p SPLITS, subject to a Heegner hypothesis (Theorem in §3.2,
  referenced at DLR_stark_points.txt:419-429). Proof route: p-adic Gross-Zagier of Bertolini-
  Darmon-Prasanna (BDP) for Heegner points in terms of a Katz-style p-adic Rankin L-series,
  combined with DR1's iterated-integral/Garrett-Hida relation, plus a comparison-of-periods
  argument that surfaces an unexpected appearance of Katz's 2-variable p-adic L-function. The
  Stark unit `u_{g_α}` becomes an honest elliptic unit in this proven case.
- Everything else (p inert in K; K real quadratic / Stark-Heegner points; A4/S4/A5 exotic;
  cyclotomic/Eisenstein settings) is CONJECTURAL, backed only by high-precision numerics
  (20–30 digits of p-adic precision, quoted per-example below).
- The paper explicitly frames itself as offering "a more constructive alternative to BSD" since
  it yields POINTS not just heights (DLR_stark_points.txt:48-52) — this is their own stated
  motivation, worth noting as their positioning, not a claim we should import verbatim.

### Rank-2 numerical examples (exact anchors — genuine analytic-rank-2 double zeros)

**Example 3.13** (DLR_stark_points.txt:2073-2121): `E: y²+xy+y = x³-7x+5`, conductor 57,
Cremona label **57b**. `K=Q(√-23)`, class number 3, χ conductor 23. `g` = cubic theta series
on `S_1(23,χ)`, `h` = Eisenstein series `E(1,χ)`. Decomposition `V_gg = V_ψg ⊕ L ⊕ L(χ)` with
`r(E,V_ψg)=2`, other summands rank 0 — a GENUINE rank-2 constituent. Mordell-Weil rank 2 over
cubic field `Q(a)`, `a³-a²+2a-1=0`, generators `P=(9a²-4a+17,-45a²+20a-80)`, `Q=(a²+3,2a²+2)`.
`H=Q(b)`, `b⁶-6b⁴+9b²+23=0`. `p=19`. Verified to 25 digits 19-adic precision:
```
∫f·g = [63ζ3+18 · logE,19(Pψg+)logE,19(Qψg-) - logE,19(Pψg-)logE,19(Qψg+)] / [2^6·19 · log_p(u_ψg-)]
```

**Example 3.14** (DLR_stark_points.txt:2129-2192): `E: y²+y=x³+x²+9x+1`, conductor 35,
Cremona label **35a**. `K=Q(√-23)` again, both primes of 35 INERT in K — first example with NO
Heegner point from a modular curve (needs a Shimura curve for indefinite quaternion algebra
ramified at 5,7 — points instead found by descent, not by computing the Shimura parametrization).
`p=5`. Rank breakdown `r(E,V_ψg)=r(E,L(χ))=1` (rank (1,1) setting, not pure rank 2), verified to
30 digits 5-adic precision:
```
∫f·g = 3·7·logE,5(PK)·logE,5(Pψg+) / (2·5·log_5(u⁻))
```

**Exotic tetrahedral (A4) rank-2 examples** (DLR_stark_points.txt:2919-2979) — TWO independent
curves confirming the SAME regulator formula, both genuinely rank 2 with `r(E)=0, r(E,Ad_g)=2`:
- **26b**: `E: y²+xy+y=x³-x²-3x+3`, conductor 26. `M=Q(w)`, `w⁴+7w²-2w+14=0` (disc `124²`,
  Gal(H/Q)≅A4 — same tetrahedral field as Example 5.4's rank-(1,1) case, level 124). Rank-2
  Mordell-Weil lattice generators `P,Q ∈ E(M)` given explicitly (rung3_pdfs, DLR_stark_points.txt
  :2925-2931). `p=13`. Verified to 20 digits 13-adic precision (eq. 79–80):
  ```
  ∫_{γ_gα} f·h = (ζ3·E_α/√3) · [logE,13(P1)logE,13(Qgα) - logE,13(Q1)logE,13(Pgα)] / log_p(u_gα)
  ```
- **52b**: `E: y²=x³+x-10`, conductor 52, same field M, same `p=13`, same formula shape
  (eq. 79-80 reused) — authors note algebraic constants for 26b and 52b are IDENTICAL because
  "both curves have non-split multiplicative reduction at 13" (DLR_stark_points.txt:2977-2979) —
  a genuine cross-curve check, not just internal consistency.

**Trivial-vanishing rank-2 control** (Example 5.5, DLR_stark_points.txt:2983-2993): `E: y²+xy=
x³-18x+31`, conductor 4811=17·283, label **4811a**. `h` octahedral (S4) weight-1 form level 283,
quadratic character, `g=h*`. Here `r(E/Q)=r_an(E/Q)=2` but `r_an(E,Ad_g)=0` — regulator matrix
has determinant 0 for a TRIVIAL reason (rank exhausted by the trivial summand, not Ad_g). All
associated iterated integrals verified to VANISH, `p=17`, 5 digits precision. Important negative
control: shows the machinery correctly predicts zero when the "extra" rank isn't in Ad_g.

**Independent CM-rank-5 check** (Example 3.11, DLR_stark_points.txt:1955-2067): `E: y²+xy+y=
x³+x²-2x`, conductor 79, label **79a**, `K=Q(√-79)` class number 5. Genuine Heegner-point-based
Mordell-Weil rank 5 (not rank 2), `p=29`. Included because it's the example that "first convinced
the authors the p-adic iterated integral had geometric meaning" via a self-consistency ratio
identity (eq. 65) discovered BEFORE they understood the denominator's transcendental factor
(DLR_stark_points.txt:2064-2067) — historically informative on how the conjecture was found.

---

## 3. COMPUTABILITY: the algorithmic pipeline

### Lauder's algorithm (arXiv:1310.4421, `lauder_efficient_rankin_padic.txt`)

**What it computes**: ordinary projections `e_ord(H)` of overconvergent p-adic modular forms,
specifically `H = d^{-(1+t)}(g^{[p]}) × h` (the non-classical form whose ordinary projection
gives the Rankin/Garrett triple-product p-adic L-value), IN POLYNOMIAL TIME in `N, p, m`
(m = desired p-adic precision) — improves on the prior exponential-time approach of naively
iterating the Atkin `U_p` operator on q-expansions (lauder_efficient_rankin_padic.txt:21-31,
336-340). Requires `p ≥ 5` and weight condition `k = ℓ-m+2` (DR1's balanced-weight condition
translated to ensure `H` is genuinely OVERCONVERGENT, not just nearly-overconvergent) —
lauder_efficient_rankin_padic.txt:96-121. Works equally well at weight 1 as at higher weight
(explicitly claimed, key for the DLR application) — line 27.

**Pipeline** (Algorithm 2.1, lauder_efficient_rankin_padic.txt:300-340), 7 steps:
1. Choose a **Katz basis** `{e_{i,s}}` for the space of `p/(p+1)`-overconvergent modular forms
   (built from `E_{p-1}` and classical modular forms — the Eisenstein-family trick named in the
   mission brief).
2-4. Precision bookkeeping (choose working precision `m' = m + ⌈(p+1)⌉` etc.).
5. **Atkin matrix**: compute the matrix `A` of `U_p` acting on the Katz basis truncated to `ℓ`
   elements, via q-expansions modulo `q^{ℓ'}`, by linear algebra mod `p^{m'}`.
6. **Two-stage projection**: (a) apply `U_p` once directly to `H`'s q-expansion to "improve
   overconvergence" by a factor of p (moves `H` from `1/(p+1)`- to `p/(p+1)`-overconvergent so
   the finite Katz-basis truncation becomes valid); (b) iterate the FINITE matrix `A` to a large
   power `r := (p^f-1)p^m` via fast exponentiation (f = residue degree needed for unit roots of
   the reverse characteristic polynomial of A) to project onto the ordinary subspace.
7. Read off the ordinary-subspace basis from the echelon form of `A^r`.

**Precision caveats (normalization traps)**: there is an unavoidable loss of `m'-m` digits of
precision converting `U_p(H)` to a Katz expansion (line 367); the algorithm ASSUMES the smallest
nonzero Newton-polygon slope `s_0` of `A`'s reverse characteristic polynomial satisfies
`⌈m/s_0⌉ ≤ (p^f-1)p^m` — justified only empirically ("smallest non-zero slope ever observed
is 1/2"), not proven in general (lines 382-386). Author flags TWO unanalyzed complexity aspects
of the full pipeline as "of minor practical importance, but difficult to analyse" (line 127) —
NOT FOUND explicitly which two, beyond the pointer to "Note 2.3 (1) and (3)" which is outside
the excerpted range; would need re-extraction if precision-loss bookkeeping becomes load-bearing.

**Direct BSD-rank-1 application already demonstrated** (lauder_efficient_rankin_padic.txt:129-146):
for f,g weight-2 rational newforms,
```
log_{E_f}(P_g) = 2 d_g · [E_0(g)E_1(g)/E(g,f,g)] · L_p(g,f,g)(2,2,2)
```
recovers an explicit rank-1 point `P_g ∈ E_f(Q)` ("Zhang point") from a pure q-expansion
computation — this is the k≥2 analogue (proven/implemented) of what DLR then push to weight
(2,1,1) conjecturally.

### From-scratch Python implementation requirements (synthesized from Lauder + DLR §1, §2)

1. **q-expansion arithmetic mod `(p^m, q^{ℓ'})`** for classical modular/Eisenstein series —
   standard, e.g. via Sage-style power series or a custom truncated-polynomial ring over `Z/p^m`.
2. **Katz basis construction**: need `E_{p-1}` (weight `p-1` Eisenstein series normalized to
   constant term 1) and a `Z_p`-basis `W_i(N,χ,Z_p)` of classical modular forms of controlled
   weight — this is the "Eisenstein family trick" alluded to in the mission brief; see
   lauder_efficient_rankin_padic.txt §2.1.1 (only the opening lines were extracted here — the
   full basis-construction recipe is NOT extracted in this pass and would need a second read of
   lines ~180-300 of that file for a literal implementation).
3. **Atkin/`U_p` matrix**: linear algebra mod `p^m` over the truncated Katz basis; fast matrix
   exponentiation `A^r` for `r = (p^f-1)p^m`.
4. **Weight-1 specifics (DLR, not in Lauder's paper directly)**: need the p-stabilizations
   `g_α, g_β` of a weight-1 form (roots of the Hecke polynomial `x²-a_p(g)x+χ⁻¹(p)`), the
   GENERALIZED eigenspace projector `e_{g_α*}` (not just the ordinary projector — Hypothesis C
   is precisely the statement that this generalized eigenspace is finite-dimensional and equals
   the classical space), and the overconvergent primitive `d^{-1}f̆` via term-by-term division
   of Fourier coefficients by `n` (excluding multiples of p) — this last step is elementary
   (DLR_stark_points.txt:213-221) but only valid because `f` (weight 2) already has `a_0=0`.
5. **Global-side objects** (points, units) are NOT computed by this algorithm at all — they are
   supplied independently (Magma descent, LMFDB / Cremona tables, explicit generator search) and
   then plugged into the conjectural identity as a CHECK, not a construction, in every example
   extracted above. The "constructive" framing of Conjecture ES (line 48-52) is aspirational:
   in practice the points were found FIRST by classical descent and the p-adic side computed
   SECOND to verify agreement — worth being honest about this reversal if building an instrument
   that claims to "construct" rank-2 points from the p-adic side alone.

**Precision/level/weight ranges actually demonstrated**: levels up to a few hundred (57, 35, 79,
124, 133, 4811 seen above), primes p up to ~29 in the examples read, precision 20-30 digits.
NOT FOUND: an explicit statement of the largest level/precision the authors' implementation
could handle before becoming impractical — would require reading Lauder §3 (illustrative
computations) in full, not done in this pass.

**Is code published?** NOT FOUND in the extracted text — no explicit URL or Magma package name
for the DLR/Lauder implementation appears in the introduction or algorithm section read here.
(The broader literature search surfaced Jan Vonk's "Computing overconvergent forms for small
primes" as an independent extension for p=2,3, but its code-availability was not checked either.)
Treat "is code published" as NOT FOUND, not as "no" — a targeted check of Lauder's or Rotger's
personal pages for a code repository would be a fast follow-up.

---

## 4. THE RANK-2 FACE: which constructions actually reach analytic-rank-2 single curves

### The Ad_g / exotic weight-one mechanism (DLR §5, the sharpest rank-2 lever)

When `g` is an EXOTIC weight-1 form (tetrahedral A4, octahedral S4, or icosahedral A5 projective
image) and `h = g*` its dual, `V_gh = L ⊕ Ad_g` splits off the trivial rep from the **3-dimensional
adjoint** `Ad_g`. Then:
```
r(E, Ad_g) = rank(E(M)) - rank(E(Q))     [A4 case, M = quartic field, DLR:2575-2576]
r(E, Ad_g) = dim E(M̃)_L^- - dim E(K)^-  [S4 case, DLR:2639-2641]
```
i.e. Ad_g-rank is literally a DIFFERENCE of classical Mordell-Weil ranks over a tower — this is
the up-a-dimension mechanism the mission brief is asking about, made completely explicit and
computable via ordinary number-field descent (no p-adic input needed to compute the rank itself,
only to compute the REGULATOR/logarithm side).

**Exact group-theoretic point formulas** (all explicit, all PROVEN as group theory — only the
p-adic identity linking them to the iterated integral is conjectural):
- **A4** (order-3 Frobenius, the only REGULAR case, density 2/3 of primes): single point `P`
  and its 4 Galois translates `P1,...,P4` generate `E(H)_L^{Ad_g}`; `P_{g_α} = P2 + ζ3⁻¹P3 + ζ3 P4`
  (DLR_stark_points.txt:2601-2605).
- **S4** (order-3 or order-4 Frobenius regular; order-4 case density 7/12): same shape formula,
  `P_{g_α} = P2+ζ3⁻¹P3+ζ3P4` (order 3) or explicit `i`-eigenspace combinations (order 4, eq 75-76).
- **A5** (order >2 Frobenius regular, density 11/15): six points `P1,...,P6` (from a single
  point `P ∈ E(M̃)⁻`, M̃ the sextic Lagrange-resolvent field) generate a 6-dim space covering BOTH
  three-dimensional constituents `ρ1⊕ρ2 = Ad_g ⊕ Ad_{g'}` simultaneously (DLR_stark_points.txt:
  2707-2741) — the A5 case is the richest, giving access to TWO adjoint constituents at once
  from ONE Galois orbit.

**This IS the rank-2 mechanism requested**: two independently-verified rank-2 curves (26b, 52b,
§2 above) instantiate exactly this A4 construction with `r(E,Ad_g)=2`, points obtained by
classical Mordell-Weil descent over the quartic field `M`, and the p-adic identity (eq 79-80)
checked to 20 digits. The rank-(1,1) cousins (91a/91b in Example 5.3, 124a in Example 5.4) show
the SAME field/group data giving rank 1 for a different curve — i.e., the tetrahedral field is
fixed, the curve varies, and the rank-2-vs-rank-(1,1) distinction is purely about which curve's
`L(E,Ad_g,1)` has a double zero. This means: **given a fixed A4/S4/A5 number field, scanning
curves E/Q for which `r(E,Ad_g)=2` is a completely classical (non-p-adic) rank computation**,
and the p-adic apparatus only kicks in afterward to verify/predict the regulator identity.

### Later work (2016–2025) — status of each named extension

- **Rivero–Rotger, Beilinson-Flach elements, Stark units and p-adic iterated integrals**
  (arXiv:1806.10022, Forum Math. 31 (2019)) — cached (`rivero_rotger_beilinson_flach.pdf/.txt`)
  but NOT read in this pass; per DR1's own forward reference (item II, DR1_diagonal_gross_zagier
  .txt:318-327) this is the `h`=Eisenstein-series specialization proving
  `L(E,ρ,1)≠0 ⟹ Hom(ρ,E(Q̄)⊗C)=0` for a single odd irreducible 2-dim ρ (rank 0, not rank 2) —
  flag as NOT FOUND / needs a second pass if the rank-2 face of THIS specific paper matters.
- **Balanced triple product p-adic L-functions and Stark points** (arXiv:2403.05183, 2024) —
  per web search only (not fetched as PDF): a RANK-ONE analogue of Conjecture ES, restricting
  the balanced (not unbalanced) triple-product p-adic L-function to weights `(2,ℓ,m)` and
  evaluating at `(2,1,1)` — proves some special cases. STATUS: proven-in-special-cases,
  conjectural in general; NOT independently verified from primary text in this pass.
- **Casazza–Rotger, "Stark points and the Hida-Rankin p-adic L-function"** (Ramanujan J. 45
  (2018)) and **"On the elliptic Stark conjecture at primes of multiplicative reduction"**
  (Indiana Univ. Math. J. 68 (2019)) — per web search only: extends Conjecture ES to `f` with
  SPLIT multiplicative reduction at p, proves particular cases. NOT independently verified here.
- **Gatti–Guitart, "On the elliptic Stark conjecture in higher weight"** (arXiv:1903.02430) —
  per web search only: extends to `f` of weight `k=r+2≥2` (not just weight 2), `g,h` still
  weight 1; proposes conjectural formulas, gives theoretical evidence in some cases. NOT
  independently verified here.
- **Rivero, generalized Kato classes / exceptional zero / adjoint L-invariant** (per web search,
  e.g. arXiv:2103.00987 "Generalized Kato classes and exceptional zero conjectures"): a NEW
  PROOF (Euler-systems route) of a DLR conjecture on the L-invariant of `Ad_g` for weight-1 g —
  status: theorem, in the exceptional-zero corner of the DLR programme, not independently
  verified from primary text here.
- **Fornea–Gehrmann, Plectic Stark-Heegner points** (arXiv:2104.12575, read above) — a
  DIFFERENT construction (not diagonal-cycle-based; uses Čerednik-Drinfeld p-adic uniformization
  of Shimura curves + Nekovář-Scholl "plectic" cohomology) aimed at elliptic curves over general
  totally real F with MULTIPLE primes `p_1,...,p_r` of multiplicative reduction, targeting rank
  `r ≥ 2` via an `r`-fold WEDGE `∧^r A(E)`. Purely CONJECTURAL construction; "indirect evidence"
  offered = showing higher derivatives of anticyclotomic p-adic L-functions compute the plectic
  invariants (their Theorem, not the full plectic-point conjecture itself).
- **Fornea–Gehrmann, On the algebraicity of polyquadratic plectic points** (arXiv:2203.15998,
  read above) — PROVES (not just conjectures) algebraicity in the POLYQUADRATIC CM special case:
  **Theorem A** (Arithmetic significance, fornea_gehrmann_polyquadratic.txt:251-253):
  `N_{S/℘}(pr_S^-(P_{A,S})) ≠ 0 ⟹ r_alg(A/E)=r & r_an(A/E)=r`.
  **Theorem B** (Algebraicity, line 255-258): the plectic invariant equals (a norm of) an
  explicit wedge `w_{A,S} ∈ ∧^r(A(E)_Ω)` of GLOBAL points over some auxiliary quadratic `Ω/Q`.
  **Theorem C** (line 274-277): an iff characterization tying non-vanishing to BOTH the analytic
  rank AND a max-rank condition `ϱ_A(S)=r` over the twists. Authors explicitly flag (Remark 1.11)
  that this is a proof of only the "minus part" of their earlier conjecture, aside from the
  unwanted auxiliary extension `Ω/Q`; the "plus part" is deferred to "future work" via [HM22].
  **This is the most advanced PROVEN rank-≥2 plectic result found in this pass** — but it is a
  restricted CM/polyquadratic case, structurally parallel to (not a generalization of) the
  DLR/DR programme; the two research lines (diagonal cycles vs. plectic/Shimura-curve) remain
  separate as of the papers read here.
- Non-Archimedean plectic Jacobians (arXiv:2401.07737) — found only via web search title, not
  fetched/read; NOT FOUND beyond the abstract-level description already reported by the search.

---

## 5. NORMALIZATION TRAPS (for a future instrument)

1. **Test-vector dependence, hidden in Conjecture ES's "for some choice of test vectors."**
   The trilinear form `I_p^0` and its target formula both depend on choices of `(f̆,γ̆,h̆)`; DR2
   is explicit (DR2_HWA_BSD.txt:225-227) that different choices multiply the p-adic L-value by
   an ALGEBRAIC factor in the Hecke field, and the identity `Lp^{fα}(f̆*,ğ_α,h̆_α) ~ Lp^{fα}(...)`
   uses `~` = "equal up to an algebraic factor" throughout — an instrument MUST fix and record
   exact test-vector normalizations before comparing numbers across runs, or apparent
   discrepancies will just be this ambiguity.
2. **Two inequivalent p-stabilizations `g_α` vs `g_β`** (roots of the weight-1 Hecke polynomial)
   give DIFFERENT non-classical p-adic L-values (DR2's four values in eq. 10, DR2_HWA_BSD.txt:
   245-248) that "bear no simple direct relation to L(f,g,h,1), or to each other" when the
   central value is nonzero — only when `L(f,g,h,1)=0` do they collectively become "avatars"
   of the second derivative. Do not conflate `g_α` and `g_β` branches.
3. **Irregular primes (`α_g=β_g`) break Hypothesis C** except when `g` is Eisenstein — for
   cuspidal irregular `g`, Hypothesis C is explicitly "not expected to hold" (DLR_stark_points
   .txt:274), so the whole `e_{g_α*}` projector construction is unavailable; must screen for
   `α_g ≠ β_g` (equivalently, `p` a REGULAR prime for `ρ_g`) before attempting any computation.
4. **Frobenius-regularity density is NOT 1** — for the exotic A4/S4/A5 constructions, the "point
   `P_{g_α}` is completely pinned down" case only occurs for a fixed positive-density (2/3, 7/12,
   11/15 respectively) subset of primes; for the complementary density, Conjecture ES only
   asserts `P_{g_α}` lies in an unspecified subspace — an instrument scanning primes must check
   the Frobenius conjugacy class in the relevant `A4/S4/A5` extension before trusting a specific
   point-formula, not just check `p ∤ N`.
5. **The "constructive" framing is aspirational, not operational** — in every worked numerical
   example, the GLOBAL side (points, units) was obtained FIRST by ordinary/CM descent methods
   (Magma, naive search) and the p-adic iterated integral computed SECOND as a check. Don't
   present Conjecture ES as a way to "find" rank-2 points without already knowing where to look;
   its verified content is an IDENTITY between two independently-computable sides, not (yet) a
   search algorithm for the points themselves.
6. **Weight-1 Fourier coefficients are algebraic, not rational** — every worked example needed
   an explicit number field (`Q(ζ3), Q(ζ), Q(i), Q(√5)`, etc.) and an explicit p-adic embedding
   of that field before ANY computation could start; get the embedding convention (which root of
   unity maps to which residue mod p) wrong and every downstream digit is wrong with no local
   symptom — DLR are careful to always spell out "the unique 12th root of unity in `Z_13`
   congruent to `7` mod 13" etc.; replicate this discipline exactly.
7. **`E(f,g,h)` / `E_0(f)` / `E_1(f)` "Euler factor" normalization varies by which leg is
   dominant** — DR1's `E,E_0,E_1` (weights `k≥ℓ+m`, eq 6-8) and DLR's `E(g_α,f,h), E_0(g_α),
   E_1(g_α)` (weight-1 `g` dominant, DLR_stark_points.txt:2748-2759) are STRUCTURALLY parallel
   but NOT the same formula — swapping which modular form is treated as "dominant weight" changes
   which Frobenius eigenvalues (`α` vs `β`) enter the product. Keep DR1-style and DLR-style Euler
   factors in clearly labeled separate functions if implementing both.
8. **Sign/parity bookkeeping**: Hypothesis A (all local signs +1) is what FORCES even-order
   vanishing; if a candidate curve/representation has a `-1` local sign somewhere the entire
   even-rank / double-zero framing is inapplicable and one is instead in an ODD analytic rank
   setting (Gross-Zagier/Kolyvagin territory, rank 1, different toolkit entirely) — screen local
   root numbers explicitly, don't infer parity from the global sign alone.

---

## NOT FOUND / needs follow-up

- Katz-basis explicit construction recipe (Lauder §2.1.1 body, beyond opening lines) — needed
  for literal implementation, not extracted in this pass.
- Lauder's Note 2.3 (1) and (3) — the two "difficult to analyse" complexity aspects of the full
  Rankin p-adic L-function algorithm (as opposed to just the ordinary-projection subroutine).
- Explicit code/Magma-package availability for the DLR/Lauder implementation — no URL found in
  extracted text.
- Rivero–Rotger 2019 paper (arXiv:1806.10022) — cached, not read; needed if the Beilinson-Flach
  rank-0 mechanism (vs. rank-2) becomes relevant.
- arXiv:2403.05183 (rank-one analogue, 2024) and Casazza-Rotger / Gatti-Guitart papers — only
  characterized via web search summaries, not primary-text-verified.
- The "plus part" resolution of the polyquadratic plectic conjecture (deferred by Fornea-Gehrmann
  to unpublished/future work citing [HM22]) — check whether it has since appeared.
