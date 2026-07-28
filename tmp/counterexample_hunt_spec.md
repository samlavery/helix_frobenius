# Counterexample-hunt spec — falsifiers at scale + the plane-JC side quest

**Date 2026-07-26. Status: SPEC (Sam-approved direction; runs pending).
Provenance rule (post-Jul-24 lesson): every instrument file created under
this spec carries a header line `-- hunt-spec 2026-07-26, session <id>`;
nothing uncommitted is ever cited as corpus evidence.**

Register discipline (the JC lesson): a "candidate" exists only after the
certification ladder below. Detections at instrument resolution are
"events"; events survive re-run + tightened gates to become "flags";
flags get exact/interval certification (bsd_certify engineering) to
become "candidates". Pre-registered: everything below 5× instrument
resolution is noise and is recorded as such. Null results are recorded
in the falsifiability register (count currently: zero, after deliberate
searching) with the scale S of the search attached.

---

## Campaign 1 — Siegel corridor (GRH falsifier, classical weak spot)

Target: an off-line event for real primitive χ mod q — the one place
classical lore itself prices a possible GRH failure (exceptional/Siegel
zeros near s = 1).

Instrument: the no-oracle 3D locator (focal_closure.py growth scanner,
validated Dirichlet real+complex to 1e-12) + the S(t)-ledger audit
variable: S_Γ = S_mult + N_off^mult (CarrierScaleCompensation /
ResidueJump frame). N_off^mult > 0 anywhere = event.

Sweep: real primitive χ, q ascending (start 3 ≤ q ≤ 10^4, extend to 10^5
as runtime allows); per character: (a) the near-s=1 corridor scan
[1 − c/log q, 1] on the real axis (the Siegel box), (b) the low strip
0 < t ≤ T(q) with the contour census vs carrier census cross-check.
Exactness gate: locator residual vs lattice threshold; float pipeline
only for triage, every event re-run in mpmath high precision.

Cost: cheap per character; embarrassingly parallel; overnight for the
10^4 sweep.

## Campaign 2 — Lehmer/close-pair corridor (arch-floor falsifier)

Target: falsifier (a) of the register — a non-collapsing arch floor at a
close pair, where discreteness stress is maximal.

Instrument: the arch-floor collapse test at the 0.1%-resolution method
laws (de-modulated eta, peak enumeration, never clip). Sites: the known
first real pairs at indices 66678/71733, the classical Lehmer pairs from
tables, plus the tightest 100 pairs below T = 10^6 harvested from LMFDB
zero lists.

Semantics: floor collapse to machine zero at every site = null (register
count stays zero, scale updated). A floor that BOTTOMS OUT above the
exactness gate, reproducibly, at tightened resolution = event → ladder.

## Campaign 3 — Maass spiral hunt (Ramanujan falsifier)

Target: a spiral strand — |α_p| ≠ 1 signature — in the Maass family,
where RP is open and our own register holds temperedness as the favored
branch, not a theorem (helix-strand frame: EveryFrobeniusHasHelixSource).

Instrument: the radius-live strand detector (HelixStrandTemperedness
frame; the radius-live niceness bank means no unitarity is presupposed by
the instrument — the detector is honest w.r.t. the 7/64 window).
Data: LMFDB Maass forms (level 1 eigenvalue list, then level > 1),
a_p to p ≤ 10^4 per form. Per (form, p): strand-radius estimate with
resolution certificate; the two-clock weight law (GL(2) long-span
instrument, meas/pred ~1.0 ± 4%) upgraded to the 0.1% resolution methods
before any deviation is read.

Known trap (pre-registered): windowing leakage manufactured a fake line
once before (32.a ln4 anomaly). Every deviation must survive the leakage
diagnostic before it is even an "event".

## Side quest — the plane-JC multiplication-mechanism dichotomy

The 3D counterexample's mechanism (Tao digestion, 2026-07-21): the
multiplication map (linear form) × (quadratic form) → (cubic form) on
binary forms is 3-to-1 by the fundamental theorem of algebra (three roots
= three linear-factor splits); the construction's content is a
resultant-normalized 3-dim affine slice on which the Jacobian determinant
is CONSTANT (−2). Collision is free; constancy is the miracle.

The 2D question, made finite: does any resultant-normalized affine slice
of the analogous 2-variable multiplication family have constant Jacobian?
Parametrize candidate slices to total degree D (start D = 4, raise to 8);
"det = const" is a finite system of polynomial identities in the slice
parameters, over ℚ, solvable by EXACT linear algebra + Gröbner steps —
no floats anywhere.

Outcomes (both are content):
- consistent system → explicit 2D candidate map → direct exact collision
  check → if it collides, that is a counterexample to the plane Jacobian
  conjecture (then: independent symbolic verification ×2 before a word
  is said to anyone);
- inconsistent at all D ≤ 8 → the mechanism-class obstruction in the
  plane, certificate = the exact rank computation → Lean brick
  (PlaneMultiplicationObstruction.lean: the inconsistency as a
  decide/linear-algebra theorem), a publishable structural result about
  WHY the plane resists the only known counterexample mechanism.

Kill criteria: two week-equivalents; if the parameter systems grow past
exact-solvability at D = 8 without a decision, record and park.

**Theory sharpening (2026-07-26 session).** The mechanism decomposes into
three requirements, and the 2D failure mode localizes:
(a) *collision* — free, from factorization multiplicity (cubic: 3 linear
splits; the 2D analog l₁·l₂ is 2:1 via the factor swap);
(b) *branch-locus removal* — constant Jacobian forbids ramification, and
the collision degenerates exactly on Res(l₁,l₂) = 0 (2D: the diagonal
l₁ = l₂, where the swap has fixed points and the multiplication map's
Jacobian must vanish) — so the slice must sit inside Res = const, which
removes the branch locus and makes the swap free;
(c) *the miracle* — the slice must be polynomially ≅ ℂⁿ (Tao: "the
variety is in fact equivalent to the affine space ℂ³ by polynomial
changes of variable"). In 2D the natural Res/disc level sets are smooth
affine QUADRICS (e.g. {b² − 4ac = 1}), which are NOT isomorphic to ℂ² —
the candidate domains fail (c) at the first examples.
Refined round-1 question: does ANY 2-dim affine-polynomial slice satisfy
(b) ∧ (c) simultaneously for the 2-variable multiplication family? The
exact search runs over polynomially-parametrized slices (l₁, l₂ with
coefficients polynomial in (u,v), degree ladder), imposing det J = const
as exact identities over ℚ; the (c)-failure of quadric slices suggests
the obstruction candidate: *in the plane, branch-removal forces the slice
onto a nontrivial level surface that is never affine space* — if that
survives the search, it is the mechanism-class obstruction theorem, and
its statement is coordinate-free enough to aim at Lean.

**Round-1 results (2026-07-27).**

*Deck-symmetry obstruction (second leg, theorem-grade modulo standard
citations).* Any plane candidate F with a nontrivial polynomial deck
symmetry (F∘σ = F, σ ≠ id a polynomial automorphism — the shape a
swap-invariant multiplication slice would produce) is IMPOSSIBLE: a deck
symmetry of a generically finite map has finite order; finite-order
polynomial automorphisms of ℂ² are linearizable (Jung–van der Kulk tame
generation + the standard tree/finite-subgroup argument), hence have a
fixed point; at a fixed point of a deck symmetry the map ramifies, so
det J vanishes there — contradicting constancy. CONSEQUENCE: plane
collisions must be deck-FREE (asymmetric), exactly as the 3D
counterexample's three factorizations are; naive symmetric 2D
constructions are dead by theorem, not by search.

*Honesty anchor:* plane JC is proven for degree ≤ 100 (Moh), so no
low-degree search can find a counterexample; the low-degree ladder maps
the MECHANISM (which slices support det-constancy) — its value is the
obstruction structure, not direct hunting.

*D=1 exact search (tmp/jc_plane_d1.sage, exact over ℚ):* normal form
l₁ = ux+vy, l₂ = A(u,v)x+B(u,v)y affine-linear, F a linear combination of
the product coefficients (12 parameters). det J has 6 monomials; the
det-const locus (const ≠ 0, Rabinowitsch) has DIMENSION 8 — a rich family
containing the tame shears (e.g. l₂ = x+uy, F=(v+u², u), det ≡ −1) — while
a generic asymmetric pin (l₂=(1+3v)x+2uy) is INCONSISTENT (dim −1):
det-constancy is a proper, structured condition on slices. All D=1
members are degree-≤2 maps, injective by Wang's theorem — oracle
consistent. Next rung: D=2 (quartic maps), asking whether the det-const
family acquires any component NOT generated by tame compositions — the
Jung–van der Kulk frame says no for automorphisms; the question is
whether non-injective det-const candidates are structurally excluded or
merely absent at low degree.

## Campaign-2 telemetry discovery (2026-07-28): Lehmer bimodality

The arch/gap² ratio across the harvested close-pair sites is BIMODAL,
five to eight orders apart: ordinary pairs at ~2.4–2.6 (d = −5108,
−3288) vs ultra-suppressed at 10⁻⁵–10⁻⁸ (d = 8113, 4737, −7691, 3061),
with intermediates (−8103, −2999 at ~2·10⁻²). The quadratic law alone
does not predict two populations — at the suppressed sites the curvature
|Λ''| collapses along with the gap (near-double-zero shape). Hypothesis,
pre-registered NOT asserted: selection effect (scan-missed pairs are
biased toward locally-flat |Λ|). Falsification test, designed: an
unbiased control — systematic fine scan (step 0.01) over a fresh
conductor band, ALL pairs in the same gap range regardless of
coarse-scan visibility; bimodality persisting = a new Lehmer-class law,
ordinary population dominating = selection artifact, retract. Full
numbers in memory: lehmer-bimodality.

## Order of execution

1. Campaign 1 tonight-scale sweep (existing instrument, new driver).
2. Campaign 3 harness (radius-live detector + LMFDB pull) — the highest
   scientific value per hour given RP-for-Maass sits next to our own
   tower claims.
3. Campaign 2 opportunistically (short runs at named sites).
4. Side quest in parallel as the theory session (exact algebra, no
   compute contention).
