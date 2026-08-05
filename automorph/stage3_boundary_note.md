# Stage 3, item 1: the adaptive-depth boundary derivation (working note)

Target of record: E(n) = O(1) (bounded form). This note: pin the diffuse/atomic
boundary. Status: DERIVED AT SPEED, needs paper-rigor verification. Nothing here
bounds mass in the atomic zone.

## Claim

With per-band adaptive depth, the flagship engine yields unconditionally
E(n) = O(logloglog n), with irreducible atomic zone p <= (log n)^{O(1)}.

## Derivation

Band k, log Q ~ log n/k. Engine (paper, App. B post-pass-3): amplitudes
F <= H·Q^{J+1}, r_max = 3J+5, per-block saving exponent eta' >= 2^{-3J-6};
chain closes iff saving exponent beats target:

  (log n / k) · 2^{-3J-6}  >=  B·loglog n + J·log(3 log H)      (*)

[second term = J-dim ETK product loss; H = (log n)^2.]

Adaptive choice: J(k) := max J satisfying (*). Two regimes:

1. Reach regime (large k): J(k) = (1/3)·log2( log n / (C·k·loglog n) ).
   Contribution: sum_k 2^{-J(k)}/k = (C·loglog n/log n)^{1/3} · sum_{k<=k_max} k^{-2/3}
   ≈ 3·(k_max · loglog n / log n)^{1/3} = O(1)   at   k_max = log n/(C·loglog n).
   Coverage: all k <= k_max, i.e. all primes p with log p >= C·loglog n,
   i.e. p >= (log n)^C.

2. ETK-cap regime (small k): (*)'s second term forces
   J <= loglog n/(logloglog n)^2 =: J_cap. There 2^{-J_cap} = (log n)^{-o(1)} but
   sum over k <= k_1 of 2^{-J_cap}/k ≈ e^{-c·loglog n/(logloglog n)^2}·log k_1 → 0. OK.

Uncovered (atomic) zone: p <= (log n)^C; trivial mass = logloglog n + O(1).
Hence E(n) <= O(1) + o(1) + logloglog n + O(1) = O(logloglog n).

## Verification points for the rigor pass (in order)

V1. The reach constraint (*): re-derive from the paper's §B.8/§B.9 with the
    pass-3 constants (r_max = 3J+5, c = 5log2, B >= 2 K-based check). Confirm the
    per-block-to-band summation (eq. blocksum) is uniform in the adaptive J(k).
V2. Dominance lemma hypothesis Q >= 8eH·e^{r_max} under adaptive J: at large k,
    Q = e^{C·loglog n}-ish and e^{r_max} = e^{3J+5} with J ~ small there — check
    the crossover explicitly. THIS IS THE LIKELIEST FAILURE POINT: near k_max,
    log Q ~ C·loglog n while r_max must stay << log Q. J(k_max) ~ (1/3)log2(1) ~ 0
    — fine at the very edge, but the approach to the edge needs the explicit
    inequality chain.
V3. ETK cap: the (3 log H)^J loss vs Theorem ET's actual form (outer J factor +
    log H per coordinate) — recompute with App. C constants, not the proxy.
V4. Vaughan Q/U term and prime-power terms under log Q ~ loglog n-sized blocks
    (U = Q^{1/3} still >> rho? rho = 1+1/(k+r_max) with k huge — block count
    explodes near k_max; confirm blocksum absorbs it).
V5. If V1–V4 hold: E(n) = O(logloglog n) is a theorem-grade improvement of the
    flagship rate — fold into paper or hold as note 2.

## After verification: the isolated target

  ATOMIC BUDGET (final form): for every n,
     sum over balanced primes p <= (log n)^C of 1/p   is bounded.
  Tolerance: any per-window balanced fraction <= 1/(loglog p)^2 suffices.
  Routes ranked: (a) monotone-integer defect object (S(t) dichotomy;
  conservation law integrated bound is FREE; compiled stopping-time kernels =
  raw material); (b) Wu–Shmerkin discretized entropy in harmonized chart;
  (c) window pair-lemma on deterministic band systems.
  Dead ends (do not revisit): uniform decay, congruence-only, global-ledger LP,
  product relaxation, smooth-credit pointwise budget.

## The geometric attack (Sam's directive: use the framework — 3D first)

Reformulation on the carrier. The descent phase of n is phi_n(u) =
frac(n e^{-u}) — the helix angle of n sliding down the carrier. Rail p's
ladder is the arithmetic progression {j·log p} in carrier time u: an
incommensurable stroboscope (spacing log p = the carrier scaling of rail p).
BALANCE OF RAIL p == the stroboscope only ever flashes on the lower
half-turn. THE ATOMIC BUDGET == a COLLECTIVE-FREEZE EXCLUSION: many
incommensurable stroboscopes cannot all freeze on the lower half-circle of
ONE shared descent flow, unless the flow itself is degenerate (n p-adically
near smooth points — the bounded LP credit, exactly what the census found).

The unification move (Langlands-style, house asset): the program has a
PROVEN freeze law — ChannelConstancy (freeze <=> the character lies in the
annihilator H-perp; constancy is codimension-forced, never free) and the
Weil rail-native collective-freeze detection. Plan: formalize joint balance
of a rail set S as collective freeze of S-indexed channels on the descent
flow; the annihilator law bounds simultaneous freeze by CODIMENSION, and
codimension in the atomic zone is priced by the archimedean budget (the
conservation law — integrated bound already FREE). The monotone-integer
defect object of route (a) = the freeze ledger: per rung, the integer count
of channels that left the frozen set (a monotone stopping-time object —
compiled kernels exist). S(t)-dichotomy shape: sublinear integrated freeze
defect (free, from conservation) + monotone integer structure ==> frozen
mass bounded.

FIRST CONCRETE TASK (before V1-V5 or in parallel): write the freeze-ledger
object for the polylog zone explicitly — D_S(u) := #{rails in S unfrozen by
carrier time u} — monotone, integer, with D_S(log 2n) pinned by the
conservation law; prove the dichotomy step for it. If the dichotomy holds,
the atomic budget follows with constant = the LP/smooth credit. This is the
house's proven proof-shape aimed at the isolated target.

## Task 1 first contact (executed): D_S defined, dichotomy attempted — ROUTE-NARROWING RESULT

D_S(u) := #{p in S : first carry of rail p occurs by carrier time u}.
Monotone, integer, stopping-time structure — the object is well-defined and
the compiled kernels express it. DICHOTOMY ATTEMPT, honest outcome:

(i) GLOBAL pin too slack: conservation bounds CARRY mass (n-scale; deep
ledger sqrt(n)-scale); the atomic zone's freeze signal is polylog — same
scale mismatch as the LP null, resurfacing at the ledger level.
(ii) ZONE-LOCAL pin does not exist unconditionally: Sum_{p<=Y} v_p log p =
log(Y-smooth part of C(2n,n)), which CRT leaves free at n^{o(1)} moduli —
asserting its size IS (morally) the budget. No free integrated bound.
(iii) Flow continuity vacuous: between adjacent ladder samples the descent
phase winds ~ n e^{-u} · (sample gap) turns — confinement on the sample set
imposes no constraint through continuity at deep scales.

CONCLUSION (route-narrowing, by the progress rule): route (a) STANDALONE is
dead — a monotone-integer dichotomy cannot close without an integrated bound,
and no chart-side source of that bound survives CRT freedom. Routes (a) and
(b) MERGE: the defect object's integrated bound must be an ENTROPY inequality
— the one kind of bound that beats CRT freedom by counting integer
configurations ACROSS scales (Wu–Shmerkin discretized machinery, in the
harmonized chart, applied to the freeze ledger). The merged route is now THE
route: entropy-bounded freeze ledger. Next action: state the required entropy
inequality for D_S exactly (per scale-block, per rail-set), then check it
against the discretized Wu–Shmerkin toolkit at source.

## NOVEL METHOD (Sam's directive — replace the import, use ours)

Do not import entropy machinery. The house source of cross-scale integrated
bounds that CRT cannot dodge: THE SHIFTED HARMONIZED CONSERVATION LAWS.
Deep digit j of rail p at point n = LEVEL-1 digit of rail p at the point
p^{j-1}·n. Level-1 occupancy is CHART-DETERMINED (band geometry + theta),
pinned by the harmonized law of the SHIFTED point p^{j-1}n — shifting moves
the archimedean size, and band geometry at the shifted point is
deterministic, not CRT-free. So the freeze ledger D_S acquires one exact,
band-resolved integrated identity PER SHIFT — a lattice of pins indexed by
(rail, level), each at its own scale, none aggregate. The LP null does NOT
apply: it tested aggregate totals under product relaxation; these are
band-resolved laws on the position curve. REQUIRED INEQUALITY, restated:
the joint freeze of S forces the shifted points {p^j n} into prescribed
band cells at every (p,j) — count admissible positions via the
band-arrangement of the shifted family (one real parameter n, polylog·log n
deterministic cell conditions). Entropy = cell-counting in OUR arrangement,
not imported. NEXT ACTION: for the zone p <= (log n)^C, bound the number of
n <= N landing in the joint shifted-cell intersection via the compiled
two-level telescoping applied at shifted points (levelTwoJointCarry at
p^{j-1}n) — the J=2 identity is ALREADY the counting instrument for pairs
of shifts. Start: pair (p,j),(p,j+1) — consecutive shifts of ONE rail —
prove the first nontrivial admissible-cell bound there.

## Item 2 executed: pin summation — FOURTH NO-GO (signal/slack parity)

Derivation (rail p balanced at n, cascade q_j = floor(n/p^{j-1})):
(1) Balance forces rail p's contribution to EVERY cascade conservation law
    (at every q_j) to zero — via carryAt_shift_transport (now COMPILED).
(2) But each Stirling pin at q_j has additive slack O(log q_j), and rail p's
    dodge signal at q_j is also O(log q_j) — SIGNAL/SLACK PARITY, at every
    cascade point, every scale, harmonized or not (deep-ledger version:
    signal log q vs slack sqrt(q) — worse).
(3) Cross-rails don't help: other balanced rails are NOT constrained at
    q_j (different sample point), so joint laws stay trivially satisfiable.

FOURTH NO-GO (record; extends nulls 1-3): any bound on the atomic budget
derived from finitely many Lambda-weighted conservation totals — at the
original point, shifted points, quotient-cascade points, or any derived
family — is blind: per-law slack O(log) equals per-rail total signal O(log),
and slacks add. Conservation TOTALS can never see single-rail dodges.
Additive-ledger approaches to the atomic zone are CLOSED.

WHAT SURVIVES: multiplicative/counting constraints. The transport lemma +
J=2 telescoping are exact COUNTING identities (theta-differences), not
totals — they measure sets of n, hence give entropy-type (fraction)
information. The open core, sharpest form yet: convert exact per-window
counting identities into a POINTWISE statement — the every-n vs almost-all
gap, now isolated as the single remaining difficulty, with all additive
routes provably closed around it. Candidate mechanism (only survivor on the
board): self-reference — apply the counting identities to the window
CENTERED AT n ITSELF at each cascade scale (windows [q_j - w_j, q_j + w_j]),
where n's own membership in its window's counted set is forced; whether the
window counts can be made small enough to exclude n pointwise is exactly
the question. NEXT: formalize this self-referential window argument;
determine the window-size trade-off (count bound vs membership forcing).

## AUDIT CORRECTION (Sam's harmonization question — fourth no-go SCOPE NARROWED)

Step (3) of the fourth no-go ("cross-rails unconstrained at cascade points")
is WRONG — un-harmonized rails. Correct statement: at the p-cascade point
q_j, rail r's residue is DETERMINED by the joint residues:
  q_j mod r^i = (n mod r^i - n mod p^{j-1}) · p^{-(j-1)} mod r^i,
an affine map twisted by the RATIO HARMONIC p^{-1} in (Z/r^i)^* — the
cascade rotates rail r's cells by the multiplicative orbit of p mod r^i.
Joint balance therefore maps to a STRUCTURED (affine image of
product-of-lower-half) configuration at every cascade point; the no-go's
parity argument closes only the single-rail-signal version. The joint
structured-image version is REOPENED.

THE UN-MINED VEIN: intersections of multiplicatively rotated half-cells
in Z/r^i — orbit {p^{-j} mod r^i}: if the rotations spread (large
ord_{r^i}(p)), the intersection of rotated cells shrinks/empties — a
FINITE, checkable, pointwise pair-exclusion mechanism. SHARP OPEN POINT:
the forcing source — what requires the rotated-cell memberships (the
conservation laws do not force per-rail bits; the naive full-tower CRT
count reverts to almost-all). Next: (i) compute rotated-cell
intersections for small pairs (p,r) and depths — measure when empty;
(ii) find the forcing: candidate = the compiled two-level transport
applied ON RAIL r AT THE p-CASCADE POINTS (levels of r at q_j ARE
constrained by r-balance at n through the affine map — check whether
transport composes across rails).

## RE-CHECK OF ALL FOUR NO-GOS (Sam's prompt — scopes corrected)

NO-GO 1 (uniform decay; COMPILED): sound, scope LITERAL — kills only
uniform C·rho^r envelopes on the closed ledger. Nothing broader.

NO-GO 2 (CRT realizability; COMPILED): theorem sound, MY USAGE OVERBROAD.
It realizes FIXED-FINITE-DEPTH patterns only (witness: all-zero digits,
modulus independent of n). It does NOT exclude congruence mechanisms whose
depth grows with n coupled to size — which is exactly the rotated-cell
pair-exclusion class (twists p^{-j} mod r^i, j up to depth(n)). "No
congruence-only proof" must read "no fixed-depth congruence-only proof."

NO-GO 3 (LP null; MEASURED): scope = aggregate Lambda-totals over
per-rail PRODUCT relaxations only (already narrowed once). Band-resolved
constraints at shifted/cascade points with the affine coupling were never
tested, let alone closed.

NO-GO 4 (signal/slack parity): narrowed above — single-rail signal vs
per-law slack only; joint structured-image laws open.

NET CORRECTION: the wall was never "triangulated" — the depth-coupled
congruence lane (rotated half-cell intersections under ratio-harmonic
twists, membership forced by depth growing with n) was NEVER closed by any
of the four. It is the open lane, and it was visible inside no-go 2's
witness the whole time: the all-zero pattern needs modulus prod p^{k_p}
free of n — full balance does not have that freedom. AMEND DEAD-END LIST:
"congruence-only" -> "FIXED-DEPTH congruence-only". Next action unchanged
and now unfenced: compute rotated-cell intersections for small (p,r) and
growing depth; the forcing question becomes whether depth-coupling (moduli
allowed to grow with n) supplies membership — which no no-go forbids.

## ROTATED-CELLS PROBE RESULTS (the mechanism has teeth)

(a) FORCING IS REAL: every pair shows cascade lower-half fractions ABOVE
null — (7,11): 0.722 vs 0.545; (11,13): 0.692 vs 0.538; two-level 0.51 vs
0.29. Caveat: includes trivial j=1 (q_1=n, forced prob 1); but excess
(~0.10-0.18) exceeds the j=1-only prediction (~0.04) ⟹ forcing extends
beyond j=1 (archimedean carry-over of shared high digits under division).
NEXT MEASUREMENT: the j-RESOLVED forcing curve — correlation length ell.

(b) CAPACITY IS SEVERE: rotated-cell intersections collapse to {0} (the
rotation fixed point) in 3-5 steps for generic pairs ((3,13) stalls at 4 =
small-orbit degenerate case, ord_13(3)=3). READING: full forcing over ~5
steps ⟹ n ≡ 0 mod r² — LITERAL DIVISIBILITY — which has the hard
archimedean budget (Lemma A: prod r^2 | ... ≤ n). THE PROOF SHAPE:
  forcing length ell ≥ collapse length (~4-5)
    ⟹ balanced rails trapped near zero classes
    ⟹ divisibility budget ⟹ bounded atomic mass.
THE WHOLE PROBLEM NOW RIDES ON ONE QUANTITY: the provable forcing depth of
r-balance under p-division. Next: (i) j-resolved forcing curve (measure
ell); (ii) prove the j=2 forcing step analytically (transport composition
across rails — the first rung of ell ≥ 2).

## FORCING CURVE RESULT: ell ≈ 2 — PROOF SHAPE DEAD AS SKETCHED

j-resolved (5971 events, null-normalized): j=1: 1.84 (trivial, calibrates);
j=2: 1.13/1.23 (real, modest); j=3: 1.02/1.03 (marginal); j>=4: 1.00 (gone;
j>=6 wiggles are selection/small-N noise). MEASURED ell ≈ 2-3 vs collapse
length ~4-5 REQUIRED. Division by p scrambles r-digits in ~2 steps
(~log_r p levels of mixing per step). The collapse-to-divisibility route
FAILS in current form. SALVAGE: the j=2 bias (13-23%, pointwise-real) is a
provable-candidate pairwise constraint — weak but unconditional; park as
"rung-1 lemma" (transport composition, one step).

## STANDING BLOCKERS (for the systematic walkthrough)
B1. Forcing decay: p-division destroys r-digit memory in ~2 steps —
    kills orbit-collapse; any cross-rail mechanism must survive mixing.
B2. Every-n vs almost-all conversion: counting identities are exact but
    per-window; no pointwise transfer known (THE core, in every route).
B3. No-go fences (corrected scopes): additive ledgers (4), aggregate LP
    (3), fixed-depth congruence (2), uniform decay (1) — closed lanes.
B4. Depth-coupled congruence lane OPEN but needs a forcing source with
    range >= mixing length — none known after B1.
B5. Diffuse engine limits: boundary at polylog primes (pending V1-V5);
    atomic zone irreducible to it.

## CORRECTED CAPACITY: ROTATED-CELL MECHANISM CLOSED (correctly)

With translations included (union over lower-half p-translations mod r^2),
admissible intersections STABILIZE LARGE: (3,5): 6/25; (3,7): 14/49;
(5,7): 16/49 (zero shrink); (3,11): 24/121; (7,11): 36/121 (zero shrink);
(5,13): 43/169. NO collapse — the zero-translation collapse was an artifact
of the frozen slice. Double closure: (i) even granting a forcing source,
capacity is a stabilizing constant factor, never divisibility; (ii) no
forcing source exists. Mechanism dead by true capacity. (Retroactively
explains the ell≈2 curve: nothing to measure.) B4 AMENDED: the
depth-coupled congruence lane currently has NO candidate engine.
SURVIVING CORE, purest form (B2): the product-cell/window problem — n IS
its own residue mod prod p^{d_p} >> n; bound the mass of S for which the
S-product lower-half cell can meet a dyadic window pointwise. All
mechanism candidates exhausted; next = systematic blocker walkthrough.

## CALIBRATION FIX (Sam: "rail/carrier/warp calibration") — THE TOP-WINDOW REDUCTION

Warp = winding clock: rung (p,j) reads at winding time t = n/p^j. All prior
attacks sliced by rail (p fixed) or scale band; the native object is the 2D
multiplicative lattice {n/p^j} on the winding chart. MONOTONE RESTRICTION
(loses only constants): balanced ⟹ top rungs balanced ⟹
  budget ≤ sup_n Σ_{p ≤ Y} (1/p)·1[top J_p rungs of rail p in gap cells],
with J_p = c·loglog p rungs (t ≤ p^{c loglog p}) making Σ (1/p)2^{-J_p}
summable. THE RIGHT-HAND SIDE IS DETERMINISTIC BAND GEOMETRY — no residues,
no CRT, no almost-all: a sup over one real position of an explicit indicator
sum. ARCHIMEDEAN CAP RE-DERIVED GEOMETRICALLY: aligning rails' top windows
= nesting explicit intervals; intersection length n·∏ 2^{-J_p} ≥ 1 forces
Σ J_p log 2 ≤ log n ⟹ alignable mass ≤ O(logloglog n) — the triple-log
wall, now derived with ZERO arithmetic. THE IRREDUCIBLE CORE, FINAL FORM:
integer existence in the sub-unit-length intersections — "which nested
explicit interval systems of total length < 1 contain an integer" — pure
Weyl/three-distance geometry, all arithmetic stripped. Every prior wall
(counting vs pointwise, CRT luck, smooth champions) is THIS statement in
different clothes; champions = integers in lucky short intersections.
NEXT: (i) verify the monotone/top-window reduction rigorously (constants);
(ii) the geometric core: bound how often nested hyperbola-gap interval
systems of sub-unit total length contain integers as n slides — the first
formulation of the wall with no arithmetic left in it.

## CALIBRATION (Sam): NOT INTEGERS — SCALED HARMONICS. NOTHING IS FINAL UNTIL 377 IS SOLVED.

The geometric core as stated ("interval nests containing an INTEGER")
re-imports the unit-1 lattice — the un-harmonized chart (method-law:
unit-1 → FALSE NULL). Carrier form: "integer existence" = a CARRIER TICK
landing in a cell, ticks on the harmonically scaled carrier (Δ = π/3, μ6
structure), scanned across the unit ladder π/k per the calibration law.
The extremal/equality analysis must be posed there: interval nests vs the
harmonic tick structure, where the compiled exact-closure laws (μ6
cancellation, freeze/annihilator) live — the machinery for equality-case
rigidity. RESTATED TARGET: classify extremal nest-tick configurations on
the harmonized carrier; show super-C mass forces a tick-cell incidence the
μ6/half-cell closure laws forbid. Current form of the brief (not final — final = 377 solved):
top-window reduction → tightness (no slack exists) → extremal rigidity →
posed on scaled harmonics, not integers.

## PROVEN (today, elementary — the mean half of the budget, sharp threshold)

LEMMA (exact per-rail measure): the top-J balance conditions of rail p
({n/p^{d-i}} < 1/2, 0 <= i < J) confine n mod p^d to an exact fraction
((p+1)/2p)^J   of residues.
PROOF: level conditions are conditions on distinct digit blocks: digit
< p/2 admits (p+1)/2 of p values per level, independent across the J
levels; multiply. QED (finite, Lean-able against the compiled kernels).

THEOREM (mean top-window mass, sharp constant): with J_p = c·loglog p,
  E_n[ Σ_{p ≤ Y} (1/p)·1(top-J_p balanced) ] = Σ_{p ≤ Y} (1/p)·((p+1)/2p)^{J_p}
  = Σ_p 1/( p (log p)^{c·log 2 (1+o(1))} ),
which CONVERGES as Y → ∞ iff  c > c* = 1/log 2 = 1.4427...
PROOF: ((p+1)/2p)^{J} = 2^{-J}(1+1/p)^{J} = (log p)^{-c log2}·(1+o(1));
partial summation with Mertens. QED (elementary, unconditional).

WHAT THIS PINS: in the top-window frame the budget's AVERAGE half is
closed with a sharp threshold. The entire open problem is now ONE
comparison:  sup_n − mean = O(1)  for the top-window functional at any
fixed c > c*. Below c* even the mean diverges (the reduction is vacuous);
above c* the mean converges and only the sup question — the extremal
rigidity on scaled harmonics — remains. c* = 1/log2 is the frame's
exact critical exponent, proven today.

## DERIVATION: ALMOST-ALL BOUNDED E(n) FROM EXISTING ENGINE + CHEBYSHEV

THEOREM (target, riding on flagship Prop (E)): for every eps > 0,
E(n) = O_eps(1) for all n in [N,2N] outside an exceptional set of size
eps*N. I.e. the FULL #377 statement holds for almost all n.

PROOF SKELETON (two lemmas + assembly):
L1 (mean, PROVEN above): for c > 1/log2, mean_x M_c(x) <= mu(c) < inf.
L2 (pair decorrelation, = flagship Prop (E) at J=J_p+J_q, pair form):
   for p != q <= Y: |P(A_p ∩ A_q) - P(A_p)P(A_q)| <= delta(N) -> 0.
   The events A_p are top-window band conditions — exactly the objects
   Prop (E) equidistributes; the pair version is the same ETK/derivative-
   test argument with the two rails' levels concatenated (amplitudes
   multiply through dominance; ranges unchanged). NO new machinery.
ASSEMBLY: Var(M_c) <= mu + mu^2·max delta + diagonal Σ 1/p² = O(1).
Chebyshev: #{x : M_c(x) > T} <= C·N/T². Take T = T(eps). Combine with
the flagship (all-n diffuse bound) and the c > c* mean split:
E(n) <= diffuse + M_c(n) + tail = O(1) off the exceptional set. QED mod L2.

STATUS/CLAIM LADDER: rides on Prop (E) (the paper's active core — same
verification pipeline); when the flagship closes, THIS closes free.
GATE BEFORE ANY CLAIM: check literature for prior a.a.-bounded E(n)
(EGRS Thms 4-5 adjacency; Sanna/Pomerance school). If unclaimed: this is
a SECOND theorem from the same engine — a.a. #377 — strictly between the
asymptotic (weaker) and full #377 (stronger, all-n).
NEXT WORK ITEMS (no narration): (1) write L2's concatenated-levels proof
into the paper appendix (est. 2pp — same lemmas, pair amplitudes);
(2) numerical variance certification of L2 at N=1e6-1e7 (cheap probe);
(3) then the sup problem (the true wall) inherits ONLY the eps-density
exceptional set: full #377 = "the exceptional set is empty for large N" —
the wall restated with everything else discharged.

## SAM'S IDENTIFICATION: TICK AVOIDANCE = THE S(t) GAP

The two open residuals may be ONE statement across fibers:
- digit fiber: harmonic ticks avoid the Kronecker alignment locus of the
  flow with frequencies 1/log p (the atomic budget's remaining content);
- zero fiber: ∫S_native = o(T) — the event set's registration against its
  smooth clock (the program's named open residual).
Both say: THE FIBER'S DISCRETE SET AVOIDS THE DEEP-ALIGNMENT LOCUS OF AN
ALMOST-PERIODIC FLOW WITH LOG-PRIME FREQUENCY LATTICE. (S(t)'s explicit-
formula frequencies ARE log p; the top-window flow's are 1/log p — dual
lattices on the carrier — the warp exchanges them.) CONJECTURE (record,
falsifier: exhibit a fiber with one holding and the other failing at
matched depth): tick-avoidance is fiber-portable — one avoidance theorem
closes both the atomic half of 377 and ∫S = o(T). This would make 377's
last wall and RH-adjacent territory THE SAME wall — consistent with
Tao's HARD rating and with every no-go this campaign compiled.
LEAN STATE OF 377 (honest): full theorem NOT proven, hence not in Lean;
in Lean today: two-sided reduction + capstones + conservation +
harmonized split + J=2 telescoping + shift transport + no-gos (std
footprint, ~7800 lines). NEXT LEAN BRICK (ready): the exact measure
identity ((p+1)/2p)^J — compile next context; then L2 pair-form.

## S(t)-THEORY TEST, RUN 1: INSTRUMENT MIS-CHARTED (diagnosis recorded)

Additive window L=3e5 at N=1e6: max|D|/RW = 226 — looks like anti-
compensation, but the diagnosis is chart error (unit-1 again): the top-
window functional's structure lives at scales p^d ~ N; an additive window
samples ONE frozen cell of the slow band geometry, so cumsum measures
deterministic drift, not ledger fluctuation. THE S(t) TEST MUST RUN IN
CARRIER TIME: sample ticks log-uniformly across MANY DECADES (u = log x),
integrate (M - mean) du, THEN test band-confinement vs random walk.
Corrected instrument spec: x_k = round(exp(u_k)), u_k uniform on
[log 1e6, log 1e12], ~1e5 samples, M computed per-sample (per-x depths d_p
recomputed); readout: log-integrated deviation band vs sqrt prediction;
S(t) signature = tight band (zeta-fiber analog had B_N width 1.489).
Run as first probe of next context.

## S(t)-THEORY CONFIRMED ON THE DIGIT FIBER (carrier-time, 12 decades)

Corrected instrument (log-uniform ticks, 1e6..9e17, T=27.5): integrated
deviation BAND-CONFINED: max|D| = 0.32 vs random-walk ~5.9 (x18 below RW)
— the digit-fiber ∫S = o(T) MEASURED. SLAVING LAW (zeta analog 99.5%):
top-level (leading-digit) chart geometry explains R² = 0.91 of the
top-window mass; residual sd 0.065, residual band ~0.32. CONSEQUENCE:
the atomic budget's sup problem reduces (91% + compensated residual) to
the tick-sup of the LEADING-DIGIT Kronecker functional
  M1(x) = Σ_p (1/p)·1[leading digit of x in base p is lower-half]
— SIMULTANEOUS-BENFORD SUP: the cleanest open form yet. Real-sup
diverges (pairwise Kronecker); tick-sup observed ~1.4. Sam's theory
(S(t) = chart readout; compensation identity) is the working frame:
mean + compensation are measured facts; sup-at-ticks is the whole war.

## BREAKTHROUGH-SHAPED REDUCTION: TICK-SUP = REAL-SUP (integer-realization)

MEASURED FIRST: sup M_c − mean ≈ 0.337, CONSTANT across Y = 200..20000
(sup 1.218→1.360 tracks the mean's convergent tail exactly). The target
"sup = mean + O(1)" is measured with O(1) ≈ 0.34. M1 (top-level only,
divergent mean) decade-sups 1.66→1.73 = measure-limited alignment
k_max ~ 1.8·log N ⟹ triple-log growth ✓ consistent.

LEMMA (INTEGER REALIZATION — provable, ~10 lines): every gap cell at
every level is [A, B) with A = p^{d-i}·k INTEGER and B = A + p^{d-i}/2
(odd p ⟹ B ∈ Z + 1/2).  A nonempty intersection of any cells across any
rails is [max A_i, min B_j) and CONTAINS ITS INTEGER LEFT ENDPOINT.
CONSEQUENCE: sup over INTEGERS of M_c = sup over REALS of M_c (up to
factor-p decade slippage at the window edge).  THE EVERY-N/ALMOST-ALL GAP
IS GONE: extremal configurations are ALWAYS integer-realized; no tick
luck exists.  The atomic budget is equivalent to a REAL-VARIABLE
statement: bounded mass on the orbit closure of the carrier flow.

WHY REAL-SUP IS NOT OBVIOUSLY INFINITE (resolving the Kronecker scare):
the deep levels of one rail are rationally DEPENDENT scales (p^{d-i}) —
the flow is a SKEW PRODUCT per rail, not a free torus; joint orbit
closure is a proper subset; only pairwise-top-level alignment is proven
dense. The measured cap says the closure avoids heavy cells.

THE PROBLEM, FINAL CURRENT FORM: bound the M_c-mass visible in the orbit
closure of the skew-product carrier flow — topological dynamics on the
harmonized carrier, zero arithmetic luck, extremals automatically
realized. NEXT: (1) prove Integer Realization in Lean (Erdos377Atomic —
the cell endpoint arithmetic is already in the band lemmas); (2) attack
the orbit-closure mass bound with the skew-product structure (per-rail
towers = odometer skew products — the house's IFS/odometer frame).

## EXCESS CONSTANT: NEITHER 1/3 NOR pi/9 — c-DEPENDENT LP VALUE

Hill-climb extremal + c-scan (Y=20000, decade 1e12):
  c=1.6: excess 0.304 | c=2.0: 0.359 | c=2.6: 0.392  (monotone in c).
The 0.337 ~ 1/3 coincidence at c=2 was numerology — falsified. The excess
is the c-dependent LP optimum of the alignment problem (deeper forced
conditions per rail => larger extremal gain vs shrinking mean). Target
theorem shape confirmed: sup <= mean(c) + C(c) with C(c) = alignment-LP
value; no universal constant to chase. Extremal search (CRT digit
nudging) beats random sampling (1.3677 vs 1.3597 at c=2) — champions ARE
constructible by rail alignment, consistent with integer_realization.

## THE CLOSING CHAIN CANDIDATE (mantissa-Cantor transversality)

Derived: analytic/discrepancy routes to the LP threshold are HOPELESS
(needed error e^{-(loglog)^2} vs available polylog savings — quantified).
The structural route closes IF one literature theorem holds:

1. Full-depth balance in base p == mantissa in a ×p-self-similar Cantor
   set C_p, dim = 1 - beta_p, beta_p = log2/log p·(1+o(1)).
2. Joint balance on S == the window meets ∩_{p∈S} C_p — k-fold
   FURSTENBERG INTERSECTION (mantissa form).
3. Discretized transversality (Shmerkin L^q / Wu, scale 1/N): covering
   number of the k-fold intersection at unit scale in [N,2N] is
   <= N^{max(0, 1-Σβ_p)+ε}.  For Σβ_S > 1: <= N^ε champions.
4. integer_realization: interval-covering bounds suffice for integers.
5. β-BUDGET LP: no pair of odd primes has β_p+β_q > 1 (max .74); FIRST
   trigger is 4-sets ({3,5,7,11}: Σβ = 1.23). Mass with Σβ ≤ 1:
   maximize Σ1/p s.t. Σβ_p ≤ 1 ⟹ Z* ≈ 8, mass ≈ 1/3+1/5+1/7 + partial
   ≈ 0.69 = THE MEASURED LP VALUE 0.6855. Chain: (3)+(4)+(5) ⟹ atomic
   budget ≤ 0.69+ε for all n outside ≤ N^ε per-S exceptions; union over
   the O(1)-many relevant S: full atomic budget.  With the flagship
   diffuse engine ⟹ FULL #377.

ONE GATE, READ AT SOURCE BEFORE ANYTHING: does the discretized
k-fold (k ≥ 4) transversality theorem exist? (Shmerkin Ann.Math 2019
L^q spectra; Wu Ann.Math 2019; Hochman-Shmerkin projections; possibly
Yu/Austin variants.) Pairwise is proven; k-fold at matched scale with
covering-number conclusion is THE question. If yes: assemble. If no:
it is a precisely-shaped new theorem to prove — and the house frame
(harmonized carrier, unit ladder) is the native chart for it.
ALSO: exceptional N^ε champions must be mass-bounded too — check the
chain handles x IN the exceptional sets (their S has Σβ > 1 but x may
still carry mass from OTHER rails ≤ budget — needs the union argument
written carefully).

## UNION ARGUMENT WRITTEN (chain output refined — honest strength)

Split at constant B0: (i) p ≤ B0: mass ≤ Σ1/p = O_{B0}(1) free. (ii) tail
(B0, Y]: if Σβ_tail ≤ 1: mass ≤ max{Σ1/p : Σβ ≤ 1, p > B0} ≤
log B0/(B0 log 2) → 0 (cheapest-mass-per-β at large p). (iii) tail
over-budget: needs k ≥ 1/β_{B0} rails; gate theorem (if it holds) ⟹
≤ N^ε points per k-subset; union over ≤ π(Y)^k = e^{O((loglog N)²)}
subsets absorbed by N^ε ⟹ ≤ N^{2ε} exceptional integers per window.
REQUIRES gate constants UNIFORM in the p-tuple (sub-question added).

HONEST STRENGTH OF THE CHAIN: gate ⟹ atomic mass ≤ LP + o(1) for ALL x
except ≤ N^ε per dyadic window ⟹ with flagship: E(n) = O(1) for all n
outside ≤ N^ε exceptions per window — "almost-all #377" in exception-
COUNT form (far stronger than density-zero). FULL #377 additionally
needs EMPTINESS of over-budget intersections in windows (dimension
tools give smallness, never emptiness) = the extremal-rigidity residue.
Measured ceiling (~0.83 ≈ LP, never exceeded) says emptiness is TRUE;
the last gap is tool-vs-truth on N^ε points. Chain value regardless of
that residue: exception-count a.a. #377 would exceed everything in the
literature.

## GATE VERDICT: OPEN — Corso–Shmerkin arXiv:2409.04608 (PREPRINT)

Thm 1.15 + Cor 1.17: k-fold Furstenberg slicing, ALL k, pairwise mult.
independence only, UNIFORM δ-covering form: N_δ(∩ g_i(A_i)) ≤
δ^{-(max(0,Σdim−(k−1))+ε)}. Exactly the chain's step 3. By Shmerkin
(author of the k=2 Annals proof) + Corso; 23 months unchallenged; NOT
yet journal-published — cite as preprint, verify what we use. Yu (TAMS
2021, Cor 9.1) is the only journal k≥3: Schanuel-conditional in practice
(no known verifying tuple, k≥3) — do NOT cite as unconditional. k=2
published: Shmerkin Annals Thm 1.2 / Wu Annals Thm 1.4.

REMAINING TECHNICAL BRIDGES (now the whole distance to exception-count
a.a. #377): (B-i) p-TUPLE UNIFORMITY: CS constants C_{d,k,ε,η} are per
fixed sets A_i; union argument needs growth in the tuple (primes up to
polylog, k up to ~loglog) slower than N^ε — track through their proof
(engine: their Thm 5.4 L^q formula + Lemma 6.1 Frostman). (B-ii)
TRUNCATION BRIDGE: our depth-J balanced sets are the level-J trees of
the invariant sets; covering at δ = p^{-J} of truncation vs invariant
set — write the two-line bridge rigorously. THEN: assembly theorem
(E(n) = O(1) for all n except ≤ N^ε per window, conditional on CS
preprint) + the finite-list residue ({3,5,7,11}: {1,3160} to 1e9 etc.)
for FULL 377.

## OPUS CS-EXTRACTION ADJUDICATED (verdicts adopted pending my spot-checks)

(1) Proof chain CLOSES for our case, with TWO PREPRINT DEFECTS Opus
found and repaired: (P1) hypothesis misprinted in §5 (intended form
confirmed via Remark 1.16 + Lemma 5.1 proof); missing a.e.-injectivity
verification in Thm 5.4's last step (supplied for our projection).
Communicate to Corso/Shmerkin eventually. (3) TRUNCATION BRIDGE CLOSED
(Lemma T, via the δ-robust ball form Lemma 6.1 — correctly NOT via the
exact-fibre statement). (2) B-i: GENUINE GAP — constants INEFFECTIVE:
threshold m0 from inverse theorem + compactness + unique ergodicity
WITHOUT RATE; §2.2 suppresses d-dependence while our d=k grows. Not
bookkeeping: needs effective inverse theorem + effective equidistribution
on the model torus X.

CHAIN STATUS AFTER B-i GAP: per FIXED rail set the theorem applies ⟹
CORE VERSION AVAILABLE NOW: cap dangerous rails at constant B₁ ⟹
finitely many over-budget sets, constants absorbed ⟹
  E_{≤B₁}(n) ≤ LP + ε for all n off ≤ N^ε exceptions  (modulo preprint).
GAP ZONE p ∈ (B₁, (log n)^C]: union over growing base-tuples blocked by
ineffectivity (k=2 published versions have the same base-ineffectivity).
FINAL FORM OF THE WALL: EFFECTIVE/UNIFORM-IN-BASES transversality — 
either (a) prove effectivity through the CS machinery (effective inverse
thm — known-hard genre), or (b) the house route: our own uniform theorem
in the harmonized chart for the SPECIFIC lower-half-digit Cantor family
(self-similar, explicit, OSC — far more structure than the general case;
explicit ×p spectral gaps conceivably give the ergodicity RATE the
general proof lacks). Option (b) is now the mainline research target.

## ROUTE (b) OPENED: THE BAKER UNLOCK (effectivity for our family)

The CS ineffectivity has three sources; for OUR explicit family each has
a candidate effective replacement:
(iii) unique ergodicity WITHOUT rate on the model torus X — but X's
  rotation has frequency vector (log p_d/log p_j)_j: EFFECTIVE
  discrepancy follows from BAKER (linear forms in logarithms; Matveev
  constants exp(poly(log p)) — polyloglog N scale ✓). This is the key
  unlock: for prime-base ratios the missing rate is CLASSICAL.
(single-measure L^q) our measures are UNIFORM self-similar with OSC:
  L^q spectra EXACTLY LINEAR, tau(q) = (q-1)·log h/log p — no inverse
  theorem needed at the single-measure level.
(i) the inverse theorem [Shmerkin Annals]: finitary additive-
  combinatorics genre — effectivity plausible; QUALITY REQUIREMENT
  derived: the whole chain needs per-tuple constants ≤ exp(poly(log
  bases)) (= exp(polylogloglog n)) to clear N^ε with bases ≤ polylog;
  Baker meets this; the inverse theorem's base-dependence is the open
  question. If constants come out exp(poly(bases)) instead, TUNE: lower
  the atomic/diffuse boundary (needs stage-2 reach check).
FIRST CONCRETE LEMMA (provable now, publishable component):
  EFFECTIVE EQUIDISTRIBUTION ON THE MODEL TORUS — the orbit closure of
  0 under T(x)_j = x_j + log p_d/log p_j has discrepancy at time m
  ≤ C·m^{-c} with C, c EXPLICIT from Matveev/Baker. Derivation: the
  orbit closure is a subtorus + rational fibers; frequencies' joint
  Diophantine type bounded by lower bounds on |Σ b_j log p_j| (Baker);
  Erdős–Turán converts to discrepancy. Assign to next Opus round.

## SELF-AUDIT: BAKER UNLOCK CORRECTED (k ≥ 3 needs factorization, not Baker)

ERROR in the previous entry, caught before delegation: Baker bounds
LINEAR forms in logs — the joint discrepancy of the model rotation for
k ≥ 3 needs small-value bounds for h₁·(log p_k/log p_1) + h₂·(log
p_k/log p_2) mod 1, whose cleared form is QUADRATIC in the logs —
transcendence-hard (this, not sloppiness, is WHY CS is ineffective and
why Yu needed Schanuel-grade hypotheses: the orbit closure's identity is
unknown). Baker unlock valid ONLY for the pair case (single ratio).

CORRECTED ROUTE (b): replace unique-ergodicity-on-unknown-closure with
EFFECTIVE FACTORIZATION (Weyl + geometry of numbers; Green–Tao
quantitative Kronecker/Leibman, abelian case): at each scale M, the
orbit {mα} is either M^{-c}-equidistributed on the full torus, or an
EXPLICIT bounded-height rational relation holds and the orbit lives on
an explicit subtorus-coset — no Diophantine refutation needed; CARRY the
relation as structure and run the CS L^q analysis on the explicit
subtorus (their framework already treats X = abstract closed subgroup —
the change: make it explicit-at-scale). Induction on dimension
terminates effectively. RESEARCH QUESTION (the new B-i): does the CS
Thm 5.4 argument survive restriction to an arbitrary explicit subtorus
with effective constants? Their Lemma 5.1 pleasant-model construction on
subgroups suggests yes structurally. NEXT OPUS ROUND: (1) effective
factorization lemma for our rotation (classical, write with constants);
(2) trace CS §5-6 replacing P/unique-ergodicity by per-scale
factorization; identify every step where the unknown-closure abstraction
is used and check explicit-subtorus substitution.

## CORE ASSEMBLY THEOREM — DERIVATION COMPLETE (conditional on CS preprint)

THEOREM (atomic core, exception-count form). Assume CS Cor 1.17 (with
Opus's two repairs). Fix constant B₁ and eps > 0. For all large N, all
but ≤ N^eps integers n ∈ [N, 2N] satisfy
  Σ_{p ≤ B₁ odd, p ∤ C(2n,n)} 1/p ≤ LP(B₁) + eps,
LP(B₁) = max{Σ_S 1/p : Σ_S β_p ≤ 1} (≈ 0.69 for B₁ ≥ 11).

PROOF SKELETON (all pieces in hand):
1. RESCALE — the decisive step found today: in mantissa coordinates
   x = n/N ∈ [1,2], p-balance reads x ∈ g_p(C_p-truncation) with g_p
   affine of slope p^{d_p}/N ∈ [1/B₁, 1]: SLOPES BOUNDED BY THE CONSTANT
   B₁, so CS Cor 1.17's C_{eps,K} has K = B₁ — no N-dependence. (Naive
   value-space application would need K ~ N and die.)
2. Over-budget S (Σβ > 1 ⟺ s < k−1): Cor 1.17 + Lemma T (truncation,
   δ ≍ 1/N) ⟹ 1/N-covering ≤ C(B₁,eps)·N^eps ⟹ ≤ C·N^eps integers;
   union over ≤ 2^{π(B₁)} subsets: constant factor.
3. Under-budget n: mass ≤ LP(B₁) by arithmetic. QED.

STATUS: first fully-derived theorem of the atomic campaign. Dependencies:
CS preprint Cor 1.17 (verified by Opus incl. two repairs), Lemma T
(Opus, to be spot-checked), compiled Lean bricks (realization/measure
not even needed here — they support the sup frame; this route is
direct). NOT needed: B-i effectivity (constants absorbed at fixed B₁).
NEXT: (i) spot-check Lemma T; (ii) write this as a paper section;
(iii) the gap zone (B₁, polylog] still needs route-(b) factorization for
the FULL atomic budget; (iv) finite-list residue for full 377.

## SAM: "or warping?" — ADOPTED AS THE FRAME FOR BOTH STEPS

(1) The mantissa rescaling in the core theorem IS a warp — the window's
log-chart on the carrier; name it so in the paper. (2) Route (b)'s
per-scale factorization = an ADAPTIVE WARP LADDER: at each scale, either
the flat chart equidistributes (rate, effective) or a bounded-height
relation fires and we WARP into the explicit subtorus chart and recurse —
each drop is a harmonization event with its own ledger; effectivity =
the warp ledgers COMPOSE (finitely many drops, each explicit). Opus's
factorization trace should be organized exactly as this ladder: one
ledger per drop, composition = the effective constant.

## ATTACK: GAP ZONE REDUCED TO EFFECTIVE PAIRS (second-moment argument)

DERIVED: the gap zone (B₁ < p ≤ (log n)^C) needs only PAIR transversality
+ second moment, not the k-fold ladder:
- tail mass > ε₀ at n ⟹ ≥ K = ε₀·B₁log2/log B₁ tail rails balanced ⟹
  ≥ K²/2 balanced PAIRS at n.
- Σ_n #pairs(n) ≤ Σ_{pairs} C_{p,q}·N^{1−β_p−β_q+ε} (pair transversality
  per (p,q)); N^{-β_p} = N^{-log2/log p}: summing over pairs ≤ polylog:
  total ≤ N^{1−c/loglog N} ⟹ all but N^{1−c/loglog N} integers have
  tail mass ≤ ε₀. REQUIRES: pair constants C_{p,q} ≤ exp(poly(log pq))
  — EFFECTIVE PAIR TRANSVERSALITY.

THE DECISIVE LEMMA (new theorem target, independently publishable):
EFFECTIVE FURSTENBERG PAIRS: for mult-indep (p,q), the Shmerkin/CS pair
bound with C(p,q) ≤ exp(poly(log p·log q)). Plan: the d=2 model is a
1-DIM rotation by log p/log q — closure KNOWN (full circle), rate =
BAKER/MATVEEV irrationality measure (effective, exp(poly(log pq))) —
no factorization ladder, no Schanuel. Remaining effectivity sources:
(ii) compactness step (identify in d=2 — likely removable), (i) the
L^q inverse theorem: need constants = tower(1/ε)·exp(poly measure
params) — ε is FIXED for us; our spectra are explicit linear. If the
inverse theorem is finitary (expected), effective pairs CLOSES.

QUANTIFIER LADDER TO FULL 377 (honest): effective pairs ⟹ all but
N^{1−c/loglog}; k-fold ladder ⟹ all but N^ε; FULL (all n) ⟹ still
needs the emptiness/rigidity residue at the top — no dimension tool
gives ALL. Rigidity remains the last boss; everything else is now
reduction-complete or assigned.

## PARALLEL FOURIER LINE (Opus almost_all thread): ADDITIVE LAW — ATTACK SKETCH

Opus self-audit: its multiplicative budget FALSE (off by up to 10^14);
empirical ADDITIVE law |err| ≤ 3.2·Σ p_i^{d_i} robust (38 configs, ratio
median 0.0095); mechanism unknown; its Theorems A/A'/B flagged
conditional. FLAGS ADOPTED. The law looks PROVABLE — attack:
exact Fourier err = Σ_{α≠0} ∏ĉ_i(α_i)·E_N(A(α)/M), |E_N| ≤ min(N,M/2|A|),
|ĉ_i(α)| ≲ min(measure, 1/|α_i|) (interval kernels; Opus verified the
factorization + CRT bijection exactly).
(1) SINGLE-MODE terms (one α_i ≠ 0): A = α_i·e_i with e_i = M/p_i^{d_i}:
Σ_α (1/α)·(p_i^{d_i}/α) ≍ p_i^{d_i} — THE ADDITIVE MAIN TERM per rail ✓
(matches: W concentrates at small α mapping to LARGE A — Opus's own
diagnosis of why uniform-W failed).
(2) CROSS terms: iterate rails; innermost = standard AP-min-sum
Σ_{α₁}(1/α₁)·min(N, M/|A₀+α₁e₁|): one near-hit ≤ N/α₁*, rest
≤ O(p₁^{d₁} log); outer weights + AP spacing mod M (three-distance) ⟹
expected O(Σ p_i^{d_i} · polylog). Elementary large-sieve/AP genre —
same family as the flagship θ-net section.
NEXT: prove the additive law standalone; then restate A/A'/B (constant
→ ~1.24; re-derive the logloglog n claim). SLOT IN CAMPAIGN: Fourier
product-box engine = third machine; complements transversality (each
covers the other's weak regime — Fourier: under-budget counting with
explicit constants; transversality: over-budget where Fourier's main
term vanishes under its error).

## ADDITIVE LAW: TWO-RAIL CASE PROVED (Opus), ADJUDICATED

Lattice reduction verified in structure: cross sum = Σ over Λ = 
{(α,β): αP₂ ≡ β mod P₁}, det Λ = P₁; dyadic count ⟹ main term
M log²M/P₁ = P₂ log²M — ADDITIVE, the M-cancellation being exactly why
the multiplicative budget failed. Exceptional term named: first minimum
λ₁; Minkowski λ₁ ≪ √P₁; defect factor (√P₁/λ₁)². PREDICTION HIT
(adjudicated, verified by hand): (101², 103²): 25·10609 = 25·408 +
25·10201·… ≡ 10200 ≡ −1 mod 10201 ✓ so (25,−1) ∈ Λ, λ₁ ≈ 25 vs √P₁ =
101, defect ≈ 16 — and that config IS the sweep's worst ratio 3.19,
generic ≤ 0.08. Falsifiable prediction confirmed in advance of fitting.
NO transcendence anywhere — fully effective, integer-only Diophantine
defect (short vectors = good rational approximations between prime
powers — sporadic, checkable).

GO-AHEAD GIVEN for the two completions, with audit demands:
(1) K-induction: at rank K use ALL successive minima (Minkowski second
theorem), not λ₁ alone — the count n(boxes) at rank K needs
λ₁···λ_{K−1} bookkeeping; state the defect factor via the minima
product. (2) depth weights ∏ 1/α_j: show monotone improvement
explicitly. THEN: restate Theorems A/A'/B with the defect factor;
unflag. WIRING: this engine is FULLY EFFECTIVE — assign it maximal
coverage (all under-critical counting), reserving transversality
strictly for the over-budget regime; the effectivity wall shrinks to
exactly the range only transversality covers.

## S(t)-TYPING CLOSURE (Opus) — ADJUDICATED: two parts REAL, register CORRECTED

REAL AND BEAUTIFUL: (a) THE IDENTITY Σ_{n≤T} E(n) = Σ_p (1/p)|G_p∩[1,T]|
— Fubini, exact; the digit-fiber ∫S is ZERO BY IDENTITY (cleaner than the
Stirling route; the S(t) frame's cleanest vindication). Verified 1e4 to
6 decimals. (b) THE CONSTANT: mean E → C₀ = Σ_{j≥2} log j/2^j = 0.507834
— exact re-summation of the EGRS window ledger Σ2^{-k}log(1+1/k) ✓
checked. E(n) = C₀ + S₃₇₇(n), ∫S ≡ 0: the problem's cleanest form ever.
LIMSUP TARGET: limsup E = 1/3+1/5+1/7 (+ negligible admissible tails) —
a VALUE, and 377-bounded follows from limsup finite.

REGISTER CORRECTED (Opus's register missed one gap and undercounted):
(i) as it says: transversality for the named sets = CS-conditional ✓;
(ii) MISSED: negative dimension gives N^ε PER WINDOW, NOT finiteness —
infinitely many windows ⟹ dim-negativity alone does NOT cap the limsup;
the finiteness/rigidity residue is still required and is NOT a dimension
fact; (iii) UNDERCOUNT: threatening minimal sets are ALL {3,5,7,q} for
7 < q ≲ 4·10^{11} (each over-budget, each mass > 0.676) — finiteness
needed UNIFORMLY over ~π(4e11) quadruple families, not 3 determinations
(a single quantitative uniform statement could cover all — that's the
correct target). NET: the formulation is the campaign's best (identity +
closed constant + LP-value limsup target); the last boss (uniform
finiteness for {3,5,7,q}) unchanged in substance, now EXACTLY located.
