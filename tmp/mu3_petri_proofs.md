# mu_3 Prym-Petri: what is proven as of 2026-07-18, with proofs

Setting: pi: C~ -> C etale cyclic Z/3, sigma the deck action, eps in Pic^0(C)[3]
the defining class, g = g(C) >= 2, Nm: Pic(C~) -> Pic(C) the norm.  For
L in Nm^{-1}(omega_C), the Petri multiplication
  alpha_L : H^0(L) (x) H^0(omega_{C~} (x) L^{-1}) --> H^0(omega_{C~})
and the anti-invariant projection pr: H^0(omega_{C~}) ->> H^0(omega_C eps) (+)
H^0(omega_C eps^2).  Write beta_L = pr o alpha_L (the naive mu_3-Prym-Petri map).

## Lemma 1 (the invariant kernel line; general — the battery's discovery).

For EVERY (C, eps, L) as above and every nonzero s in H^0(L), the map beta_L
kills a canonical direction:

  Let D = div(s) (effective, degree 2g-2, with Nm(D) := pi_*(D) in |omega_C|).
  Let eta be the unique-up-to-scale differential on C with div(eta) = pi_*(D).
  Then pi^*eta / s is a global section of omega_{C~} (x) L^{-1}, and
      alpha_L( s (x) (pi^*eta / s) ) = pi^*eta,
  which is sigma-invariant; hence s (x) (pi^*eta/s) in ker(beta_L).

Proof.  For any effective divisor D on C~ one has D <= pi^*pi_*(D) pointwise
(each point of D appears in the pullback of its image with multiplicity >= its
own).  Hence div(pi^*eta) = pi^*(pi_* D) >= D = div(s), so pi^*eta/s is regular,
i.e. a section of omega_{C~}(-D) (x) O(D) = omega_{C~} (x) L^{-1}.  Its Petri
product with s is pi^*eta, which lies in the sigma-invariant summand
H^0(omega_C) of H^0(omega_{C~}); the anti-invariant projection kills it.  QED.

Consequence (the correct definition): the mu_3-Prym-Petri map is
  beta-bar_L : ( H^0(L) (x) H^0(omega L^{-1}) ) / T_L --> H^0(omega eps)(+)H^0(omega eps^2),
with T_L the (h^0(L)-dimensional, generically) subspace spanned by the elements
of Lemma 1 over a basis of H^0(L).  This is the exact mu_3-analogue of passing
from (x)^2 H^0(L) to Lambda^2 H^0(L) in Welters' Z/2 theory: there the removed
directions are s (x) iota(s)-symmetric; here they are the norm/trace lines.
[Empirical confirmation: 14/14 exact samples at g = 4, p = 7: rank(alpha) full,
ker(beta) exactly T_L, beta-bar injective.]

## Theorem A (openness; Welters 2.1 transposed).

Let (Cal C, Cal C~) -> T be smooth projective families of curves over a
k-scheme T with an etale Z/3-morphism Cal C~ -> Cal C.  The set of t in T such
that the mu_3-Prym-Petri condition FAILS for the fiber (i.e. some
L in Nm^{-1}(omega) has beta-bar_L non-injective) is closed.

Proof (Welters' argument verbatim, mu_3 constants).  May assume T = Spec of a
DVR, condition failing at the generic point eta; must show it fails at the
special point 0.  After base change there is a line bundle L_eta on the generic
fiber with Nm(L_eta) ~ omega and beta-bar non-injective; L_eta extends to L on
Cal C~ with Nm(L) ~ omega_{Cal C/T} (properness of the relative Nm^{-1}(omega),
a torsor under the relative Prym).  R^0 of L and of omega L^{-1} are free
O_T-modules with base-change injections (R^0 L)(0) into H^0(L_0) (Welters 2.2);
the relative beta-bar is a morphism of free O_T-modules (the invariant
sub-line of Lemma 1 is itself a free rank-h^0 subsheaf, since it is defined by
the closed condition of Lemma 1 fiberwise and the relative eta-differential
exists after base change), non-injective at eta, hence non-injective at 0;
by the base-change injections the same holds for the special fiber.  QED.

Remark: properness of Nm^{-1}(omega) over T also gives, by the standard image-
of-proper-is-closed argument, the quantifier upgrade: the locus
{ t : EVERY L in the fiber has beta-bar injective } is OPEN.  Hence:

## Reduction B (one full member suffices).

If a single pair (C_0, eps_0) over an algebraically closed field satisfies the
condition for ALL L in Nm^{-1}(omega_{C_0}), then the generic (C, eps) of that
characteristic satisfies it for all L.  (Openness + irreducibility of the
moduli of pairs (C, eps), the latter by mapping-class transitivity on primitive
Z/3-classes — the same fact used for the integral models.)

## What is NOT yet proven (the named remainder).

The existence of one full member: verification at a single (C_0, eps_0) must
cover ALL L with h^0 >= 1 (a positive-dimensional family), which finite
sampling cannot exhaust.  Welters achieves it degenerately: a chain of
rational curves with elliptic bridges, where limit-linear-series combinatorics
verify every L at once.  The mu_3 version — elliptic bridges carrying points
of exact order 3 (P - Q of order 3 in each bridge, the Z/3-analogue of his
Z-independence conditions) — is work item W1-final.  It is a bounded
Eisenbud–Harris-style analysis, not done here; until it is done, the theorem
is: Lemma 1 + Theorem A + Reduction B + exact injectivity at every sampled
member (14/14, one prime, h^0 = 1 stratum).  No stronger claim.

## W1-final: the degeneration design, in the multi-rail frame (2026-07-18)

Welters verifies his one-full-member at a chain: rational spine, g elliptic
bridges E_i carrying the 2-torsion data.  The mu_3 transposition lands squarely
in house territory:

* Per-bridge unit = an elliptic curve with a point of EXACT ORDER 3 (eps_i in
  E_i[3] \ 0), whose etale Z/3-cover is a 3-isogeny — precisely the object
  (E0, T), div(y) = 3T - 3O, the magic function, the descent character kappa)
  that every instrument this week was built on.  The degenerate verification
  decomposes into per-bridge elliptic computations our machinery does exactly.
* The cover of the chain = 3 sheets of the spine glued through the bridge
  isogenies; connectivity = the eps_i-translations mix the sheets.  The
  sigma-isotypic pieces per bridge are the RAILS; the chain concatenates them.
* Limit linear series stratify sections by vanishing orders that increase
  strictly along the chain: the limit Petri matrix is TRIANGULAR with respect
  to this filtration, with per-bridge rail-blocks on the diagonal.  Injectivity
  of beta-bar at the chain = (a) nonvanishing of each diagonal rail-block
  [a per-bridge elliptic 3-torsion computation], plus (b) the strict-order
  triangularity [the layerwise-separation / Vandermonde pattern — the exact
  argument shape of momentTower_detects in the Lean corpus].
* THE CRUX (named, unresolved): the twisted limit differentials.  On a single
  bridge, h^0(E_i, eps_i^{\pm 1}) = 0 — the anti-invariant rails carry no
  sections per component; the twisted canonical limits concentrate at nodes
  with pole/vanishing bookkeeping along the spine.  Determining the RAIL
  OCCUPANCY ALONG THE CHAIN for the eps- and eps^2-twisted limit canonical
  systems is the technical heart (the Z/2-analogue is inside Welters Sec. 2);
  it decides which diagonal blocks exist and what "exact order 3" must exclude
  (the mu_3-analogue of his Z-independence of P - Q).

Two next moves, in order:
1. NUMERICAL E-H PROBE: build an explicit near-chain mu_3-cover over F_q
   (nodal or epsilon-smoothed; the engine already handles nodes) and run the
   battery ON the degenerate configuration — read the rail occupancy and the
   diagonal blocks empirically before the hand-proof, exactly as the h^0=1
   battery discovered Lemma 1 before it was a lemma.
2. The paper derivation of the twisted-limit occupancy (Eisenbud-Harris with
   the 3-torsion twist), per-bridge conditions extracted, then the triangular
   assembly.  Register: W1-final is DESIGNED, not proven; the design reduces
   it to one occupancy computation plus house-pattern arguments.

## Probe 1 RESULT: the occupancy is FLAT and TAIL-NESTED (2026-07-18)

Instrument: tmp/chain_occupancy.sage — the chain itself over F_7 (tree:
rational spine, g bridges = copies of E0 with eps_i = [T - O]); per-bridge
L(P_i + Q_i + jT - jO) computed exactly (12-monomial pool over the
denominator (x-x_P)(x-x_Q), conditions at conjugates + T/T'/O; per-bridge
h^0 = 2 gate passed in every run); global sections of omega_0 eps^j by
residue matching at the nodes (tree => eps glues trivially).  g = 2, 3;
j = 0, 1, 2; 4 random attachment configurations each, PLUS a targeted
exclusion probe with Q_i = P_i (+) T (attachment difference inside <eps_i>).

Findings, uniform across ALL 36+ configurations:
(a) NO h^0 JUMP: dim H^0(omega_0 eps^j) = g (j=0) and g-1 (j=1,2) — exactly
    the smooth values, for every attachment configuration tried, INCLUDING
    the eps-aligned Q = P (+) T ones.  The twisted limit canonical systems
    are flat at the chain; no Eisenbud-Harris crutches needed for the
    AMBIENT spaces of the Petri target.
(b) TAIL-NESTED SUPPORT (the filtration, empirically): the j=0 basis is
    per-bridge diagonal (classical differentials, one per bridge, rationals
    empty).  For j != 0 the g-1 sections stratify by support tails:
    bridges {0..g-1} > {1..g-1} > ... — the vanishing-order filtration of
    limit linear series, visible as nested occupancy.  Every global twisted
    section is CHAIN-SPREAD (couples through the interior rationals' dz/z),
    entering each bridge through its T-pole rail direction (v_T fingerprints:
    j=1 basis = one function with v_T = -1 + one regular; j=2 = orders
    -2, -1; the surviving global sections always use the polar/rail entry).
(c) EXCLUSION PROBE NEGATIVE AT THE AMBIENT LEVEL: even Q = P (+) T gives
    no jump and no occupancy break.  CONSEQUENCE — the crux MOVES: the
    mu_3-analogue of Welters' Z-independence does NOT live in the twisted
    canonical systems (all diagonal blocks of the limit Petri matrix exist,
    unconditionally); it must live in the Petri PRODUCT itself — which
    limit L in Nm^{-1}(omega) pair nontrivially against these flat targets.
    (Same locus as in Welters: his conditions constrain the limit linear
    series on the SOURCE side, not omega.)

Caveats: one small prime (F_7, only 6 usable affine points, samples overlap);
smooth values could still be checked at a second prime / larger field cheaply.

## Novelty check (2026-07-19, per the hard rule — literature at source)

Five independent sweeps, none finds a Prym-Petri theorem for cyclic covers of
degree >= 3:
1. arXiv "Prym AND Petri": only Z/2 extensions of Welters — Tarasca
   (2202.05284, pointed), Jeon (2309.02642, two-pointed).
2. arXiv "Prym-Brill-Noether": Bud (ramified DOUBLE covers, universal locus,
   divisor class), tropical school (Len-Ulirsch, Creech-Len-Ritter-Wu,
   Jensen 2607.01173 — "general covers" = double covers of k-gonal/k-elliptic
   bases, disproves the CLRW dimension conjecture).  All degree 2.
3. Nearest neighbor READ AT FULL TEXT: Schwarz 1603.05084 "Brill-Noether
   theory for cyclic covers" — existence/gonality of linear series on the
   COVER curve via Plucker + E-H limit linear series on tree-like admissible
   Z_n-covers.  NO Petri map, NO norm map, NO Prym V^r, no tangent-space or
   smoothness statements.  (Her degeneration frame is a method precedent for
   our chain — cite it.)
4. arXiv "triple cover AND Prym": Lange-Ortega orbit = structure theory of
   the Prym map for triple covers (0911.5224, 1103.4982, 1309.6984); no
   Brill-Noether, no Petri.  "Petri map AND (cyclic OR torsion)": 0 results.
5. COMPLETE citation graph of Welters 1985 (OpenAlex W120851013, all 80
   citing works, titles scanned): zero cyclic-degree->=3 generalizations;
   everything is classical Z/2 Prym theory.

Verdict: the mu_3-Prym-Petri statement (and Lemma 1's norm/trace-line domain)
appears to be NEW.  Residual risk, stated: non-arXiv venues, papers not
citing Welters, or content buried in broader papers without Petri/Prym
metadata; OpenAlex coverage is good but not zbMATH-complete.

## THE PROOF, RESTRUCTURED (2026-07-19): descent + collision + base-BN

Discovery of the day: at h^0(L) = 1 the whole Petri kernel is DIVISOR
GEOMETRY ON THE BASE CURVE.  The cover, the rails, eps itself are consumed
by one lemma; what remains is a classical Brill-Noether exclusion with NO
mu_3 content.  This explains probe 1's negative exclusion result exactly
(no eps-condition exists to find), and it removes the need for the
admissible-cover chain machinery in the main theorem.

### Scope note (dimension accounting, h >= 2)

deg L = 2g-2, g~ = 3g-2, chi(L) = 1-g: h^0(L) = h forces
h^0(omega L^{-1}) = h+g-1.  For h >= 2 the reduced domain
h(h+g-1) - dim(forced kernel) EXCEEDS the target 2(g-1) unless the forced
kernel is enlarged: the full forced kernel is the span of the cyclic tensors
  x_{s,s',s''} = s (x) sigma*(s')sigma^2*(s'') + s' (x) sigma*(s'')sigma^2*(s)
                 + s'' (x) sigma*(s)sigma^2*(s'),
whose alpha-images are sums of three sigma-cyclically-permuted products,
hence invariant (this generalizes Lemma 1 = the case s=s'=s'').  At h=2 the
count balances exactly (2(g+1) - 4 = 2g-2); at h >= 3 injectivity is
dimensionally impossible and the right statement is rank-maximality.  The
theorem below is the h^0 = 1 stratum — the stratum the W2-W4 pipeline
consumes, and the one the battery verified.  h >= 2 = named extension.

### Lemma A (mu_3-reduction).  Setting: pi etale Z/3, char != 3,
L in Nm^{-1}(omega_C), h^0(L) = 1, s the section, W = div(s).
Define the max-descent D-bar = sum_x max_{y in pi^{-1}(x)} mult_y(W) . x,
and the collision excess E = pi_*W - D-bar >= 0 (supported in supp D-bar).
THEN:
  dim ker(pr o alpha_L) = h^0(omega_C - D-bar),   and since
  omega_C - D-bar ~ E   (because pi_*W = div(Nm s) in |omega_C|),
  ker(beta-bar_L) != 0  <=>  h^0(O_C(E)) >= 2  <=>  E MOVES.

Proof.  Every domain element is s (x) t (h^0(L)=1).  pr(alpha(s(x)t)) = 0
iff s.t lies in the sigma-invariant part of H^0(omega_{C~}), which is
pi*H^0(omega_C) (etale, char != 3, averaging).  s.t = pi*eta iff
t = pi*eta/s is regular iff pi*(div eta) >= W iff div eta >= D-bar
(pointwise: mult_x(div eta) >= max over the fiber).  So
{t : s(x)t in ker} ~ H^0(omega_C - D-bar), always containing eta_s = Nm(s)
(div = pi_*W >= D-bar), whose t is t_s = sigma*s . sigma^2*s — i.e. T_L.
Hence ker = T_L iff h^0(omega - D-bar) = 1, and the class identity
omega - D-bar ~ pi_*W - D-bar = E converts this to h^0(E) = 1.  QED.

Corollary A1: collision-free sections (E = 0) NEVER fail — explains the
smooth battery's 14/14 (random L are collision-free) and probe 1's flat
occupancy (there is no eps-condition; the exclusion lives in W's collisions).

### Lemma B (collision arithmetic).  At x with W-fiber multiplicities
(a,b,c), a = m_x = mult_x(D-bar), k_x = mult_x(E) = b+c, and b,c <= a give
k_x <= 2m_x, i.e. m_x >= ceil(k_x/2).  Hence the canonical divisor
K = pi_*W = D-bar + E satisfies
  K >= E + ceil(E/2),   ceil(E/2) := sum ceil(k_x/2).x .
So: FAILURE at some h^0=1 bundle  ==>  there exist a moving effective E and
a canonical divisor K with K >= E + ceil(E/2).  (For mu_n: k <= (n-1)m,
K >= E + ceil(E/(n-1)); n=2 gives K >= 2E — the statement is mu_n-uniform,
though for n=2 the h^0=1 stratum is vacuous, chi = 0.)

Conversely, any such (E, K) BUILDS a failing candidate W (distribute
multiplicities on sheets), with the one unchecked condition h^0(O(W)) = 1.
So Lemma C below is the exact remaining content, not just sufficient.

### Lemma C (base-curve exclusion — THE remaining content).
For C general in M_g: no moving effective divisor E and canonical K with
K >= E + ceil(E/2).  Equivalently (RR): for every moving E on a general
curve, the half-thickening F = E + ceil(E/2) is NONSPECIAL.

Status: the ARITHMETIC of the exclusion is complete; the GEOMETRIC
expected-dimension inputs are (i) classical BN [citable], (ii) E-H
Brill-Noether with ramification [citable], (iii) one linked-incidence
transversality statement [to prove or find; chain-provable].  Details:

C-arithmetic (proven today, pure counting).  Write E = sum k_i x_i, r
points, delta = e - r (profile coincidences), c = sum ceil(k_i/2), so
deg F = e + c.  E moves on general C => e >= gon >= (g+2)/2 (classical).
Two regimes:
 (Z1) e + c <= g - 1 ("automatic speciality" zone — F special for free).
      Bad data here need a pencil with a profile-delta member:
      delta <= rho + 1 = 2e - g - 1 (E-H BN-ram), and the zone forces
      c <= g - 1 - e.  Summing: c + delta <= e - 2.  But PER POINT
      ceil(k/2) + (k-1) >= k, so c + delta >= e.  CONTRADICTION:
      the zone is EMPTY, all profiles, all g.
 (Z2) e + c >= g.  Virtual dimension of bad data over a fixed general C:
      dim{(pencil, profile-delta member)} - codim{F special}
      = (rho + 1 - delta) - (e + c - g + 1) = r - c - 2 <= -2
      (c >= r since each ceil(k_i/2) >= 1).  Expected: EMPTY with margin 2.
 Reduced case sanity (delta = 0, c = e): bad <=> some pencil class N has
 h^0(omega - 2N) > 0; expected h^0 = g + 2 - 2e <= 0 exactly on the moving
 range e >= (g+2)/2 — the bound is tight but never positive.

C at g = 4 (the pipeline case) is COMPLETE modulo classical facts:
 - reduced: h^0(omega - 2N) > 0 with N trigonal <=> omega = 2N <=>
   VANISHING THETANULL <=> the canonical quadric is a cone — general g=4
   curves have rank-4 quadric (two distinct trigonal pencils), citable.
 - non-reduced: finitely many ramification coincidences (doubled/tripled
   trigonal members with enhanced canonical vanishing), each a proper
   closed condition in M_4.
So W1-h^0=1 AT g=4 holds for every (C, eps), eps != 0, with C outside an
explicit proper closed locus (thetanull + finite coincidence list) — and
g = 4 is exactly the base genus of the SIXFOLD Prym (dim 2(g-1) = 6).

### THEOREM (W1, h^0=1 stratum; conditional only on Lemma C's item (iii)
for general g; unconditional-modulo-classical at g = 4).
Let C be a curve in the Lemma-C-general locus of M_g, eps ANY nonzero
3-torsion class, pi the associated etale Z/3 cover.  Then for every
L in Nm^{-1}(omega_C) with h^0(L) = 1:  ker(beta_L) = T_L exactly
(the mu_3-Prym-Petri map beta-bar_L is injective).
Proof: Lemma A converts failure to a moving collision excess; Lemma B
converts that to K >= E + ceil(E/2); Lemma C excludes it.  QED.

Notes.  (1) eps-UNIFORM: one generality condition on C serves ALL eps
simultaneously — stronger than "generic pair", and no R_{g,3}-irreducibility
or one-full-member argument is needed for this stratum.  (2) The earlier
Theorem A/Reduction B remain for the h >= 2 rank-maximality extension.
(3) The chain-cover instrument now targets Lemma C item (iii) (a BASE
curve statement — classical E-H technology, no covers), not the cover.
(4) Search targets for (iii) before proving it: Osserman linked series;
Farkas incidence/ramification divisors; "semicanonical pencil" literature.

### Lemma C: the de Jonquieres route (2026-07-19 evening)

The right literature key is DE JONQUIERES DIVISORS (multiplicity-profile
loci in linear systems).  Sources: Farkas arXiv:2210.07843 ("Generalized
De Jonquieres divisors on generic curves"), which proves — for a GENERAL
curve, for ALL series simultaneously, by flag-curve limit linear series —
that every irreducible component of
  Sigma^f_mu(C) = {(l, x_1..x_e) : dim|V(-sum a_i x_i)| >= r - |mu| + f}
has dimension EXACTLY rho(g,r,d) + e - f(r+1-|mu|+f).  Plus Ungureanu
[U, Thm 1.5 as cited there]: full-degree case.

WARNING (caught before use): the naive reading of [U] ("no series has a
dJ divisor of length < d-r") is FALSE for composed series — 2E in |2N| is
a length-e member with e < 2e - r_2 whenever r_2 < e.  Her hypotheses must
be read at source before ANY use.  The applications below use only Farkas
Thm 1.1, with hypothesis-checks pending the same source read.

DELTA = 0 (reduced E), THE DIMENSION-COMPARISON KILL:  if some pencil N
has s = h^0(omega - 2N) >= 1, then EVERY reduced member E of |N| satisfies
K >= 2E for some canonical K (class-level!), so the canonical dJ locus with
profile mu = (2^e), f = |mu| - r = 2e-g+1 (allowed boundary value) contains
a subvariety of dimension >= dim W^1_e + 1 = 2e-g-1.  Farkas: every
component has dim = e - f = g-e-1.  So 2e-g-1 <= g-e-1, i.e. e <= 2g/3.
CONTRADICTION for e > 2g/3: bad is EMPTY there.  Since moving E needs
e >= (g+2)/2, and (g+2)/2 > 2g/3 iff g < 6:  DELTA=0 IS FULLY KILLED FOR
g <= 5 — in particular g = 4, the sixfold pipeline case, now rests on
Farkas' published theorem instead of the thetanull hand-analysis (both
agree; the tower cone is the e = g-1 = 3 face of the same statement).
CORRECTION (2026-07-19, caught while Lean-formalizing the arithmetic): at
g = 6, e = 4 the comparison gives EQUALITY (2e-g-1 = g-e-1 = 1), no kill;
that single boundary point joins the window.  It sits at rho = 0, the
exact shape of Ungureanu 1810.05461 Thm 1.1 — expected coverable there.

RESIDUE, stated precisely:
 (i)  verify Farkas Thm 1.1 hypotheses at source for the (2^e)-canonical
      application (f at the boundary |mu|-r) and read [U]'s hypotheses;
 (ii) delta = 0, g >= 7, window (g+2)/2 <= e <= 2g/3: not covered by the
      comparison; Clifford only caps s.  Candidate: run Farkas' flag-curve
      degeneration once with the linked (pencil + canonical) bookkeeping —
      my Z1/Z2 arithmetic is the combinatorial core it needs;
 (iii) delta = 1 profiles (E with one double point; delta >= 2 expected to
      die by [U] on the PRIMITIVE pencil once hypotheses are verified):
      analogous squeeze to run.
For g = 4: (ii) is vacuous and (iii) was already closed by the finite
coincidence list.  W1-h^0=1 AT g=4 = COMPLETE modulo reading Farkas'
hypotheses (one afternoon of source verification).

### SOURCE READ DONE (2026-07-19, late) — residue (i) DISCHARGED.

Farkas Thm 1.1 hypotheses verified at ar5iv source: Sigma^f_mu is a closed
determinantal locus in G^r_d x C^e, NO pairwise-distinctness requirement,
boundary f = |mu| - r explicitly allowed ("reduces to the classical de
Jonquieres case"), NO generality restriction on ell (every series on the
general curve), positive partition entries only.  Our canonical (2^e)
application is squarely in scope.  THEREFORE:
  * the delta=0 dimension-comparison kill (e > 2g/3) is SOURCE-VERIFIED;
  * delta=0 at g <= 6 — in particular THE g=4 REDUCED CASE — is CLOSED on
    the published theorem;
  * bonus: Farkas-on-pencils (r=1, full-degree profile, f = e-1) gives
    dim{(pencil, profile-delta member)} = rho + 1 - delta for ALL pencils
    on the general curve — replacing both the E-H BN-ram citation and any
    use of [U] for input (ii).

Ungureanu read (1612.03141 v4, Thm 1.5): her non-existence needs ell
GENERAL in G^r_d and g-d+r < 0 — NOT every series.  Farkas' one-line
quotation overstates her theorem; our composed-series paradox (2E in |2N|)
is resolved exactly there (2N is not general).  Consequence: [U, 1.5] is
UNUSABLE for special pencils; do not cite it for any delta >= 2 kill.

Ungureanu 1810.05461 ("intersections of secant varieties"): the two-series
emptiness technology for the remaining window EXISTS.  Her Thm 1.1: general
C, COMPLETE RESIDUAL PAIR l_1 = |K - N|, l_2 = N a pencil, rho = 0
(i.e. e = (g+2)/2, the minimal moving degree), point-count r_1 + r_2 =
g - e + 1: intersection of incidence varieties EMPTY.  Our delta=0 bad
configuration at e = (g+2)/2 is the SAME residual-pair shape with e points
instead of g - e + 1 = e - 1 (off by one).  Her Thm 1.2 = the general
dimension-sum criterion (f = 1).  Residue (ii)/(iii) is now: adapt her
Thm 1.1/1.2 (or rerun Farkas' flag-curve degeneration with the linked
bookkeeping) across the window — with literature coordinates fixed.

STATUS AFTER TODAY: W1-h^0=1 at g = 4 is PROVEN, resting on: Lemma A + B
(ours, complete), Farkas 2210.07843 Thm 1.1 (source-verified), classical
thetanull properness, and the finite delta=1 coincidence list at g=4.
General g: proven except the (g >= 7) window + delta=1 analogues, both
localized in the Ungureanu-Farkas toolbox.

## W2 write-ups (2026-07-19): the geometric payoff of W1

Setting: Y := Nm^{-1}(omega_C) inside Pic^{2g-2}(C~), a torsor under
ker(Nm) with identity component the Prym P, dim Y = 2g-2.  Tangent space
at any L:  T_L Y = ker(dNm) = H^1(eps) (+) H^1(eps^2)  [from pi_* O_{C~} =
O (+) eps (+) eps^2; dNm = the trace projection onto H^1(O_C)].
V^1 := { L in Y : h^0(L) >= 1 };  depth-one points are those with h^0 = 1.

### Theorem T (tangent lemma; W2 item ii).
Let L in V^1 be depth-one with section s.  Then
  T_L V^1 = ann( Im beta_L|_{s-slice} )  inside T_L Y,
and dim_L V^1 = g-1 always (see Lemma P below).  Consequently:
  (a) If ker beta = T_L exactly (the W1 conclusion), then rank beta = g-1,
      dim T_L V^1 = (2g-2)-(g-1) = g-1 = dim_L V^1: V^1 is SMOOTH of
      dimension g-1 at L.
  (b) Conversely if ker beta strictly contains T_L, then dim T_L V^1 =
      g-1 + (dim ker - 1) > dim_L V^1: V^1 is SINGULAR at L.
So W1 <=> V^1 is smooth along its entire depth-one locus; for (C,eps) with
C Lemma-C-general, Sing(V^1) is contained in V^2 (expected: finitely many
points, by the h=2 dimensional balance).

Proof.  A tangent vector v in H^1(O_{C~}) preserves the section to first
order iff the cup product v u s = 0 in H^1(L) (standard determinantal
deformation theory of {h^0 >= 1}).  Serre-dually, the transpose of
(u s): H^1(O) -> H^1(L)  is multiplication  (. s): H^0(omega L^{-1}) ->
H^0(omega_{C~}) — i.e. the s-slice of the Petri map alpha_L.  Restricting
v to T_L Y = the anti-invariant part of H^1(O_{C~}), the pairing with
H^0(omega_{C~}) factors through the anti-invariant projection pr; hence
T_L V^1 = T_L Y  ∩ ann(Im alpha|_s) = ann(Im (pr o alpha)|_s) =
ann(Im beta_L).  Its dimension is (2g-2) - rank beta = (2g-2) - (g -
dim ker beta) = g - 2 + dim ker beta.  With Lemma P this gives (a), (b).

### Lemma P (parametrization; the dimension of V^1).
The assignment  eta in |omega_C|  ~>  choices of W in C~^{(2g-2)} with
pi_* W = div(eta)  ~>  L = O(W)  defines a surjection
  Phi: { W : pi_* W in |omega_C| } --> V^1
whose source is finite over |omega_C| = P^{g-1} (finitely many preimage
splittings per divisor) and whose fiber over a depth-one L is the single
point |L|.  Hence every component of V^1 through a depth-one point has
dimension exactly g-1, and V^1 has dimension g-1 wherever it meets the
depth-one stratum.  (Local existence of the (g-1)-parameter family through
a given L: lift div(eta') for eta' near eta through the finite fiber-
product {(W', eta')} -> |omega|, which is finite surjective near (W, eta).)

Machine confirmation (tmp/w2_battery.sage, the bielliptic specimen): all
54 depth-one configs have rank beta = 3 = g-1 — by Theorem T these are 54
verified SMOOTH POINTS of V^1, dimension 3, on a sixfold torsor.  On the
thetanull tower, the u-fiber configurations (rank 2, kernel 2, h^0(L) = 1
in 10/12) are by (b) SINGULAR POINTS of V^1: they sweep a 1-parameter
family (the trigonal pencil times the finite sheet choices) — the original
tower's V^1 carries a singular CURVE beyond the expected finite V^2.  The
instrument saw both smooth and singular regimes exactly as Theorem T
prescribes.

### Item (i), scoped honestly: V^1 versus the Abel-Prym threefold W_3.
Both are (g-1)-folds attached to (C, eps) (at g = 4: threefolds; W_3 =
3-fold sum of the Abel-Prym curve in P, V^1 in the torsor Y).  PROVEN:
via Phi, any two points of V^1 over the same eta in |omega| differ by an
explicit sum of at most 2g-2 Abel-Prym curve elements ([y - sigma^a y]);
so the fibers of V^1 -> |omega| are AP-sum translates of each other.
OPEN (named): whether V^1 is itself a translate of W_3 (the mu_3 analogue
of the Z/2 identification of Prym-BN loci with Abel-Prym subvarieties —
literature exists only for Z/2).  Discriminating instrument job, queued:
compare Theta-degrees — the rigidity-law data give W_3 . Theta^3 = 3! C(6,3)
= 120; the degree of Phi and the Theta-pairing of V^1 are computable on
the bielliptic specimen.  Until that lands, W2 consumes only Theorem T +
Lemma P (which suffice for W3's normal-bundle setup: the smooth locus of
V^1 with its tangent description is what H^1(N) sees).

### MACHINE VALIDATION (2026-07-19, tmp/thetanull_check.sage) — the theory
predicted its own failure mode and the instrument confirmed it.

The tower's genus-4 base curve C (u^3 + xu + (y+1) = 0 over E0) has
QUADRIC RANK 3: a CONE — vanishing thetanull, omega = 2N, N = the trigonal
pencil = the u-map itself (u has exactly 3 poles).  So C sits ON the
excluded locus of Lemma C, and Lemma B's converse says the failing
configuration is constructible: W = (2 of 3 preimages) over each point of
a u-fiber E0(c); predicted s-slice Petri kernel = h^0(omega - E0(c)) =
h^0(N) = 2 (vs 1 = T_L).  Test (canonical-image rank; kernel = 4 - rank):
  u-fiber triples:  rank 2, KER = 2 — 5/5 fibers (the cone ruling).
  random triples:   rank 3, ker = 1 — 5/5 controls (T_L only).
Consequences:
  (a) Lemma A's kernel equality verified in BOTH regimes (jumping and not).
  (b) The generality hypothesis of the Theorem is NECESSARY — sharp, not a
      proof artifact.  (Register: the constructed failure is at s-slice
      level; whether h^0(O(W)) = 1 for the constructed W — making it a
      literal h^0=1-stratum counterexample on thetanull curves rather than
      an h >= 2 point — is unverified.  Compute h^0(O(W)) next.)
      DONE (tmp/hw_check.sage): dim L(D9) = 4, pool-stable, = the isotypic
      prediction {1,u}+{t}+{x/t}; h^0(O(W)) = 1 in 10/12 fiber+exclusion
      configurations (2 special-choice h^0=2 exceptions).  The constructed
      failures ARE literal h^0=1-stratum counterexamples: on a thetanull
      genus-4 curve the theorem genuinely fails, so the generality
      hypothesis is necessary in the strictest sense.
  (c) The battery's 14/14 is now EXPLAINED, not just observed: random
      sections are collision-free, and collision-free never fails (Cor A1).
  (d) The tower curve itself is NOT Lemma-C-general: fine for the pipeline
      (W2-W4 need the theorem at a general genus-4 curve, a moduli
      statement), but batteries on the tower must avoid colliding L or
      expect the h^0(N)-kernel.
Next instrument (Probe 2): limit linear series in Nm^{-1}(omega) at the chain
— per-bridge L-aspects (degree-2 bundles on each E_i with the norm condition)
and the limit Petri products against the flat tail-nested targets read out
per diagonal block.  That is where the per-bridge exact-order-3 exclusion
condition will fire, and it is a per-bridge elliptic computation.
