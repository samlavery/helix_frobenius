# W3 spec: the semiregularity map for the depth-one threefold (2026-07-19)

Target: Bloch's semiregularity map for Z = V^1_sm (the smooth locus, dim 3,
codim q = 3) inside X = Y ~ the sixfold Prym torsor:
    pi : H^1(N_{Z|X}) --> H^4(X, Omega^2_X).
Injectivity of pi ("Z semiregular") + Hodge-flatness (free in split-Weil
moduli) => the cycle deforms with its class (Bloch/Dan-Kaur) => W4's
propagation of algebraicity off the covered locus.

## Structural reductions (derived today)

1. ABELIAN TRIVIALIZATION.  With W := T_0 X (dim 6 = 2g-2, = H^1(eps) (+)
   H^1(eps^2)), Omega^p_X = O_X (x) Lambda^p W*, so
     H^4(X, Omega^2) = Lambda^4 W-hat (x) Lambda^2 W*   (dim 15 x 15 = 225),
   and Serre-dually the injectivity of pi is equivalent to LEFT-nondegeneracy
   of the pairing
     H^1(N) x H^2(X, Omega^4) --> C,   (xi, phi) |-> int_Z <contract(xi, phi)>,
   with phi = w1 ^ w2 (x) psi, w_i in W, psi in Lambda^4 W*: every column is
   an integral over Z of a contraction of xi against constant forms.  ALL
   ingredients live on Z; via the parametrization Phi: V^1 -> |omega| = P^3
   (Lemma P) they reduce to curve-level data.

2. NORMAL BUNDLE.  0 -> T_Z -> O_Z (x) W -> N -> 0 (T_X trivial).  LES:
     H^0(O_Z)(x)W -> H^0(N) -> H^1(T_Z) -> H^1(O_Z)(x)W -> H^1(N)
       -> H^2(T_Z) -> H^2(O_Z)(x)W -> ...
   The fiberwise description of T_Z is Theorem T: T_L Z = ann(Im beta_L) —
   so N_L = (Im beta_L)* canonically: THE NORMAL BUNDLE IS THE (dual) IMAGE
   BUNDLE OF THE PRYM-PETRI MAP along V^1.  W1 = its rank constancy (= 3)
   on the depth-one locus.  H^i(O_Z) via Phi: H^i(P^3, Phi_* O_Z),
   Phi finite; the sheet combinatorics of Phi determine Phi_* O_Z.

3. SHEET STRUCTURE OF Phi (new, from the lift analysis): over a generic
   eta in |omega| (6 distinct points), the lifts W are 3^6 = 729 choices;
   ker(Nm) has 3 components, so V^1 has <= 3 "parity" sheets-classes and
   Phi has degree ~3^5 per class onto P^3.  The monodromy (wreath-type on
   sheet choices) decomposes Phi_* O and hence computes H^i(O_Z) — job
   queued below.  Heuristic count check over F_7: per rational point of
   div(eta), a Frobenius-stable sheet choice exists with prob ~1/3 (t-fiber
   splits iff the y-value is a cube), contributing 3; else 0: E[#lifts] ~ 1
   per eta => |V^1(F_7)| ~ |P^3(F_7)| = 400 ~ 7^3: consistent with dim 3.

4. GAUSS-MAP HANDLE.  The Gauss map of Z is L |-> ann(Im beta_L) in
   Gr(3, W): its differential is the VARIATION of the Prym-Petri image —
   the same section-space data.  Semiregularity on abelian varieties is
   governed by this variation (second fundamental form); the instrument
   can measure the Gauss rank at sampled points NOW (finite differences of
   beta-image frames along V^1-directions).

## Job queue
 J1 DONE (tmp/w3_count.sage): RAW |V^1(F_7)|-weighted count = 1502 over
    399/400 etas (the single exception is eta = omega0 itself, div = the
    branch divisor R — u-sheet ramified there, bounded correction, TODO).
    Distribution: 310 etas with 0 lifts; contributing etas cluster on
    3^k (3, 9, 27) x deg-2 composites (10 = C(5,2) O-part, 56 = C(8,5)
    m=3 split-split — formula fingerprints check out).  Average 3.76
    lifts/eta vs naive-independence 1: the splittings are CORRELATED
    (F = (l-u)(l+u) pairing), input for J3's monodromy decomposition.
    Scale consistent with dim 3 + multi-component structure (<= 3 parity
    sheets, |L|-weighted).
 J1-spec (superseded, kept for method): |V^1(F_7)| exact on the generic stratum via the
    E0-side factorization — for eta = (c0 u + l(x,y))/u * omega0 with
    c0 != 0, div(eta) = zeros of F := l^2 - c0^2 h on E0 (each lifting to
    the UNIQUE u-sheet u = -l/c0), so: factor Res_Y(F, G) over F_7, per
    closed point (deg d, mult m) test y-value cubic in F_{7^d} (t-split)
    and tally prod [split: C(m+2,2); inert: 3|m].  Output: total count,
    distribution, exceptional-eta list.  Cross-checks dim 3 + feeds the
    Theta-degree discriminator and Phi_* O.
 J2 COMPLETE (tmp/w3_gauss.sage): GAUSS RANK = 3 at the generic depth-one
    base point — the Gauss map of V^1 is IMMERSIVE there: nondegenerate,
    theta-divisor-like.  Per-direction second-fundamental-form blocks:
    ranks (2, 3, 3) for l1 = (1, X, Y) — the constant direction bends in a
    rank-2 block (fine structure for J4's pairing).  Engine: tau-linear
    point motion by the 2x2 (E0-tangency, F-motion) solve; conjugates by
    Frobenius on both orders; rows by logarithmic derivatives; kernel by
    the perturbation solve (valid by W1's rank constancy — the theorem is
    load-bearing INSIDE the instrument now).  Good news for W3: a
    degenerate Gauss map would have threatened the semiregularity
    pairing's nondegeneracy; theta-like is the favorable regime.
 J2 LAYER 0 DONE (tmp/w3_gauss.sage): generic depth-one base point found
    (eta with ONE closed point of degree 6, fully off the special fibers);
    s = 1 trick + Frobenius-conjugate evaluation rows give dim M = 4,
    rank pr(M) = 3 — W1 VERIFIED AT A GENERIC DEPTH-ONE POINT (new
    coverage class beyond the 54 fiber configs).  Engine note: a degree-d
    closed point imposes d conjugate rows (one row = rank collapse to 9/6).
    REMAINING: the tau-layer per design below (dual-number Hensel at the
    moving closed points, perturbation kernel M_0 K_1 = -M_1 K_0, image
    frame F_0 + tau F_1, Gauss rank over the 3 eta-directions).
 J2: Gauss-rank probe — DESIGN (2026-07-19, three key facts):
    (a) BASE POINTS: the battery's special-fiber configs are UNUSABLE for
        first-order variation — their eta_0 has triple points, and moving
        a triple point branches like tau^(1/3): dual numbers fail.  Use
        GENERIC depth-one points from the J1 census (eta with 6 distinct
        split closed points and >= 1 rational lift).
    (b) THE s = 1 TRICK: at L = O(W~) presented by its section divisor,
        alpha(s (x) eta) = eta, so Im beta-bar = pr(M-space) where
        M-space = {eta in H^0(omega_C~) : div eta >= W~} — computed by
        EVALUATION ROWS of the 10-dim omega-basis at the 6 lifted points
        (no L-space, no denominator pools).  tau = 0 sanity: dim M = 4,
        rank pr(M) = 3 — re-validates W1 at a GENERIC depth-one point,
        beyond the 54 fiber configs.
    (c) FIRST-ORDER ENGINE: base ring K_d[tau]/tau^2 per closed point
        (E0-zeros of F(tau) = l(tau)^2 - h move tau-linearly by Hensel;
        u = -l(tau) explicit; t by etale Hensel).  Extension-field rows
        -> F_7-rows by restriction of scalars (coefficients in an F_7-
        basis).  Kernel over dual numbers by perturbation: M_0 K_1 =
        -M_1 K_0 (rank constant at depth one).  Gauss differential along
        each of the 3 eta-directions = F_1 mod F_0 of the image frame;
        Gauss rank in {0..3} measured.  Expectation 3 (nondegenerate,
        theta-like); anything less = structural news for semiregularity.
 J3 STRUCTURAL RESULTS (2026-07-19, derived):
    (a) ONE COMPONENT ONLY (proven): any two lifts W, W' over the same eta
        differ by sums of Abel-Prym elements [y-tilde^(a) - y-tilde^(a')],
        and every such element lies in the IDENTITY component of ker(Nm)
        (the (1-sigma)-image is connected and contains 0 via y-paths).
        So V^1 lies entirely in ONE of the three components of the torsor
        Y — the effective component.  The 3-component ambiguity is gone.
    (b) REFUTED AND REPLACED (2026-07-19, k=2 census): the first-draft
        irreducibility argument FORGOT A CONSTRAINT and the F_49 census
        caught it within the hour: weighted count 341552, ratio to 49^3 =
        2.903 -> the count tracks 3 q^3 (deficit 0.68 q^{5/2}, comfortable
        Weil range).  V^1 HAS THREE IRREDUCIBLE COMPONENTS.  The correct
        monodromy: as eta loops, the divisor's total motion-cycle gamma is
        NULLHOMOLOGOUS in C (it bounds the 2-chain traced by the moving
        divisor), so the total sheet-shift satisfies sum a_i =
        eps-holonomy(gamma) = 0: the monodromy lies in the index-3
        subgroup {sum a_i = 0} x| S_6, and SIGMA := sum of sheet-labels
        mod 3 is a monodromy invariant with exactly 3 orbits (243 sheets
        each).  THE MU_3 PRYM PARITY — the Z/3-twin of Mumford's Z/2
        parity on {h^0 > 0} for classical Pryms.  h^0(O_{V^1}) = 3; each
        component V^1_SIGMA is an irreducible threefold (dim, smoothness,
        Gauss-nondegeneracy all as measured).  The Weil-program cycle is
        ONE component.  Item (i) sharpens: is each V^1_SIGMA a translate
        of W_3?  All three components lie in the SAME Y-component ((a)
        stands: the AP-difference argument constrains the Y-piece, not
        the finer SIGMA).
        PARITY LAW CONFIRMED POINTWISE (tmp/w3_parity.sage, 48/48 clean
        all-split etas over F_7): lift-distribution over the 3 components
        is UNIFORM iff some closed-point degree !== 0 mod 3 — measured
        (1,2,3)->(9,9,9), (1,5)->(3,3,3), (2,4)->(3,3,3) — and TOTALLY
        CONCENTRATED iff all degrees == 0 mod 3 — measured (6,)->(3,0,0),
        20 etas, including the J2 Gauss base point (its 3 lifts are three
        points of ONE component).  Explains 3 nmid 1502.  The mu_3 parity
        is now: derived (null-cycle monodromy), detected (k=2 ratio
        2.903), and confirmed pointwise (48/48).
    (c) DECOMPOSITION FRAME (continuation plan): Phi_* O_Z decomposes by
        the 28 = #{multisets of size 6 from F_3} character-orbit local
        systems on P^3 minus the discriminant; h^i(O_Z) = sum of the
        orbit-sheaf cohomologies; the trivial orbit gives the O_{P^3}
        summand.  Computing the orbit-sheaf twists (branch behavior at
        the discriminant) = the remaining J3 work; the classical model is
        the Prym/Wirtinger Phi_* line-bundle decomposition for double
        covers, here upgraded to wreath rank.
    (d) LES START: with h^0(O_Z) = 1 and H^0(T_Z) = 0 expected (Gauss
        nondegenerate by J2, theta-like subvarieties carry no vector
        fields), H^0(N) begins with the 6-dim translation image W ->
        H^0(N); H^1(N) then needs h^1(O_Z) and H^{1,2}(T_Z) — the
        orbit-sheaf computation (c) feeds all of them.
 J3 (superseded spec): monodromy decomposition of Phi_* O => H^i(O_Z) dims => H^1(N) via LES.
 J4 PIVOT (2026-07-20, the unblocking move): abandon the 243-cover
    presentation; take the cycle Z = W_3 = AP+AP+AP with its RESOLUTION
    mu: Sym^3 C~ -> W_3 (mu generically injective: AP(A)=AP(B) =>
    A + sigma B ~ B + sigma A, degree-6 on genus-10 has h^0 = 0
    generically => divisor equality => A = B; AP itself injective since
    y + sigma y' = y' + sigma y with h^0(deg 2) = 1).  On Sym^3 of a curve
    every group in the pairing is symmetric-power linear algebra over
    curve data: H^i(O_{Sym^3}) = Lambda^i H^1(O_{C~}) (dims 1,10,45,120),
    H^1(T_{Sym^3}) = H^1(T_{C~}) = 27, Serre pairings = our section
    spaces.  Caveat named: W_3 singular where mu identifies; Bloch needs
    lci — work on the smooth locus / Dan-Kaur variant; the V^1-component
    coincidence with W_3-translates remains the open identification.
    FIRST DECISIVE NUMBER (reachable now): LES-transpose identifies
    RIGIDITY (h^0(N) = 6, i.e. ker(H^1(T_Z) -> H^1(O_Z) (x) W) = 0) with
    SURJECTIVITY of the multiplication
      H^0(omega~) (x) [H^0(omega eps) + H^0(omega eps^2)] --> H^0(omega~^2)
    (60 -> 27 on the specimen; H^1(T_{C~}) = H^0(omega~^2)*).  Rank 27 =
    rigid; rank < 27 = extra deformations, a discovery either way.
    tmp/w4_rigidity.sage measures it by product-evaluation rank.
    MEASURED (2026-07-20): gate h^0(omega~^2) = 27 exact; MULTIPLICATION
    RANK = 24, corank 3 — and the graded diagnosis EXPLAINS IT EXACTLY:
    per sigma-grade the ranks are (6/9, 9/9, 9/9); the bielliptic
    involution iota~ (u -> -u, lifts, commutes with sigma) grades
    everything, ALL six anti-invariant omega-sections are iota-ODD
    (structural: /u-built), so grade-0 products are all iota-EVEN and the
    3-dim iota-odd part of H^0(omega_C^2) is unreachable: corank =
    h^0(omega^2)^{iota-odd} = 3 on the nose.  VERDICT: not mu_3-intrinsic
    non-rigidity — a bielliptic artifact, exactly quantified; on the
    specimen h^0(N) = 6 + 3 (three genuine extra deformations, the
    Z/3-analogue of the classical bielliptic Prym-Torelli degeneration).
    Generic rigidity is the expectation off the bielliptic locus, but the
    instrument CANNOT yet certify it: trinomial towers are structurally
    thetanull, bielliptic towers structurally iota-obstructed — the NEXT
    INSTRUMENT PROBLEM, sharply specified: a genus-4 (C, eps) avoiding
    both (non-Galois degree-3 cover of E0 with u^2-term / mixed coefficient
    poles, or work over F_7(lambda)).  Semicontinuity: rank >= 24 nearby;
    one surjective instance anywhere gives generic rigidity forever.
    THIRD STRUCTURAL OBSTRUCTION (2026-07-20, tmp/w5_kummer.sage): the
    mu_3-KUMMER family u^3 = f, f in L(3O), is thetanull WHOLESALE (12/12
    candidates, quadric rank 3) — mechanism proven: u in L(O-fiber) (poles
    on ONE fiber) makes {1, u} a pencil with omega = 2*[O-fiber]; same
    mechanism as the trinomials (there too u in L(O-fiber)).  DESIGN LAW:
    the cover coordinate must have poles on >= TWO distinct fibers of the
    elliptic base.  Budget analysis: R = 6 is tight; naive two-fiber
    coefficient choices give slope-2/3 Newton (e = 3 at both fibers) and
    genus 6+.  NEXT: index-formula scanner over v^3 + p v + q with (p, q)
    in small pole-support families across {O, T, T'}; gates decide genus,
    quadric decides thetanull; rigidity rank on the first genus-4 rank-4
    hit.  Engine notes: allowO must be 0 (series already carry /u^upow —
    double-counting inflated gates 10->27, 27->63); the Kummer engine
    (cube-root u, compensator u^2) is validated ([4,3,3], 27 exact).
    Measured on the (thetanull) Kummer member: rank 26/27, corank 1 in
    grade 0 — thetanull-Petri geometry, unusable for the certificate.
    SCANNER CAMPAIGN (2026-07-20, tmp/w6_scanner.sage + w6_lib.sage):
    general-cubic engine BUILT AND REGRESSION-VALIDATED (level-6 branches,
    per-branch ramification detection, level-aware cutoffs; trinomial
    reproduces [4,3,3] exactly).  First family (w/x-atom coefficients):
    45/60 candidates gave INFLATED gates [8,7,5] (Sigma = 20 !== 1 mod 3:
    impossible as honest h^0 => engine under-conditioning): diagnosis =
    POLE-RAMIFIED fiber places (v with fractional negative valuation) break
    the monogenic/different assumption div(1/F_v pi*omega0) = poles(F_v) —
    conductor zeros uncompensated.  Candidates confirmed irreducible
    (root-histogram probe).  BUDGET THEOREM-LET: any v with poles on two
    fibers costs deg(disc-poles) >= 12 => genus 7, UNLESS 6 of the 12
    disc zeros are spent as NODES (square factor of disc) — THE EIGHTFOLD
    TUNED-PAIR PLAYBOOK.  Nodes are engine-native (branch enumeration) but
    the section spaces need the ADJOINT CONDITION (g vanishing at both
    node branches) added at the node places: detect disc square-part via
    gcd(disc, disc'), locate node fibers, add condition rows.  NEXT BUILD:
    the node-adjoint scanner — v_F(p) = -2, v_F(q) = -2 at a second fiber
    gives clean unramified pole-branches (0, -1, -1); tune (p, q) pairs so
    disc = (deg-6 simple part) x (square), gates then decide.
    W7 CAMPAIGN (2026-07-20, tmp/w7_nodes.sage): the closed-form node
    family (v-a)^2(v+2a) + c^2 = 0 (disc = -27c^2(4a^3+c^2): 3 nodes at
    c = 0, 6 simple branch pts, genus 4) BUILT AND GATED CLEAN — level-1
    engine, adjoint conditions at node branches from the same regularity
    rows, gates [4,3,3] pass across the family.  BUT quadric rank 3
    ALWAYS — the FOURTH thetanull incarnation, mechanism found exactly:
    h := c/(v-a) has div = T_3 - O-fiber (a degree-3 single-fiber map,
    the family's own magic function; T_3 = third points over the nodes),
    and div(v+a) = R - 2*O-fiber shows omega = 2[O-fiber] on the nose.
    MASTER LAW (four incarnations): branch data built from single-fiber-
    polar functions forces omega into fiber-class multiples => thetanull.
    TUNED-PAIR ATTEMPT: p = w^2, q = 2w^3 + c (w = (y+1)/x, poles T+O)
    cancels disc tops at BOTH fibers at once (char-7 identities: 112 = 0,
    70 = 0, 49 = 0) but the fiber double-branch eta^2 = -c/(5w) has odd
    valuation => e = 2 AT both fibers => genus 5; parity-fixing c-atoms
    re-blow the pole budget.  Dead end priced exactly.
    THE (3,3)-MODEL EXIT (designed; next build): C = tri-nodal bidegree-
    (3,3) curve in E0 x P^1: coefficients a_0..a_3 in L(3O) (12 params);
    nodes PRESCRIBED at 3 chosen generic (x_i, v_i): 9 LINEAR conditions
    => >= 3-dim solution family — linear algebra, no scan-luck.  Genus
    7 - 3 = 4; omega = O(R) with R = disc-zeros minus node-doubles: NOT
    a fiber-class multiple (nodes generic) => the master law cannot fire.
    Engine: monic transform W = a_3 v + a_2/3-shift (poles only over O,
    val -3, lands in L(3*O-fib): pencil-law safe since deg 9 not 3);
    ARTIFACT NODES at the three a_3-zeros (W takes the double value
    -a_2/3 on the two finite-v branches): 3 real + 3 artifact node-places,
    both get the standard adjoint rows; fiber places unramified, level 1.
    Then gates (Sigma = 10), quadric (rank 4 genuinely open at last),
    rigidity rank.
    *** STAGE 1 CLOSED (2026-07-20, tmp/w8_model33.sage): FIRST CANDIDATE
    HIT.  Specimen: tri-nodal (3,3)-curve with prescribed nodes at
    ((6,3), v=4), ((2,5), v=3), ((4,3), v=1) over E0/F_7 (seed 3372026):
    gates [4,3,3] exact; QUADRIC RANK 4 — the campaign's first certified
    non-thetanull (C, eps); h^0(omega~^2) grades [9,9,9] = 27 exact;
    RIGIDITY MULTIPLICATION RANK = 27 OF 27, surjective in every
    sigma-grade (9/9, 9/9, 9/9).  CONSEQUENCE (semicontinuity over the
    moduli of pairs, char 7, and by lower-semicontinuity over Spec Z also
    in char 0): for GENERIC genus-4 (C, eps) the multiplication
    H^0(omega~) (x) H^0(omega~)^anti -> H^0(omega~^2) is SURJECTIVE, so
    ker(H^1(T_Z) -> H^1(O_Z) (x) W) = 0 and h^0(N) = 6: THE ABEL-PRYM
    THREEFOLD IS RIGID MODULO TRANSLATION AT THE GENERIC MEMBER.  The
    bielliptic corank 3 and Kummer corank 1 stand as the special-locus
    corrections.  Stage 1 of the semiregularity pipeline is CLOSED;
    next: H^1(N) dimension bookkeeping through the LES with h^0(N) = 6
    pinned, then the pairing matrix (J4 stages 2-3). ***
    STAGE 2 CLOSED (2026-07-20, tmp/w9_syzygy.sage): with rigidity pinned,
    delta: H^1(T_Z) -> H^1(O_Z) (x) W is INJECTIVE (Serre-dual of rank 27)
    and coker(delta) = (ker mu)^* = the SYZYGY SPACE of the rigidity
    multiplication: computed EXPLICITLY on the certified specimen:
    dim 33 exact, graded (9, 12, 12) matching the product counts
    (18, 21, 21) minus (9, 9, 9).  H^1(N) = 33 + ker(delta_2) with
    delta_2 a SQUARE map 270 -> 270 (H^2(T_Sym^3) = H^1(T_C~) (x)
    H^1(O_C~) by the S_3-Kunneth; iso would give h^1(N) = 33 exactly).
    The transverse Kodaira-Spencer obstructions land in the coker-delta
    part, so the 33-dim syzygy space carries the W4-relevant block of the
    semiregularity matrix.  STAGE 3 (the derivation + build remaining):
    Bloch's pairing on the syzygy presentation in curve coordinates —
    columns = cup/residue pairings of syzygies against Lambda^2 U (x)
    Lambda^4 W* through the Sym^3 Kunneth; the witness machinery codes
    H^1-classes as Serre functionals on H^0(omega~).
    STAGE 3 MEASURED (2026-07-20, tmp/w10_pairing.sage).  Derivation: in
    Macdonald/Serre coordinates the Bloch pairing pulled to V = H^1(O_Z)
    (x) W is UNIVERSAL index combinatorics (products in [H*(C~)^(x)3]^S3
    are exact — contraction into the [pt]-slot, then the Lambda^2-Serre
    det); the bundle map N (x) Lambda^4 W* -> omega_Z is canonical
    (psi kills Lambda^4 of the 3-dim T_Z), so descent onto H^1(N) is
    automatic at cocycle level.  The specimen enters ONLY through
    im(delta).  ENGINE FACT: the AP scalars (1 - zeta^{-j}) sit in BOTH
    delta* and the restriction r — the measured syzygies (plain
    multiplication coordinates) must be rescaled by 1/c_b in the W*-slot
    before taking the annihilator; without the rescale the descent check
    fails at rank 9, with it DESCENT = 0 EXACTLY (theory and computation
    agree).  RESULTS:
      rank(B) = 15 of 33 on coker(delta) — the AP-threefold is NOT fully
        semiregular: pi has kernel >= 18 on the coker block, universally;
      KS-BLOCK (polarized deformations Sym^2 W, 21-dim): rank 9, kernel
        12 — the W4 target was rank 12 / kernel 9 (the Weil tangent):
        THREE FLAT DIRECTIONS BEYOND THE WEIL TANGENT;
      antisymmetric block: rank 15 of 15 (saturates the full image).
    INTERPRETATION FRONTIER (named, open): (i) verify the 9-dim Weil
    tangent sits inside the 12-dim kernel (needs the (C,eps)-deformation
    classes in V-coordinates); (ii) explain 15/9/3 combinatorially — the
    3 is parity-suspicious (Z = ONE parity component; the class-level
    Hodge locus of the primitive part may exceed the Weil locus exactly
    by parity-mixing directions); (iii) either way the naive W4
    propagation via full Bloch semiregularity does NOT close — the
    correct statement must run through the rank-9 detected block (9 =
    the Weil-family dimension itself: detection exactly along the
    family?).  To our knowledge these are the first Bloch-pairing ranks
    computed for any Prym cycle.
 J4 REDUCTION (2026-07-20, the full derivation):
    Serre-dual form: pi injective <=> for every 0 != xi in H^1(N), some
    constant 4-form psi in Lambda^4 W* and 2-form u1^u2 in Lambda^2 H^1(O_X)
    pair nontrivially:  < (u1^u2)|_Z  u  r(iota_xi psi) > != 0  in
    H^3(Z, omega_Z) = k,  where iota_xi: contraction N x Lambda^4 W* ->
    Lambda^3 W*, and r: Lambda^3 W*|_Z -> omega_Z is restriction along
    T_Z -> W (Theorem T makes r explicit: the beta-image frames).
    KEY STRUCTURAL CONDITION: if restriction H^2(O_X) -> H^2(O_Z) is
    SURJECTIVE, Serre-perfectness on Z reduces injectivity of pi to:
    xi |-> (psi |-> eta(xi,psi) in H^1(Z, omega_Z)) injective.  The
    theta-divisor analogy (H^i(O_X) ~ H^i(O_Theta), i < dim, via index-
    theorem vanishing) suggests h^{0,1}(Z) = 6, h^{0,2}(Z) = 15 and the
    surjectivity; for codim-3 Z this is NOT free — it is exactly what the
    orbit-sheaf computation must settle.  Deformation bookkeeping targets:
    h^0(N) = 6 expected (translations only; Z rigid mod translation);
    the W4 application needs pi injective at least on the rank-12 image of
    the transverse Kodaira-Spencer directions (dim X-moduli 21 minus dim
    Weil/(C,eps) locus 9 — note the DIMENSION MATCH: the (C,eps)-moduli
    and the signature-(3,3) Weil family are BOTH 9-dimensional, so the
    Prym locus is open-dense-ish in split-Weil moduli; propagation's true
    content = the closure/other components + the discriminant twists).
    Numerical-class datum banked: deg Phi = 243 per parity component, so
    (Phi* O(1))^3 = 243 = 3^5 on Z — the eta-line polarization cube;
    against W_3 . Theta^3 = 120 this says Phi*O(1) is NOT numerically the
    principal theta restriction (fine — it is the norm-system polarization);
    both numbers feed the eventual chi(O_Z)/Riemann-Roch cross-check.
    BLOCKAGE, honest: the matrix needs H^1(N), which needs h^i(O_Z) and
    H^i(T_Z) — i.e. the orbit-sheaf cohomology of Phi_* O_Z (28 multiset
    orbits refined by parity; trivial orbit = O_{P^3}-summand contributing
    (1,0,0,0) per component; the generic orbits are pushforwards from
    intermediate covers whose twist data at the discriminant is the
    remaining theory).  That is the named next build — a real computation,
    not an afternoon.
 J4 (superseded): the pairing columns int_Z contract(xi, phi) in curve coordinates =>
    the semiregularity matrix itself.  BUILD PLAN (blocks on J3's orbit-
    sheaf twists): (1) H^1(N) presented via the LES connecting maps once
    h^1(O_Z), h^i(T_Z) are pinned — all matrices already live in the
    tau-engine's coordinate systems; (2) matrix entries = algebraic
    trace/residue pairings on C~-data through Phi (no transcendental
    integrals: Serre-duality pairings of the omega-basis against the
    deformation classes, the same sigma-average projection extracting
    the anti-invariant components); (3) verdict = left-nondegeneracy of
    a (dim H^1(N)) x 225 matrix over the specimen's field; F_49 run for
    robustness.  k=2 census (w3_count2.sage, running): irreducibility
    ratio test — irreducible => count/49^3 near 1, components => ~#comps.
