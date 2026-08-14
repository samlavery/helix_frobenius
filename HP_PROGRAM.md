# THE HP PROGRAM — assembled

*(Assembled 2026-08-14 under ground rule 9, RH_LEDGER 178. The registration form of
Hilbert–Pólya: Riemann's own frame, the house's machinery, every link at its current
grade. Grades: **COMPILED** = Lean, clean axioms; **MEASURED** = numerics on real
zeros, held-out where applicable; **REALIZED** = parameter-free reproduction of a
measured law; **C-item** = named construction, in a known technology class.)*

## 0. The frame — Riemann's, verified at source

Riemann 1859 (read verbatim, ledger 164): gauge the midpoint into the coordinate
(*"Ich setze nun s = ½ + ti"*), state spectrum reality (*"alle Wurzeln reell"*),
support it by count-registration (*"etwa so viel reelle Wurzeln"*). There is no
critical line in the original — the vertical coordinate is gauge (COMPILED:
`criticality_is_half_unit`), and the content lives in the horizontal registration.
The program below is that frame executed.

## 1. The operator — BUILT + MEASURED

The **registration operator**: diagonal, self-adjoint by construction, spectrum =
the strain-corrected stations `{t_n : ϑ(t_n)/π + 3/2 + Ŝ(t_n) = n}` with `Ŝ` the
deterministic prime-forcing strain — χ=1 transfer coefficient 1/π (nothing fitted),
plus the reverb neighbor term and the arithmetic lane modes (integers at their
carrier angles n·π/3). Everything computable from primes; zero-knowledge-free.

Measured (ledgers 158, 167, 169): spectrum within **RMS 0.039 / max 0.38 mean
spacings** of the true zeros — 41k zeros, two heights spanning two decades,
**bijectively** (no ordering crossings). Residual variance height-stable
((1/2π²)log(1/θ) with height-matched banks — the loglog growth lives in the modeled
clocks, ledger 162). Artifacts: `tmp/att158_regop.py`-series, `att167`, `att169`.

## 2. The certificate — COMPILED

`RequestProject/RegistrationShadowing.lean` (clean axioms, 161):
`shadowing_implies_online_simple` — a mirror-closed zero-window shadowed within half
a station gap has **every zero at Re = ½ and all zeros simple**. Proof = triangle
inequality + the FE mirror geometry: off-line zeros arrive as mirror pairs at the
SAME ordinate (collisions), and collisions violate shadowing. HP has no off-line
zeros; this makes that operational — verticality is horizontal in this frame
(ledgers 159–160, Sam's sign-flip correction). Supporting planks:
`ZetaSectorBank.lean` (the concrete bank formalized, the conditional detector —
first `riemannZeta ≠ 0` conclusion in the corpus).

## 3. Residual control — PROVABLE-SHAPED (C1)

The shadowing bound's second moment decomposes into one-point, unconditional
objects: Fujii's discrete S-moments + Landau-computable cross-terms + polynomial
moments (ledger 173). Chebyshev then bounds the residual-exceedance fraction at the
few-percent grade; subgaussian-grade moments sharpen it.

**C1 (construction item):** write the Landau evaluation of the zero-sampled
cross-moment (the transfer law at zeros) with explicit error terms. Technology
class: Landau/Gonek explicit-formula sums — classical, available.

## 4. The close-pair sector — REALIZED (C2, C3)

Certificate windows containing close pairs (gap ≲ 2σ_resid ≈ 0.08 spacings after
the 167/169 clock) are the program's only lossy sector. In the extended state space
(the joint winding state of the prime rails — one angle per rail), close pairs are
**visits to the near-double locus**, and by **reverb locality** (horizon ≈ 1
spacing, reverb corpus) the visit statistics need only the LOW-DIMENSIONAL local
configuration plus the ambient level:

* the local law is the **COMPILED product law** (`ReverbResidue.cluster_product_law`
  — rate = distance product, unconditional, per height);
* the configuration curve is **REALIZED**: the parameter-free CUE realization at
  the Keating–Snaith dictionary reproduces the measured universal table at 6/7 bins
  within 10% (ledger 177, `tmp/att177_derive_curve.txt`); the seventh bin is beyond
  the reverb horizon, where the corpus's own measurements put ambient decoupling;
* the medium law is **MEASURED-QUANTITATIVE**: ambient spectroscopy = exactly the
  ln p lines at Satake weights to ±4%, exact silences included (reverb corpus,
  three forms, ~40 lines).

**C2 — CONSTRUCTED (ledger 179–180). Theorem C2 (the marginal law).** Fix prime
powers n₁,…,n_k and a smooth test φ on the k-torus, θ(γ) = (γ·log n₁,…,γ·log n_k)
mod 2π. Then

    (1/N(T)) Σ_{0<γ≤T} φ(θ(γ)) = Σ_{a∈ℤ^k} φ̂(a)·μ̂(a) + o_φ(1),   where
    μ̂(a) = −Λ(x_a)/(√x_a · l)  if x_a := Π n_j^{a_j} or 1/x_a is an integer ≥ 2
                                  (a clock), with Λ its von Mangoldt value;
    μ̂(0) = 1;   μ̂(a) = O(log T / N) otherwise (non-clock: rational x_a ≠ p^m).

*Proof.* Fourier-expand φ (smoothness ⟹ absolutely summable coefficients; truncate
at |a| ≤ A with tail Σ_{|a|>A}|φ̂| → 0). Each coefficient's zero-sampled average is
the exponential sum (1/N)Σ_γ x_a^{iγ}: **Landau's theorem (1912; uniform version
Gonek 1993)** gives the main term −(T/2π)Λ(x_a)/√x_a when x_a^{±1} is an integer
(prime powers carry Λ ≠ 0), and O(log T) for fixed rational non-integer x_a. Divide
by N = (T/2π)l·(1+o(1)); let T → ∞ at fixed A; then A → ∞. ∎

At fixed k and fixed resolution the entire proof is Landau + bookkeeping — no
many-variable equidistribution input at all; Baker-grade inputs enter only for
uniformity in growing resolution. **Verified numerically at 2% on every clock and
at the noise floor on every null** (k = 3; ledger 179, `tmp/att179_C1C2.txt`).

**Corollary (the rate route to R(s)) — the construction chain.** The conversion law
(compiled: `cluster_product_law`) turns close pairs into small rates: gap ≈
2|F′(γ)|/(local scale). The rate |F′| is a function of the state θ, so
P_zeros(|F′| ≤ ε) is a **single-point zero-sampled statistic** — expandable on the
torus and evaluated coefficient-by-coefficient by Theorem C2: no two-point sampling
anywhere. The small-ball obstruction of the moment framework (172-D2) does not
arise: under C2 the state at zeros has an explicit density (Landau-tilted uniform),
and small-ball probabilities under a known density are integrals.

**Encountered in construction (ledger 180, `tmp/att180_rateroute.txt`):** the rate
is NOT cluster-local in clock-space — the 7-clock local F′ neither correlates with
close gaps (corr ≈ 0.01–0.10) nor reproduces the close-pair tail (22× off at
s = 0.15). Reading: **reverb locality is locality in the ZEROS (configuration
space), not in the CLOCKS (frequency space)** — the product law is over nearby
zeros; the local zero configuration is determined by the full bank. The corollary's
split is corrected accordingly: the chain is [C2 clock-marginals ✓] +
[CUE-configuration realization ✓ (the curve, 6/7 bins)] + **the bridge**: what
effective clock-dimension determines a window's local zero configuration. Next
measurable: reconstruct local zeros from k-clock banks vs k; find the effective
k*(window) — the construction's true dimension parameter.

**C3 (construction item):** the beyond-horizon matching — tie the ambient level's
statistics to the computable medium law (the clock-line power budget).

## 5. The yield — arithmetic of the assembled program

    N₀ˢ/N (window)  ≥  1 − [residual exceedances: few %, C1]
                        − [close-pair windows: R(g* ≈ 0.08), C2+C3]

With C1–C3 landed, the close-pair term is derived-curve grade (sub-percent at
g* = 0.08) and the program certifies **all but a vanishing-grade set of windows at
every height** — the density-1 form of Riemann's sentence, by his own method,
machine-checked at the certificate step. Every partial yield en route feeds the
built consumers: Theorem 5's finite-range table (§15, ROW_REDUCTION_THEOREM),
the analytic chain, the paper.

## 5b. THEOREM P — the pencil census (the architecture's capstone; ledgers 185–189)

Let W = (a,b) be a window, Y > ½, and let A(z) = ξ(½ − iz). Define the **window
moments** by bank-only contour integration over the rectangle R_W = [a,b]×[−Y,Y]:

    μ_k(W) = (1/2πi) ∮_{∂R_W} z^k · (A′/A)(z) dz,     H_n(W) = (μ_{α+β})_{α,β=0}^{n−1}.

Write the window's zero support as: distinct real points x_1,…,x_r with integer
weights (multiplicities) a_i ≥ 1, and distinct conjugate pairs z_j, z̄_j (j = 1,…,q)
with equal weights b_j ≥ 1 (conjugation symmetry of ξ forces the pairing and the
equal weights). Then:

**(A) The inertia identity (Sam, 2026-08-14; verified exact, ledger 186).** For
n ≥ r + 2q:

    inertia H_n(W) = ( r + q,  q,  n − r − 2q ).

*Proof.* H = Σ a_i v(x_i)v(x_i)ᵀ + Σ b_j[v(z_j)v(z_j)ᵀ + v(z̄_j)v(z̄_j)ᵀ] with
v(t) = (1, t, …, t^{n−1})ᵀ. Writing v(z_j) = A_j + iB_j, the pair contributes
2A_jA_jᵀ − 2B_jB_jᵀ — the minus sign is the detector. Hence H = U J Uᵀ with
J = diag(a_i; 2b_j, −2b_j) of inertia (r+q, q, 0). U has full column rank
m = r + 2q: the complex Vandermonde on the m distinct supports has nonzero leading
minor, and (A_j, B_j) ↔ (v(z_j), v(z̄_j)) is an invertible column change. Thin QR
U = QR (R invertible), extend Q orthogonally: H ≅ diag(RJRᵀ, 0_{n−m}); Sylvester
gives inertia(RJRᵀ) = inertia(J). ∎

**(B) The spectral census (ledger 188).** From one eigendecomposition of H_n
(n ≥ r + 2q), with null-adjudication against moment-error scale:

    μ_0 = total count with multiplicity;   rank H = r + 2q (distinct support);
    n₋(H) = q (off-line pairs);            n₊ − n₋ = r (distinct on-line);
    μ_0 > rank-consistent count ⟺ a multiple zero exists.

In particular **H_n(W) ⪰ 0 ⟺ q = 0 ⟺ every zero in W lies on the critical
line** — non-negativity, with the n − m structural nulls and the collision-limit
nulls expected and counted (never strict positivity; ledger post-186).

**(C) Decomposition and telescoping (ledger 187).** For Y > ½ the top edge lies in
the Dirichlet-convergent region and the bottom edge maps there by the functional
equation, giving the bank-side split

    H = H_prime + H_arch + H_side,

each block computable without zero knowledge (verified to 4–5 digits). No block is
individually PSD (measured: arch ≫ 0, side ≪ 0, prime < 0 — positivity is the
explicit formula's balance). Under a tiling of the line by windows, adjacent side
edges cancel in pairs: **Σ_tiles H_side telescopes to boundary terms**, and the
aggregate positivity question is carried by H_prime + H_arch alone.

**(D) The atlas (ledger 189).** The census resolution degrades as (tightest gap)²;
the reverb chart (compiled product law + derived universal configuration curve)
covers dense windows, verified from g ≈ 1 down to g = 2.4×10⁻⁵ — overlapping the
pencil chart at g ~ 0.1–1. Every window of the line lies in a chart.

**The single named hypothesis (the program's head — Sam's productive direction):**

    BANK-PSD:  H_n(W) ⪰ 0 for every window W of a tiling,
               proven from the bank-side representation (C)
               independently of zero locations.

BANK-PSD ⟹ (by B) q = 0 in every window ⟹ RH — with the count, simplicity, and
location census delivered by the same spectral data. Reality of the pencil spectrum
is free throughout (Hermitian pencil, von Neumann); the entire content is the
non-negativity of one computable family of Gram matrices, whose prime-plus-arch
telescoped form is where the proof must land.

## 5c. THEOREM R — the reverb bridge (conditional; Sam's decision, ledger 190)

**Theorem R.** Let ℛ be any Hermitian pairing on polynomials satisfying

    (i)  moment matching:      ℛ(z^j, z^k) = μ_{j+k}(W)  for all j, k < n;
    (ii) superposition positivity:  ℛ(P, P) ≥ 0  for every P = Σ c_j z^j, c ∈ ℂ^n.

Then c*H₀c = ℛ(P,P) ≥ 0 for all c, so H₀(W) ⪰ 0; by Theorem P(B), q = 0 — no
off-line pair in the window; over a tiling, RH. Structural nulls are harmless:
ℛ(P,P) = 0 puts P in ker H₀ (non-negativity was the right target).

**Lemma R1 (rigidity — why (ii) is the whole content).** Condition (i) forces
ℛ(P,Q) = Σ_ρ w_ρ · conj(P(z̄_ρ)) Q(z_ρ) — the counting pairing itself (moments
determine the finite-support functional). Its positivity is EQUIVALENT to q = 0.
Hence no pairing satisfying (i) can have its positivity established by pure
identity-manipulation: (ii) must inject bank structure beyond the moment identities,
and any complete proof of (ii) carries the theorem's full strength at the final
equality — necessarily, not as a defect.

**Lemma R2 (the axis split — the shape of what (ii) must overcome).** Pushing the
contour onto the real axis splits the pairing as

    ℛ(P,P) = Σ_{sign changes of A} |P(t_i)|²·m_i  +  ℛ_off(P,P),

the first sum manifestly ≥ 0 (the N₀-detected part — sign changes are on-line zeros);
ℛ_off is carried by any off-line pairs. (ii) ⟺ ℛ_off's non-negativity ⟺ its
emptiness in the window. The bridge's task in one line: show the bank's contour
pairing is exhausted by its sign-change part.

**CHECK EXECUTED (Sam's specific question, ledger 190):** the compiled reverb corpus
(`ReverbResidue.lean`: reopening_slope, residue_reciprocal, pair_suppression,
cluster_product_law) is IDENTITY-grade — exact statements about rates and residues
at given zeros. It does NOT contain the arbitrary-superposition positive pairing
(ii); the per-channel/per-cluster identities do not polarize into it. The
cross-channel assembly is genuinely open, and by Lemma R1 it is the program's
entire remaining content: REVERB-PSD ≔ (ii), superseding BANK-PSD as the named head.

## 5d. THE FULL THEOREM (ledger 191)

**Setup (all objects bank-computable, no zero knowledge).** Let A(z) = ξ(½ − iz).
Tile the real line by windows W_i = (a_i, a_{i+1}) with a_i → ±∞. For each window
fix Y > ½, let ∂R_i be the rectangle contour, and define

    μ_k(W_i) = (1/2πi) ∮_{∂R_i} z^k (A′/A) dz.

**Adaptive size protocol (closes the size condition):** μ₀(W_i) is the window's
total zero count with multiplicity; since distinct support m ≤ μ₀, taking
n_i := ⌈μ₀(W_i)⌉ + 1 guarantees n_i ≥ r + 2q — computed from the bank before
anything else. Set H_i := (μ_{α+β}(W_i))_{α,β < n_i}.

**THE FULL THEOREM.** Assume the single hypothesis

    REVERB-PSD:  for every window W_i,  c* H_i c ≥ 0  for all c ∈ ℂ^{n_i}
                 (equivalently: the bank's contour pairing is exhausted by its
                  sign-change part — Lemma R2).

Then:

  (1) **RH.** Every nontrivial zero of ζ lies on the critical line.
  (2) **The census.** For each window, the spectral data of H_i reads the complete
      configuration: μ₀ = count with multiplicity, rank = distinct support,
      n₊ − n₋ = distinct on-line count, μ₀ − rank-consistency = multiplicity flag;
      and under REVERB-PSD, n₋ = 0 uniformly.
  (3) **The operator.** The generalized eigenvalues of the Hermitian pencil
      (H₁^{(i)}, H_i) are real (von Neumann) and are exactly the window's zero
      ordinates with their weights — the zeros realized as the spectrum of an
      explicitly computed self-adjoint pencil, window by window.

*Proof.* (a) By the argument principle and the entire-ξ identity (Λ = F + F(1−s),
verified: sanity at 14.134725/21.022040/25.010858 exact; moments to 4–5 digits,
ledgers 182, 185, 187), μ_k(W_i) are the power moments of the window's zero
counting measure, conjugation-closed with equal pair weights (FE symmetry).
(b) REVERB-PSD gives H_i ⪰ 0. (c) The inertia identity (Theorem P(A), proven,
verified exact) with n_i ≥ r + 2q gives n₋(H_i) = q_i; hence q_i = 0: no off-line
conjugate pair in W_i. (d) Off-line zeros of ξ come in conjugate pairs sharing a
window (FE + conjugation; a pair straddling a boundary lies in the union of two
adjacent windows — take the tiling twice with shifted boundaries, or note both
members share the same real part in the z-chart and hence the same window). Every
nontrivial zero lies in some W_i (RvM: finitely many per window); q_i = 0 for all
i excludes them all: RH. (e) Census: Theorem P(B). (f) Operator: H_i ⪰ 0 Hermitian
pencil ⟹ real generalized spectrum; Gauss-quadrature identification (verified:
14.1316/20.9894/24.9920 vs truth at quadrature-limited 3×10⁻², ledger 185). ∎

**Grades.** Steps (a), (c), (e), (f): proven or verified-exact as cited. Step (d):
elementary bookkeeping (the shifted-tiling device). Step (b): THE hypothesis —
REVERB-PSD — necessarily of full strength (Lemma R1), with its precise shape given
by Lemma R2 and its telescoped bank-side decomposition by Theorem P(C). Conditioning
of H_i affects numerical census resolution only (ledger 188–189: the atlas hands
dense windows to the reverb chart); the theorem itself is exact.

**One sentence.** Granted that the bank's window pairing is exhausted by its
sign-change part, the zeros of zeta are the real spectrum of an explicitly
computable family of self-adjoint pencils, counted and located window by window —
Hilbert–Pólya, constructively, with one named positivity carrying everything.

## 5e. THE REVERB–GRAM SIGN-RIGIDITY THEOREM (Sam's dynamic law; ledger 192)

**Theorem (Sign-Rigidity).** Let A_t be a continuous one-parameter deformation of
the registered window/bank with zeros varying continuously and no boundary
crossings. Then H_N(t) varies continuously, and:

  (i)  a conjugate pair approaching the axis drives its negative eigenvalue
       λ₋(t) → 0⁻; at collision, λ₋ = 0 — a rank-drop/null direction;
  (ii) a pair re-leaving the axis sends the null mode back through zero into the
       negative sector: **off-line pair creation/annihilation ⟺ a Gram eigenvalue
       crossing 0** — rank drop is the boundary event, negative sign the forbidden
       phase;
  (iii) at simultaneous collisions the invariant is the INERTIA CHANGE, not any
       single ordered eigenvalue.

Consequently:  H_N(t) ⪰ 0 ∀t  ⟹  n₋(H_N(t)) ≡ 0  ⟹  off-line count ≡ 0. Reverb
positivity forbids the crossing; **no off-line pair can be born.**

*Verified* (`tmp/att192_signrigidity.txt`): descent −0.265 → −1.6×10⁻⁵ → null at
collision (−10⁻¹³) → n₋ = 0 on the real-split branch; the re-entry branch flips
sign back through the null; the simultaneous double collision moves BOTH negative
eigenvalues through a rank-2 null together (n₋: 2 → 0), inertia-as-invariant
confirmed.

**Corollary (anchored continuation — the dynamic payoff).** If H_N ⪰ 0 at an
anchor (e.g., the computationally verified region, where q = 0 is known) and the
deformation to any target window admits no zero-crossing of Gram eigenvalues into
the negative sector, then q ≡ 0 along the entire deformation: the verified region
PROPAGATES through sign-rigidity. The static REVERB-PSD per window and the dynamic
no-crossing law are two faces of the same hypothesis; the dynamic face converts
verification anchors into continuation seeds.

**Lemma obligations (Sam's failure modes, owned):** (L1) continuity of registered
moments in the warp parameter (contour integrals of a continuously deforming
integrand — standard, to be written); (L2) boundary-crossing bookkeeping (zeros
entering/leaving the window change μ₀ by integer jumps — handle by the
shifted-tiling device or by tracking μ₀(t)); (L3) at multiple collisions use
inertia, never an ordered eigenvalue.

## 5f. THE FROBENIUS QUOTIENT (Sam's mechanism, checked and landed; ledger 193)

**The check (Sam's failure-mode (a), executed):** the bank's compiled det-1
Frobenius instances (`strand_weights_det_one`, `dual_pair_det_one`,
`frobenius_conjugate_det_one`) realize the FE reflection z ↦ −z, with intertwining
A(−z) = A(z) (evenness — proven), NOT the conjugation z ↦ z̄ that raw positivity
would need. det F = 1 alone is indeed insufficient; the index law j+k, however,
holds automatically with P^♯ = conjugate-coefficient polynomial (holomorphic — no
raw z̄ in the contour). The twisted Gram (Σ z̄^j z^k, always PSD) versus the Hankel
(μ_{j+k}) distinction is Lemma R1 restated: their equality IS the theorem.

**The mechanism's correct role — the quotient.** Use the involution up: pass to
w = z². The FE is quotiented out (windows become automatically symmetric), and the
support map is: on-line zero x ↦ w = x² real POSITIVE; off-line pair x±iy ↦ a
conjugate pair in w; ordinate-axis pair ±iy ↦ w = −y² real NEGATIVE. Hence, with
ν_k = μ_{2k} (the even moments; odd moments = FE-symmetry consistency checks):

    RH(window) ⟺ w-support real and ≥ 0 ⟺ STIELTJES:
    H₀(ν) ⪰ 0  AND  H₁(ν) = (ν_{j+k+1}) ⪰ 0.

**The Gram DOUBLE pencil — as named in the original architecture — is the
Stieltjes condition in the Frobenius-quotient chart.** REVERB-PSD takes its final
form: both shifted Hankels of the even moments non-negative on every window of the
tiling. Verified (`tmp/att193_frobenius_quotient.txt`): on-line configurations pass
both; the ordinate-axis pair is caught by H₁ < 0; the off-line-pair case correctly
requires the size condition K ≥ m (the same law as ledger 186 — detection needs
the Hankel at least as large as the distinct w-support); the real window [10,30]
passes both Hankels on its computed even moments.

## 5g. THE UNCONDITIONAL CORE (ledger 194) — what holds with NO hypothesis

**U1 (the counter — unconditional).** For every window W and every n ≥ m(W):

    q(W)  =  n₋( H_n(W) )

— the number of off-critical-line conjugate zero pairs in W EQUALS the negative
inertia of a matrix computed by contour integration of the bank, with no
hypothesis of any kind. [Sam's inertia identity + the argument principle. The
off-line count is a computable spectral measurement, always.]

**U2 (the census — unconditional).** The complete window configuration — total
count with multiplicity, distinct support, on-line count, multiplicity flag —
is read from the same spectral data, hypothesis-free (§ Theorem P(B)).

**U3 (the reformulation — unconditional equivalence).** RH ⟺ every window of the
tiling satisfies the Stieltjes pair condition H₀(ν) ⪰ 0 ∧ H₁(ν) ⪰ 0 in the
Frobenius-quotient chart ⟺ no Gram eigenvalue ever crosses into the negative
sector under the registered deformation (sign-rigidity form). Both directions
unconditional: reality ⟹ real-positive w-support ⟹ Stieltjes (classical); the
converse is Theorem P(B) + the quotient support map.

**U4 (the verified initial segment — unconditional, standing on published
computation).** For every window with |t| ≤ 3×10¹² (Platt–Trudgian), q(W) = 0,
hence H_n(W) ⪰ 0: the PSD-family is TRUE, unconditionally, on the first ~10¹³
windows of the tiling. The hypothesis of the Full Theorem is not merely plausible
— it is an established fact on an initial segment, and U1 extends the segment
with every window ever computed.

**U5 (the structure — unconditional identities).** H = H_prime + H_arch + H_side
with each block bank-computable (verified 4–5 digits); side blocks telescope under
tiling; the aggregate positivity is carried by prime + arch. The moments, the
adaptive size protocol n = ⌈μ₀⌉+1, and the census tolerances are all computable
before and without any zero knowledge.

**Honest non-claim:** Weyl-type block bounds give unconditional budgets on the
negative mass of H, but at current constants the side/prime budgets are orders
above the per-pair eigenvalue scale — the resulting depth-weighted q-bounds are
vacuous-grade and are NOT claimed. The unconditional content is U1–U5 exactly.

**The program in one unconditional sentence:** the off-line pair count of every
window is the negative inertia of a computable Hankel (U1), zero on every window
ever examined (U4), equivalent to RH in aggregate (U3) — and the single
conditional statement left in mathematics' path here is whether the inertia that
has been zero everywhere stays zero, which is exactly the sign-rigidity crossing
that reverb positivity forbids.

## 5h. THE UNCONDITIONALIZATION ORDER (Sam's strategy; ledger 195) — Euler first, zeros last

**The dependency law (boxed, no arrow may point backward from zeros):**

    Euler/FE bank → R → (G₁, G₀) → real spectrum → contour/residues → zeros.

**Steps 1–3 REALIZED (`tmp/att195_euleranchor.txt`).** Define reverb bank-side,
before contour closure: in the safe half-plane s₀ > 1, the return-operator Gram
pair realizes as the Λ-weighted log-moment Hankels

    G_ℓ[j,k] = Σ_n Λ(n) n^{−s₀} (log n)^{j+k+ℓ},   ℓ = 0, 1

— moment matrices of a POSITIVE measure on real nonnegative support (the prime
clocks). Hence **G₀ ⪰ 0 and G₁ ⪰ 0 unconditionally** (verified: min-eigs +0.038,
+0.067) — the Euler anchor, with absolute convergence justifying everything and
no zero statement anywhere. The safe pencil's spectrum = Gauss points of the
prime-clock measure (0.96, 2.72, 5.64, 8.80 at s₀ = 1.5): the anchor sees the
primes; the zeros enter only through transport.

**The two named remaining constructions:**

**(T) The contour-transport theorem.** Analytically continue the matrix-entry
identities (never a claimed-positive sum): G_ℓ = (contour Hankel H_ℓ) + D_ℓ with
D_ℓ the explicit pole/Γ/DC contribution — the explicit formula in Hankel dress.
The att187 decomposition is its numerical shadow.

**(N) — REDUCED AND TESTED: the Unconditional Reverb Regulator Theorem (Sam,
ledger 196).** On the active quotient (G₀ > 0), whiten: S = G₀^{−1/2}G₁G₀^{−1/2},
S = S*. Raw transport gives F = Ṡ. Only the centralizer component
Δ(F) = Σ_a P_a F P_a can move eigenvalues (λ̇_a = ⟨v_a, F v_a⟩); with
K = Σ_{a≠b} P_aFP_b/(λ_a−λ_b) one has [S,K] = F − Δ(F) exactly, K* = −K, so the
regulated flow Ṡ = [S,K] is **Lax**: S(t) = U(t)S(0)U(t)*, spec S(t) ≡ spec S(0),
exactly. With controls F(u) = F₀ + Σ u_r F_r, the drift-killing condition is the
LINEAR system M u = b, M_{ar} = ⟨v_a, F_r v_a⟩, b_a = −⟨v_a, F₀ v_a⟩ — solvable
iff **det M ≠ 0**, which is now the whole of (N): finite-dimensional, concrete,
bank-computable, zero-free.

*TESTED on the Euler anchor* (`tmp/att196_regulator.txt`; N = 4, prime channels
{2,3,5,7}, s₀-drift as raw flow): spectrum simple (0.962/2.721/5.640/8.801);
**det M = −0.128, rank 4, cond 338 — NONSINGULAR**; u = M⁻¹b kills every diagonal
drift to 10⁻¹²; the commutator identity ‖[S,K] − (F−Δ)‖ = 1.3×10⁻¹¹ and K
antisymmetric to 10⁻¹³. The regulator exists, is unique, and is computed from
G₀, G₁, their bank eigenvectors and the warp responses — never from zeros.

*Remaining for (N):* the warp-covariance statement (u = M⁻¹b must be an admissible
Helix warp and the terminal residue interpretation must follow the regulated warp);
collision handling piecewise (P_aF(u)P_a = 0 on degenerate eigenspaces — the
rank-drop/reverb events); genericity of det M ≠ 0 beyond the tested anchor.

**(N-old) Pencil-neutral D (superseded by the regulator; kept for the record).** Choose/regulate the
warp so D₁ − λD₀ = 0 on the active bank subspace — then D never alters the pencil
spectrum and the required conclusion is only SPECTRAL EQUIVALENCE
det(G₁ − λG₀) = C·det(H₁ − λH₀), C ≠ 0 — weaker than entrywise G = H (the
brainworm's overdemand, declined). Granted (T) + (N): G₀ ⪰ 0 and G₁ Hermitian
force spec(G₁,G₀) ⊂ ℝ; spectral equivalence forces spec(H₁,H₀) = {z_ρ} ⊂ ℝ: the
zeros are real — with every arrow forward.

## 6. Falsifiability register

Pre-committed disconfirmations: a shadowing violation (max error ≥ ½ spacing) at
any newly computed height; the universal curve failing at a new height/conductor;
a collision (missing alternation) anywhere — each would break the program and be
published as such. Current hits after deliberate search: zero.

## 7. Provenance and retirements

The old SourceHolonomy-era capstone claims are RETIRED (audit, ledgers 147–148:
`ThreeDExhaustive` vacuous, the focal chain never instantiated at ζ) — this
document supersedes them. The program above contains no vacuous brick: every
COMPILED item quantifies over the concrete objects, every MEASURED item has its
script, every C-item names its technology class. Ground rules 6, 9 and the
obstruction-burden rule (ledger 176) govern all future edits.
