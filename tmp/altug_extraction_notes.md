# Altuğ "Beyond Endoscopy via the Trace Formula" — Primary-Text Extraction

Method: downloaded actual arXiv PDFs via `curl` and converted with `pdftotext -layout`
(files in `tmp/altug_pdfs/`: `altug1.{pdf,txt}` = arXiv:1506.02218 (Compositio 2015, 29pp),
`altug2.{pdf,txt}` = arXiv:1506.08911 (Amer. J. Math 2017, 40pp), `altug3.{pdf,txt}` =
arXiv:1512.09249 (J. Inst. Math. Jussieu 2020, 28pp), `deng_espinosa.{pdf,txt}` =
arXiv:2603.21506 (122pp, confirmed via `pdfinfo`)). All four downloads succeeded as real,
multi-page PDF text — this supersedes the prior scout's note that WebFetch returned only
binary; `curl` + `pdftotext` worked cleanly. All facts below are read directly from the
extracted text, with line numbers into the `.txt` files for spot-checking.

All arXiv IDs below are CONFIRMED (not reconstructed): 1506.02218, 1506.08911, 1512.09249,
2603.21506.

---

## (1) THE ELLIPTIC SUM, verbatim

**Setup (Altuğ I, §2.2.1, altug1.txt:399–420).** G = GL(2), γ ∈ G(Q) elliptic (characteristic
polynomial irreducible over Q). The elliptic part of the trace formula is
```
Σ_{γ ∈ G(Q)^{#,ell}}  vol(γ) · Π_q Orb(f_q; γ)
```
where `Orb(f_q; γ) := ∫_{G_γ(Q_q)\G(Q_q)} f_q(g⁻¹γg) dḡ_q` and
`vol(γ) := ∫_{Z⁺ G_γ(Q)\G_γ(A)} dg`, product over all places q including ∞.

**Measure normalization (altug1.txt:410–419):** at finite p, Haar measure giving G(Z_p) mass 1
(and same for G_γ(Z_p)); at ∞, on the torus G_γ(R) decomposed as δ = z_δ δ̄ u_δ with
z_δ ∈ Z⁺ central, u_δ = diag(1, sign(det γ)), δ̄ ∈ SL_2(R): if γ elliptic over R take dθ on the
eigenvalue angle e^{±iθ}; if γ split over R take dλ/λ on eigenvalues λ, λ⁻¹.

**Trap (a) RESOLVED — class number vs. class number × regulator (altug1.txt:441–459,
equation (1)):**
```
vol(γ) = { 2h(γ)R(γ)         if D_γ > 0   (real quadratic — regulator IS present)
         { 2πh(γ)/ω_γ        if D_γ < 0   (imaginary quadratic — roots of unity, no regulator)
```
where (N_γ, m_γ) := (4·det γ, tr γ), m_γ² − N_γ = s_γ² D_γ with D_γ the discriminant of
Q(√(m_γ² − N_γ)), and ω_γ, h(γ), R(γ) are the number of roots of unity, class number, and
regulator of that same quadratic field. Altuğ immediately converts this via Dirichlet's class
number formula into **L(1, χ_{D_γ})** in BOTH cases:
```
L(1, ·/D_γ) = 2h(γ)R(γ)/√D_γ            (D_γ > 0)
            = 2πh(γ) / (ω_γ √|D_γ|)      (D_γ < 0)
```
so `vol(γ) = √|D_γ| · L(1, ·/D_γ)` uniformly — **the regulator is absorbed into L(1,χ) itself
via the class number formula; it is never a separate multiplicative factor you'd add by hand.**
This is the single cleanest resolution of trap (a): don't code "class number" or "class number
× regulator" as a literal Python function — code `L(1, χ_D)` (an ordinary Dirichlet L-value at
s=1, computable directly, e.g. via the class-number formula or numerically) and the
real/imaginary distinction is already inside it.

**Final closed form after folding in all local orbital integrals, "final form of the elliptic
part" (altug1.txt:592–612, equation (4)) — this is THE target sum, fully pinned:**
```
Σ_{∓} Σ_{m∈Z, m²±4p^k ≠ □}  θ∞^{∓}(m / (2p^{k/2}))  ·  Σ'_{f² | m²±4p^k}  (1/f) L(1, ·(m²±4p^k)/f²)
```
where the primed sum over f runs over square divisors of m²±4p^k such that
(m²±4p^k)/f² ≡ 0,1 mod 4 (i.e. is itself a discriminant), and θ∞^∓ is the archimedean weight
function defined in (⋆⋆⋆) below. The two signs ∓ correspond to det(γ) = +p^k (using θ∞⁻, the
"−" branch, i.e. x²−1 sign conventions) vs. det(γ) = −p^k (θ∞⁺); the ± bookkeeping around N_γ =
±4p^k tracks which sign of determinant is being summed and is not optional — both signs appear
in every stated formula.

**The archimedean weight θ∞^∓ (altug1.txt:497–580, "final form" derivation via (⋆),(⋆⋆),(⋆⋆⋆)):**
Starting from the near-central asymptotic of the orbital integral,
`Orb(f∞;γ) = g1(γ) + |γ1γ2|^{1/2}/|γ1−γ2| · g2(γ)` (eigenvalues γ1,γ2 of γ; g1 supported only on
the elliptic torus), rewritten in (N_γ, m_γ) coordinates and using Z⁺-invariance of f∞ to reduce
to a function of the single ratio x = m_γ/√|N_γ| and sign(N_γ):
```
θ∞^∓(x) := 2|x² ± 1|^{1/2} g1^∓(x) + g2^∓(x)          (⋆ ⋆ ⋆)
```
This is exactly what test function f∞ determines; it has a prescribed (integrable but
non-smooth) singularity at x = ∓1 of type |x²±1|^{1/2} (elliptic-to-central degeneration).

**GL(3) analogue (Deng–Espinosa, arXiv:2603.21506, deng_espinosa.txt:340–343):** the elliptic
part is parametrized by pairs (a,b) (traces of the characteristic polynomial of a 3×3 matrix,
i.e. coefficients of x³ − a x² + b x − det), and reads
```
Σ_{(a,b)}  L(1, R(a,b))  ·  θ±(a p^{−k/3}, b p^{−2k/3})
```
where R(a,b) is a cubic order (Gorenstein order over Z) attached to the characteristic
polynomial, and L(1,R(a,b)) is now an order-zeta-value (Yun's zeta function J_R(s), conjectured
— NOT proven, see §(6)/(7) below — to equal L(s,R)ζ_Q(s) for a Dirichlet-series-like L(s,R)
attached to R) evaluated at s=1, replacing the quadratic class-number×regulator/L(1,χ) factor
of GL(2) with a cubic-order zeta value.

---

## (2) THE AFE INSERTION

**Test function (Altuğ I, eq. (7), altug1.txt:718–719; re-quoted verbatim in Altuğ III eq. (9),
altug3.txt:657–663):**
```
F(x) = 2 K₀(2)⁻¹ ∫_x^∞ e^{−y − 1/y} dy/y
```
where K₀ is the 0th modified Bessel function of the second kind (a fixed normalizing constant,
NOT the archimedean transform itself — do not confuse this K₀(2) constant with a Bessel-type
integral transform in x; it only appears as `2K₀(2)` normalizing the tail integral). Properties
used (altug1.txt:723–738, Lemma 3.2/3.3): 0 < F(x) < (e^{−x}/K₀(2)) for x>0 (bound 8), and its
Mellin transform F̃(z) = (1/z)·K_z(2)/K₀(2) is holomorphic except for a **simple pole at z=0
with residue 1**, is odd, and satisfies F̃(z) ≪ |z|^{σ−1} e^{−(π/2)|t|}. Altuğ III footnote 6
(altug3.txt:673) explicitly says: *"the specific choice of this function is irrelevant to the
rest of the argument. Only the pole of its Mellin transform is important."* So F is a
convenience choice (for computing F̃ in closed Bessel-ratio form), not load-bearing in itself —
any Schwartz-class F with F̃ having a simple residue-1 pole at 0 would do (Altuğ I, remark after
eq. list, altug1.txt:353–356, makes the same point: "The arguments go through with an arbitrary
choice of a Schwarz class function F").

**The functional equation being exploited (Altuğ I §3.1, Prop 3.1, altug1.txt:672–712):** for
δ a discriminant, define
```
L(z,δ) := Σ'_{f²|δ} (1/f^{2z−1}) L(z, ·(δ/f²))          (5)
Λ(z,δ) := (|δ|/π)^{z/2} Γ((z+ι_δ)/2) L(z,δ),  ι_δ = 0 if δ>0, 1 if δ<0     (#)
```
satisfies **Λ(z,δ) = Λ(1−z,δ)** (eq. 6) — this is the functional equation of the SPECIFIC
weighted sum-over-f of Dirichlet L-functions that appears in (4), not the bare L(z,χ_δ)
functional equation; it is a "square-divisor-summed" completion. Proposition 3.1's proof cites
this as "the content of Lemma 2.1 of [18]" (Zagier), also independently observed by Bykovskii —
i.e. this exact functional equation predates Altuğ and is imported, not new.

**AFE derivation (Altuğ I, Prop 3.4 + Cor 3.5, altug1.txt:743–876):** standard Mellin-contour-shift
argument (shift contour picking up the pole of F̃ at u=0, using oddness of F̃ plus the functional
equation (6′) to reflect the shifted integral back). Result, specialized to z=1 (Corollary 3.5,
eq. 11, altug1.txt:851–857):
```
L(1,δ) = Σ'_{f²|δ} (1/f) Σ_l (1/l) F(lf²/A)  +  |δ|^{−1/2} Σ'_{f²|δ} f Σ_l (1/l) H_{ι_δ}(lf²A/|δ|)
```
where **A > 0 is the free truncation parameter**, and H_0, H_1 are explicit Mellin-Barnes
transforms of F̃ against ratios of Γ-functions:
```
H_0(y) = (√π/2πi) ∫_{ℜ(u)=1} [Γ(u/2)/Γ((1−u)/2)] (πy)^{−u} F̃(u) du       (H0)
H_1(y) = (√π/2πi) ∫_{ℜ(u)=1} [Γ((1+u)/2)/Γ((2−u)/2)] (πy)^{−u} F̃(u) du   (H1)
```
Bound (Lemma 3.6, altug1.txt:912–915): H_{ι_δ}(x) ≪ (1/x) e^{−2√x} for ℜ(x) ≥ 1 — exponential
decay, so the "dual" H-sum is negligible once its argument is large; this is what makes the AFE
an actual truncation (the F-sum is the "short" side, the H-sum is exponentially small unless A
is chosen so the H-argument stays small too).

**Trap (b) RESOLVED — the exact truncation-parameter choice, in two places:**
- **General theorem (Altuğ I, Prop 4.1 + discussion, altug1.txt:1038–1103):** for ANY
  `0 < α < 1`, setting **A = |m² ± 4p^k|^α** (i.e. tying the AFE length to the discriminant
  itself, raised to a tunable power α) makes both smoothed pieces of the summand
  (θ∞^∓(m/2p^{k/2})·F(lf²/|m²±4p^k|^α) and the H-term) become C^∞ functions of the real
  variable m — because Proposition 4.1 shows θ∞^∓(x)·Φ(|1−x²|^{−α}) is smooth for any Schwartz
  Φ, α>0 (the singularity of θ∞ at x=∓1 is exactly canceled by the polynomial-in-(1−x²)^{-α}
  decay forced through F, Φ Schwartz). **α is a genuinely free continuous dial in Part I/II** —
  this is the "carefully chosen" truncation the abstract references, and its role is purely to
  make θ∞^∓ · (AFE main term) jointly smooth so Poisson summation applies; it is NOT tied to
  the conductor or weight k by a fixed formula in the general theorem.
- **Concrete instance actually used (Altuğ III, eq. after Lemma 4.4, altug3.txt:664–665,
  "Let m < 2√n. Then, by Corollary 3.5 of loc. cit., where we have taken A = 4n − m² and ι_δ=1"):**
  **α is fixed to exactly 1/2**, i.e. A = |4n−m²|^{1/2} literally — Lemma 4.4 in Part III states
  "This is just a restatement of theorem 4.2 of [Alt15a], where we take α = 1/2" (altug3.txt:718).
  So: **the general machinery leaves α ∈ (0,1) free; the executed standard-representation
  application in Part III commits to α = 1/2 specifically.** If reproducing a concrete numeric
  instance, α=1/2 is the value with a citable primary-source anchor; other α∈(0,1) are valid but
  untested in the executed papers.

**What is dualized:** it is the **f-sum inside L(1,δ)** (equivalently, the divisor/conductor
variable of the completed Dirichlet series L(z,δ) of eq. (5)) that gets AFE-expanded into a main
F-sum (short, over lf² ≲ A) and a dual H-sum (over lf² ≳ |δ|/A, negligible by Lemma 3.6) — NOT
a dualization of the trace variable m itself. The m-variable dualization happens one step later,
via genuine Poisson summation (next section), applied to the now-smooth-in-m combined
expression.

---

## (3) THE POISSON-DUALIZED FORM

**Smoothing lemma making Poisson valid (Altuğ I, Prop 4.1, altug1.txt:1038–1063):** stated and
proved directly: for α>0 and Schwartz Φ, both θ∞^∓(x)Φ(|1−x²|^{−α}) and
|1−x²|^{−1/2}θ∞^∓(x)Φ(|1−x²|^{−α}) are C^∞(R) (proof: all one-sided derivatives at x=±1 vanish
to all orders because Φ's polynomial decay beats any finite-order pole from the θ∞ singularity).

**Result of applying Poisson to the m-sum (Altuğ I, Theorem 4.2, eq. (13), altug1.txt:1088–1112,
restated identically as Theorem 1.1 of the paper, altug1.txt:245–320):**
```
(4) + Σ() = p^{k/2}/2 · Σ_∓ Σ_{f=1}^∞ (1/f³) Σ_{l=1}^∞ (1/l²) Σ_{ξ∈Z} Kl_{l,f}(ξ,∓p^k) · [integral in x of θ∞^∓(x)·(F-term + H-term)·e(−xξp^{k/2}/2lf²) dx]
```
i.e. the dual sum runs over an INTEGER Fourier-dual variable **ξ ∈ Z**, weighted by a
**Kloosterman-type sum** Kl_{l,f}(ξ, ∓p^k) (defined altug1.txt:283–300 as a twisted additive
character sum over a mod 4lf² with a²±4p^k ≡ 0 mod f² and (a²±4p^k)/f² ≡ 0,1 mod 4 — footnote 8,
altug1.txt:326–328, explicitly identifies the q≠p, f=1, gcd(ξ,q)=1 special case as **the
classical Kloosterman sum S(2̄ξ, 2ξp^k; q)**), against an archimedean integral of θ∞^∓ times the
(F,H)-transform of the AFE evaluated at a shifted/twisted argument.

**Σ() — the "missing lattice points" correction term (altug1.txt:1005–1010, defined explicitly
altug1.txt:322–332):** the raw m-sum in (4) excludes m with m²±4p^k = □ (perfect square) because
L(1,χ) has a pole there; Σ() is the analytically continued/regularized contribution of exactly
those excluded points, added back in BEFORE Poisson summation is applied (this is "problem 1"
of §4.1, altug1.txt:1013–1021) — do not omit Σ() when reconstructing (4)+Σ() numerically, it is
part of the object being Poisson-summed, not a separate correction applied after.

**The special role of ξ=0 (Altuğ I, §6, Theorem 6.1, altug1.txt:1868–1935; and Altuğ III §4.1.2,
altug3.txt: line ~ "4.1.2 Analysis of the term ξ = 0"):** the ξ=0 term of the dual sum, denoted
(13)_{ξ=0}, is EXACTLY the piece isolated and identified with **tr(1(f^{p,k})) − tr(ξ_0(f^{p,k}))**
in Theorem 1.1's master formula — i.e. ξ=0 isolates the trivial representation's trace minus the
residual-Eisenstein-series ("special representation") trace. Concretely, Theorem 6.1 evaluates
(13)_{ξ=0} in closed form as an explicit combination of a residue term
`2p^{k/2}(1−p^{−(k+1)})/(1−p^{−1}) Σ_∓ ∫θ∞^∓(x)dx` plus two contour integrals against ζ(2u+2)/ζ(u+2)
and ζ(2u)/ζ(u+1) Euler-product ratios (visible directly in the displayed formula,
altug1.txt:1889–1899) — the zeta-function ratios appearing here are the concrete mechanism by
which "isolating ξ=0" recovers the trivial representation: its trace is literally built from
values/residues of ζ(s), consistent with the trivial representation being the "s=1 pole"
detector object in the Langlands proposal.

**The remaining terms (ξ≠0):** these are Part II's object (see §(4) below) — Fourier transforms
of the smoothed archimedean weight (the θ∞^∓ · AFE-term integral against e(−xξp^{k/2}/2lf²))
combined with the Kloosterman sums Kl_{l,f}(ξ,∓p^k), summed/estimated to extract the o(X)-type
control needed for analytic applications.

---

## (4) THE ARCHIMEDEAN TRANSFORM

**Not a single Bessel function — a Mellin-Barnes-type integral transform against derivatives of
a fixed profile (Altuğ II, Appendix A.1.3, Definition A.6, altug2.txt:1905–1930):** for
`h_a(x) = |1−x²|^{a/2} h_1(x)` with h_1 smooth on (−1,1) and prescribed asymptotic expansion
`h_a(±(1−x)) ∼ |x|^{a/2} Σ_m c_m^± x^m` near x=±1, define for Φ ∈ Schwartz space, m∈N, τ∈C
with ℜ(τ)>0:
```
A^{τ,±}_{h_a,m}(Φ)(x) := (1/2πi) ∫_{(τ)} Φ̃(u) c_m^±(u/2) Γ(m+1+(a+u)/2) x^{−u/2} du
```
where the coefficient function c_m^±(u/2) is itself an explicit oscillatory sum
`c_m^±(u/2) = 2π i^{1+m+(u+a)/2} Σ_{j+k=m} c_k^± / (2j (−2)^j)` (altug2.txt:1920–1925) — this is
the archimedean transform whose asymptotic behavior (decay for large x, log-power growth for
small x, Propositions A.7/A.8, altug2.txt:1932–1949) drives the main results.

**Main asymptotic-expansion theorems (Theorems A.14 and A.15, altug2.txt:2452–2620):**
Theorem A.14 gives, for `h_a` as above and any τ,τ1>0, M∈Z>0:
```
∫_{-1}^1 h_a(x) Φ(C/√(1−x²)) e(xD) dx  =  Σ_{m=0}^M e(±D) A^{τ,±}_{h_a,m}(Φ)(∓C²D) / (∓D)^{m+1+a/2}  +  O((C²D)^{−τ1} D^{−(M+2+a/2)})
```
uniformly in C,D≠0, with the implied constant independent of C,D (the paper repeatedly stresses,
altug2.txt:2447–2449, that *"independence of the implied constants of the parameters C and D is
the central issue"* — this uniformity, not the transform's closed form per se, is what the whole
appendix is built to secure). Theorem A.15 is the companion statement for the other family of
singular profiles that appear (h having the singularity type paired with the H-transform rather
than the F-transform of the AFE).

**Where Altuğ himself names the difficulty (Altuğ III, §4.2.2 "Estimating the critical range,"
altug3.txt:1757–1800, verbatim quote at altug3.txt:1793–1795):**
> *"The only difficulty in executing this simple strategy is that the function G is not alone.
> It comes as the product of G(n/X)·I_{l,f}(ξ,n) so that one needs to get the decay properties
> of the Fourier transform of this product uniformly in all the variables, and this is done in
> Proposition 5.2 of §5."*
This is the precise, named analytic obstruction in the executed GL(2)-standard-representation
case: not the existence of the archimedean transform's closed form (that's Theorem A.14/A.15),
but securing UNIFORM decay of the Fourier transform of a **product** of an arbitrary smooth
cutoff G and the already-complicated smoothed-orbital-integral transform I_{l,f}(ξ,n), across
all of the parameters (ξ, l, f, X) simultaneously. This uniformity requirement is what forces
the long technical Appendix A of Part II and §5 of Part III to exist.

---

## (5) THE SIX TRAPS — pinned

**(a) Class number vs. class number × regulator:** RESOLVED, see §(1). vol(γ) = 2h(γ)R(γ) for
D_γ>0 (real quadratic — class number TIMES regulator, no roots-of-unity factor since real
quadratic unit groups are infinite/rank 1) and vol(γ) = 2πh(γ)/ω_γ for D_γ<0 (imaginary
quadratic — class number over roots-of-unity count, no regulator since the unit group is
finite). Both collapse into vol(γ) = √|D_γ| L(1,χ_{D_γ}) via Dirichlet's class number formula —
this is the form actually used going forward (eq. (3), altug1.txt:475–491), so in practice one
never needs to separately compute h, R, ω — just the L-value.

**(b) Exact truncation/smoothing parameter:** RESOLVED, see §(2). General machinery: any
`A = |discriminant|^α`, α ∈ (0,1) free (Prop 4.1 / Theorem 4.2, Altuğ I). Executed instance:
**α = 1/2 exactly** in Altuğ III (Lemma 4.4, altug3.txt:718, "we take α = 1/2").

**(c) Fundamental discriminants vs. all:** RESOLVED. The elliptic sum (eq. (4)) is explicitly
over ALL m with m²±4p^k ≠ square, and the f-sum inside is over ALL square divisors f²
of m²±4p^k satisfying (m²±4p^k)/f² ≡ 0,1 mod 4 (i.e. every f such that the quotient is *some*
discriminant, not necessarily fundamental) — this is by construction, since L(z,δ) of eq. (5) is
DEFINED as that sum over all such f, precisely so that the resulting L(z,δ) is the one satisfying
the clean functional equation Λ(z,δ)=Λ(1−z,δ). Altuğ III Lemma 4.2's proof (altug3.txt:585–612)
makes the fundamental-discriminant decomposition explicit: writing m²−4n = D(m,n)·s(m,n)² with
D(m,n) the fundamental discriminant of Q(√(m²−4n)), the class-number-weighted sum over ALL f
(not just f=1, i.e. not just the fundamental discriminant alone) reduces via Cox's Theorem 7.24
to `2s(m,n)h(D(m,n))/ω_{D(m,n)} · Π_{q|s(m,n)/f}(1 − (D(m,n)/q)/q)` summed over f | s(m,n) — so
non-fundamental discriminants (orders) are folded in as an explicit local Euler-factor
correction to the fundamental piece, not excluded and not treated separately.

**(d) The archimedean transform's precise definition:** RESOLVED, see §(4) — Definition A.6 of
Altuğ II (Mellin-Barnes transform with Γ(m+1+(a+u)/2) kernel against Mellin transform Φ̃ of the
Schwartz weight, times an explicit oscillatory coefficient c_m^±(u/2)), NOT a bare K-Bessel
function evaluation (the prior scout's guess of "K-Bessel-type" is directionally right in that
K-Bessel functions appear as ingredients of H_0, H_1 via F̃'s closed form F̃(z)=K_z(2)/(zK_0(2))
— but the archimedean transform proper, in the sense of "the thing whose asymptotics are the
paper's main theorem," is the Definition A.6 Mellin-Barnes integral, one level more complex than
an off-the-shelf `scipy.special.kv` call).

**(e) Analytic vs. arithmetic L-normalization:** RESOLVED for this trilogy specifically — Altuğ
III's Theorem 1.1 states explicitly (altug3.txt:129–132) that Hecke eigenvalues are "normalized
so that the Ramanujan conjecture reads as tr(T_k(n)) = O_{k,ε}(n^ε)" (i.e. UNITARY/analytic
normalization, |α_p|=1 convention), and Corollary 1.2's remark (altug3.txt:151–154) flags the
conversion cost explicitly: *"because of normalization issues (i.e. with the above definition of
τ(n) the Ramanujan conjecture would read as τ(n) = n^{11/2+ε}) the usual line ℜ(s)=1 is shifted
to ℜ(s) = 1+11/2"* for the CLASSICAL (unnormalized, weight-12) L(s,Δ) — i.e. going from the
paper's analytic normalization (critical line at 1) to the classical Ramanujan-∆ normalization
(critical line at 1+11/2 = 13/2) is exactly a shift by (k−1)/2 for weight k=12. Get this shift
right before comparing against classical tables (e.g. LMFDB's L(s,Δ) uses the classical/motivic
normalization, not Altuğ's).

**(f) Functional-equation convention:** RESOLVED, see §(2) — it is s ↔ 1−s (analytic
normalization) throughout the trilogy: Λ(z,δ)=Λ(1−z,δ) (Altuğ I Prop 3.1) and, per (e) above,
Theorem 1.1 of Altuğ III is stated in the s↔1−s (analytic) convention for the standard
L-function, with the classical s↔k−s convention appearing only in the derived Corollary 1.2
about Δ, and there the shift is made explicit and quantified (not left implicit).

---

## (6) THE STATED OBSTRUCTION — verbatim quotes

**Sarnak's obstruction to Sym³ and higher (Altuğ III, footnote 5, p.5, altug3.txt:319–323) —
this is THE single most important correction to the prior scout's notes, which had only a
paraphrase from an unrelated 2025 note flagged as unverified. The actual primary-source
statement is:**
> *"We remark that applying Poisson summation on the n-sum works well for the standard
> representation and the symmetric square, however stops being productive for higher symmetric
> powers. This point was observed by Sarnak and we refer to [Sar01] for further discussion of
> this issue."*
Note the precise cutoff: **standard rep (Sym¹) AND Sym² both work**; the wall is at **Sym³ and
above**. This directly contradicts reading the obstruction as "Sym² is already where it breaks"
— Sym² is on the working side of the line per Altuğ's own footnote. [Sar01] = Sarnak's cited
reference (full citation not extracted in this session — appears in Altuğ III's bibliography,
not independently pulled).

**Arthur's Problem VI — an unexplained exact cancellation (Altuğ III, §1.1 last remark,
altug3.txt:225–260):** Altuğ reports, as a "peculiar phenomenon," that when computing
lim_{X→∞} (1/X) Σ_{n<X} tr(T_k(n)) via the trace formula, the three geometric contributions
(elliptic, hyperbolic+unipotent, identity) individually have NON-ZERO limits —
```
lim (1/X)Σ(elliptic) = 1/(k−1),   lim (1/X)Σ(hyperbolic+unipotent) = 1/(1−k),   lim (1/X)Σ(identity) = 0
```
— which sum to exactly 0 (matching Ress=1 L(s,π)=0, expected since the standard L-function has
no pole). But summing over PRIMES p<X instead of all n<X, each of the three individual limits
is separately 0 (eq. (3), altug3.txt:255–259). Altuğ states: *"An interesting question, also
raised by Arthur (cf. Problem VI of [Art15]), is to understand if there is a conceptual
explanation for the averages to behave in this way."* — i.e. this exact elliptic/hyperbolic
cancellation, sourced from prime-power (p^l, l large) conjugacy classes, is flagged by Altuğ
himself as unexplained and connects directly to a named open problem of Arthur. This is a
genuinely new, load-bearing fact not in the prior scout's abstract-only pass.

**Restriction acknowledged as a simplification, not a fundamental limit (Altuğ III, §1.1,
altug3.txt:163–182):** Altuğ is explicit that restricting to S={∞} (full level) and to
holomorphic-discrete-series test functions at ∞ (excluding Maass forms and the
continuous/non-tempered spectrum) is a *choice for expository clarity*, not a structural limit
of the method: *"The analytic difficulties related to the elliptic part are already present in
the Selberg trace formula, and this is why we chose this approach rather than working in the
generality of [Alt15a] and [Alt15b]. We should also note the analysis carried out in these
references are sufficient to carry out the analysis without any restriction on the archimedean
test function."* — i.e. Parts I/II's machinery already covers general f∞; Part III's
restriction to classical holomorphic cusp forms is for expository economy only.

**GL(3)/Deng–Espinosa's stated obstruction (arXiv:2603.21506, abstract + §1.2.1,
deng_espinosa.txt:8–13, 322–334) — the entire result is CONDITIONAL:**
> Abstract: *"assuming Conjecture A, we isolate the contribution of the trivial
> representation..."*
> §1.2.1: *"However, we were unable to successfully prove that it coincides with Yun's zeta
> function. Nevertheless, in all cases where we can compute both functions, they coincide. We
> thus put forward the following Conjecture A [that Yun's zeta function J_R(s) = L(s,R)ζ_Q(s)
> for R a Gorenstein order]... One can easily verify the conjecture for GL(2). In GL(3), in
> principle this can be derived from our computations in the appendix. In addition, we expect
> modifications for GL(n) for n > 3."*
This is the precise, primary-sourced GL(3) obstruction the prior scout flagged as unknown: the
functional equation Λ(s,R_0)=Λ(1−s,R_0) that the whole AFE-then-Poisson strategy needs is
proved ONLY MODULO an unproven identity (Conjecture A) between two zeta functions attached to
cubic orders. Without Conjecture A, only the value at s=1 (matching the orbital integral) is
secured — not the functional equation, hence not the AFE step. A second, independent
obstruction is flagged later (deng_espinosa.txt:483–491): reciprocity/splitting symbols that
worked uniformly for quadratic fields (Kronecker symbol) have **no uniform analogue across
cubic fields** (Galois cubic needs only cubic+quadratic Hecke characters of the field itself;
non-Galois cubic needs characters of the Galois closure) — quote: *"it does not seem possible
to write uniform formulas from which the extension and periodicity can be read off."* The paper
works around this by indexing directly over orders rather than integers/conductors, at the cost
of pushing the difficulty into the coefficient behavior and the Kloosterman-sum evaluation
(Appendices A–D, ~60 pages of local computations for (q,6p)=1, q=p^k, p=2, p=3 separately).

---

## (7) The negative-numerics finding, reconfirmed

The prior scout's §5 conclusion (no floating-point instrumentation of these sums exists in the
literature) is UNCONTRADICTED by anything found in the primary text. If anything, Altuğ I's own
line (altug1.txt:44, verbatim: *"We also note that in [13] the elliptic part, although
numerically analyzed, was not treated."*) — flagged by the prior scout as a possibly-hallucinated
search artifact and marked "do not rely on this phrase" — is in fact a **verified, exact quote
from the primary source** (referring to Langlands' original 2004 paper [13], not to Altuğ's own
work). This should be un-flagged: it is real, sourced, and now pinned to altug1.txt:44 /
Compositio 151 (2015) p.3. It describes Langlands (2004), not Altuğ, as having "numerically
analyzed" (informally/heuristically estimated, not floating-point-evaluated with code) the
elliptic part without a full treatment — consistent with, not contradicting, the broader
negative numerics finding.

---

## File index

- `/Users/samuellavery/work/helix_frobenius/tmp/altug_pdfs/altug1.{pdf,txt}` — Part I (Compositio
  2015, arXiv:1506.02218)
- `/Users/samuellavery/work/helix_frobenius/tmp/altug_pdfs/altug2.{pdf,txt}` — Part II (Amer. J.
  Math 2017, arXiv:1506.08911)
- `/Users/samuellavery/work/helix_frobenius/tmp/altug_pdfs/altug3.{pdf,txt}` — Part III (JIMJ
  2020, arXiv:1512.09249)
- `/Users/samuellavery/work/helix_frobenius/tmp/altug_pdfs/deng_espinosa.{pdf,txt}` — GL(3)
  Poisson summation (arXiv:2603.21506, 122pp confirmed)
