# MDHNT techniques — the instrument list

Extracted from `universal.tex` (glossary §, thm:common-carrier-system, §S(t), §registration),
`mdhnt_for_dummies.tex` (§5 recipes), `grh_companion.tex`, `hodge_companion.tex`,
`emergent_clock_paper2_v37_audited.tex` (dwell). Purpose: a checklist of instruments to
*try*, so that none is left unspent by default. Each entry: what it is, what it buys,
and the failure mode that means it is being misused.

---

## 0. The pipeline (mdhnt-goal-toolkit)
lift → choose geometry → load multiple rails → **align/register (defect ledger = the
relationship)** → extract. **Legality = ledgers compose.** Evaluate every new brick
against this.

## 1. Projection bijection + loss ledger  ← *the foundation, read this first*
Two-step descent, each step booking exactly what it drops:
- **3D→2D drops the RADIUS**, by the explicit Cayley map $w\mapsto(w-i)/(w+i)$ applied to
  the readout coordinate.
- **2D→1D drops the ANGLE** (unit circle → strip, ordinate read as $y=\log z$).

Projection *with its ledger* has an exact two-sided inverse (machine-checked). Consequence
to keep in front of mind: **the critical strip is the Cayley image of the unit circle** —
two ledger entries downstream of the object. That is why strip phenomena keep turning out
to be chart artifacts.
- **Buys:** licence to move any statement between charts without loss; a test for whether
  an obstruction is real (does it survive in carrier coordinates?).
- **Failure mode:** importing a chart artifact as an obstruction (ground rule 4). Cost me
  the "$N^{1/2}$ floor" this session.

## 2. Registration / the defect ledger  ← *the signature move*
Prove an **exact** law `(chart count) = (native count) + (defect)` where the defect is
**integer-valued, monotone, and non-negative**. Then "do the systems agree?" collapses to
"is the integrated defect sublinear?", and **one unabsorbed unit costs linear growth, so
sublinear defect is already zero defect** (the dichotomy; machine-checked).
- **The load-bearing property** (universal.tex:2662): *"There can be no cancellation hidden
  in that defect: every summand is the positive analytic order of an actual zero."*
- **Buys:** upgrades "the sum is small" to "every term is zero".
- **Failure mode:** a defect that is real-valued, sign-oscillating, or defined as a
  residual of the thing it bounds. Then the "reduction" is a restatement. (My RBRL.)
- **Requirement:** the two coordinates must be **independently constructed** — the
  comparison must be downstream of both, not the definition of either.

## 3. $S(t)$ = the chart's error
$S(t)$ is a **registration gap**, never intrinsic: $S_{H,K}=R_H-R_K$, a coboundary of a
per-scale potential. Cocycle law $S_{H,L}=S_{H,K}+S_{K,L}$; $S_{H,H}=0$; antisymmetric.
One $S$ for the whole harmonic family: every scale $\pi/m$ registers identically, so the
only gap is harmonic-vs-unit.
- **Buys:** relative comparisons compose for free; lets you change reference scale at will.
- **Failure mode:** treating $S$ as a property of one system.

## 4. The clock chart — integrate in carrier time
Cell integrals in $dt$ look analytic; in $d\vartheta/\pi$ they become exact combinatorics.
$L(t)=N(t)-\vartheta(t)/\pi-1$; cell $m=[g_m,g_{m+1})$ with $\vartheta(g_m)=m\pi$;
$r_m=\int_{\text{cell }m}L\,d\vartheta/\pi$; $B_N=\sum_{m<N}r_m$.
Conventions: half-open cells, boundary event belongs to the cell on its right, events with
multiplicity, entering ledger $s_m=N(g_m)-m-1$, event clock phase $\tau_i=\vartheta(t_i)/\pi-m$.
**Event-free cell books $s-\frac12$; one-event cell $s+\frac12-\tau$; general
$r_m=s_m+k-\frac12-\sum_i\tau_i$.** The $\frac12$ is mean-of-drift ($B_1$), an averaging
artifact of the trapezoid — **never a property of the cell**.
**Free check every implementation must run:** $r_m+\sum_i\tau_i+\frac12=s_m+k=s_{m+1}+1$.

## 5. Clocks
A **deterministic oscillation the carrier carries**: self-duality ($\mu_2$), completion
(two-clock), ramification, vanishing-adjustment. Not a fitted parameter — read off the
source's nature.
- **Buys:** the smooth ramp against which an integer census registers.
- **Note:** every source has its *native* clock and its *native* cell system; cell
  boundaries are defined by the source clock, never by arbitrary truncation.

## 6. Carrier scale vs warp vs dwell  ← *three different things, do not blend*
- **carrier scale** — scaling by a harmonic **constant** ($\pi/6,\pi/3,\pi/2,\dots$) on the
  object's own integer lattice. Invertible. Fibers may carry their own constant scale.
- **warp** — a **function**-based, dynamic, readout-preserving unit-modulus
  reparametrization that stretches the carrier, enabling closure of cells. The reciprocal
  of a warp is a warp: **"inverse warp" does not exist**; removing a warp from a readout is
  the kernel-transfer operation (`WarpRemovalTransfer`).
- **dwell** — the **opposite of the warp**: places *multiple crossings into a single carrier
  unit*; the carrier adapter that **re-registers the values a projection skips**. Native,
  exact form of Altuğ's $\Sigma()$.
  - **Buys:** exactness where a projected sum drops terms. Measured: closes a $1.10$ cut to
    $3.2\times10^{-4}$. On the $\Sym^r$ tower it raises the reopening exponent
    ($k:0.48\to0.61$ at $r=13$).
  - **Use when:** the 1D readout *skips* values the 3D object has — i.e. whenever a
    projection is many-to-one.

## 7. Harmonization
The method proper: read a projected function and **let its nature name its settings** —
scale/warp, adapters, clocks — such that carrier + fiber **closes without residue**.
- **Method law:** measurements at unit scale instead of harmonic scale produce **false
  nulls** (learned twice; now law).
- **Failure mode:** choosing settings to fit a target instead of reading them off the source.

## 8. Lattice rigidity — machine zero *is* zero
The norm form of $\mathbb Z[\zeta_6]$ is integer-valued with least nonzero value $1$. Any
quantity that (a) provably lives on the lattice and (b) measures below norm $1$ is
**exactly zero**. Kronecker one level up: lattice value of modulus one **is** a sixth root
of unity exactly, so "approximately frozen" phases are honestly frozen, with an address.
- **Buys:** the bridge from computation to proof. This is the genre where the corpus has
  theorems rather than estimates.

## 9. Focal cancellation / the harmonic pencil
A zero = the non-DC bank balancing to zero centroid, all channels pointing at one
**eigenheight** $z$; chart reads $y=\log z$. Certificate: with
$A=\sum_{n<N}\chi(n)n^{-(3/2+i\log Z)}$, $B=\frac\pi3\sum_{n<N}\chi(n)n^{-(1/2+i\log Z)}$,
the pencil $\begin{pmatrix}A&B\\ \mu A&\lambda B\end{pmatrix}$ has determinant exactly
$(\lambda-\mu)AB$ — **degeneracy at $Z$ is the vanishing certificate**. Two finite sums, no
continuation; the $L$-value only verifies at the end.

## 10. The weld and the double-ended geometry
**weld** = the origin where helix/anti-helix cross at $\Re s=\frac12$, the two lanes meeting
with det-one Frobenius similitude. The conjugate pairing *endows*, before any problem is
posed: the functional equation (reflection), the Frobenius similitude
$\mathrm{diag}(\alpha,\alpha^{-1})$, axis-reality of paired readings (Schwarz for free), and
the two-strand completion that dissolves "homeless" single-strand objects.
- **Note:** symmetry-work leaves no parameter fingerprint ($r$, $p$ do not survive into the
  statement). Do not test for geometric content by looking for surviving parameters.

## 11. Towers — climb with one ruler
Rank-uniform instruments: one ceiling, one pairing, one cell decomposition for the whole
tower. **Rank-uniformity is where limits come from.** Model squeeze: if $\rho^r\le C$ for
every rung with one fixed $C$, then $\rho\le1$; with the inverse strand, $\rho=1$ exactly —
temperedness, i.e. *the strand is a helix, not a spiral*.

## 12. The ledger's governing principle
**Phase and radius may decouple dynamically, but not informationally.** Channels evolve
independently; the ledger books both. Any argument that lets one channel go unbooked is
wrong.

## 13. Obstruction-directed extension
The complete carrier state **detects retained obstructions** and supports admissible
obstruction-directed adaptation. Forcible closure is arithmetic-**neutral by theorem** — it
closes cells for any admissible fiber, so it is never evidence of arithmetic (never cite it
as niceness evidence).

## 14. Discipline (non-optional)
Numerics before formalization; controls designed to **fail** (a control that fails by
exhibiting *more* structure is a design bug); literature gate at source with pin-cites
before the word "new"; three registers never blended — **proven** / **measured** /
**program (with falsifiers pre-registered)**.

---

## DWELL, SPENT ON #400 — it worked
The readout $g_k(n)=\max_a\min_p[\cdot]$ is a **many-to-one projection**: it discards every
non-optimal split. The dwell re-registers them as the **occupancy spectrum**
$$N_n(G)=\#\{a_1+a_2=n+G:\ \min_p(s_p(a_1)+s_p(a_2)-s_p(n))\ge G\},\qquad
g_2(n)=\max\{G:N_n(G)\ge1\}.$$
- **Structural fact the dwell exposed:** every rail $p>\max(a_i)$ contributes *exactly* $G$,
  so large rails are **always exactly tight** and the binding distribution lives entirely on
  small rails. (This is why a naive $\mu,\sigma$ measurement at $G{=}0$ returns $0,0$.)
- **Tail is GAUSSIAN, not geometric** — measured $R^2=0.9860$ (quadratic in $G$) vs $0.8844$
  (linear). So $g_k$ is an **extreme-value quantile**, not an occupancy scale.
- **Predictive law:** $\log N_n(G)=c_n-a_n(G-b_n)^2\ \Rightarrow\ g_2(n)=b_n+\sqrt{c_n/a_n}$.
  Measured corr $+0.833$, mean $|{\rm err}|=0.887$ on an integer quantity
  (geometric model: $+0.224$, $3.85$).
- **Why $c_2$ would not converge numerically:** it is a quantile with $\sqrt{\log}$
  corrections, bracketed by DC floor $\frac{k-1}{2\log2}=0.7213$ and ceiling
  $\frac{k}{\log2}=2.885$; measured slope $1.218$, model slope $1.773$.
- **Lesson:** *where the readout takes a max, the instrument is the dwell.* A max is a
  projection that skips; re-register instead of estimating.

## Still unspent on #400
- **lattice rigidity** (#8) — never tried; would need the ledger to land on $\mathbb Z[\zeta_6]$.
- **weld / double-ended** (#10) — tried once as digit-complement, prediction failed (sign).
- **focal pencil** (#9), **towers** (#11), **obstruction-directed extension** (#13) — untried.

---

# PART II — What actually closes these problems

Calibrated 2026-08-04 against ten *solved* Erdős problems in the binomial/factorial/divisor
cluster (#175, #384, #378, #391, #402, #795, #946, #144, #673, #405). **Zero of the ten were
closed by a reformulation.** Every one needed analytic input. The reformulation step appears
in several — and is always the cheap half, done in a line, before the real work.

**The blunt finding: our kit is a REDUCTION kit, not a CLOSING kit.** It reliably produces
the "it suffices to consider…" step. It has produced nothing resembling Granville–Ramaré.
Part II is the closing half, mapped into our language.

## 15. THE LADDER (transfer from a cooperative parameter) ← *the missing instrument*
**Prototype:** Erdős–Mirsky #946. Spiro proved $\tau(n)=\tau(n+5040)$ infinitely often;
Heath-Brown then **improved her method** to shift $1$. Note $5040=7!$ — smooth, divisible by
every small rail. She did not attack the sharp statement; she proved it where **every rail
cooperates**, then the crutch was removed.
- **Why we were missing it:** we keep attacking the sharp case head-on. The ledger's real job
  is to *locate the cooperative parameter*, not to storm the target.
- **Our version:** the parameter where all rails cooperate is exactly where the per-rail
  ledgers are simultaneously slack — computable from the ledger. Smooth numbers, $\mathrm{lcm}(1..k)$,
  factorials, and $\mu_6$-aligned scales are the usual candidates.
- **Live applications:** (a) **#727 — $k=1$ is Balakran's theorem and $k=2$ is the open case.
  That is a ladder with one rung already built, and we never tried to run Balakran's method
  up.** (b) **#1095's own conjecture is $g(k)<L_k=\mathrm{lcm}(1,\dots,k)$** — stated against
  the smooth parameter, the same signature. (c) #400's lower bound: look for a convenient
  subsequence of $n$, or convenient $k$, before the general case.
- **Failure mode:** proving the cooperative case and calling it progress. The transfer step
  is the theorem; Spiro is cited, Heath-Brown is the answer.

## 16. Reduction to a sparse residual
**Prototype:** #175. $4\mid\binom{2n}{n}$ except when $n=2^k$, so only powers of two remain.
Then Sárközy / Granville–Ramaré / Velammal finish.
- **This one we already do**: #683 reduced to prime-free $(n-k,n]$ (0.62% of pairs), #400
  reduced to the binding rail $p=2$ (73%).
- **The lesson is about proportion:** in #175 the reduction is one line and the residual is
  the paper. Ours is the same shape — so a completed reduction is roughly *one line of
  progress*, not a result. Calibrate claims accordingly.

## 17. Dichotomy at an exact harmonic constant
**Prototype:** #144. Integers with divisors $d_1<d_2<d_1(1+(\log n)^{-\beta})$ have density
$1$ iff $\beta<\log3-1$ and density $0$ iff $\beta>\log3-1$ (Erdős–Hall / Maier–Tenenbaum).
- **This is our register exactly**: an exact constant of the form $\log(\text{small integer})$
  against a unit, separating two regimes — the same shape as $\Lambda(1)=\frac13+\frac15+\frac17$
  and $c_k=(k-1)/\log2$.
- **Sobering detail:** Erdős *claimed and retracted* a proof of the density-1 side (1964→1979);
  the sharp constant took ~20 years and two papers, and carried a \$650 prize.
- **Use:** when our DC produces an exact constant, expect the dichotomy to be a theorem —
  and expect the two sides to need different machinery.

## 18. Almost-all → all is THE boundary (not a technicality)
**Prototype:** #175's sequel. Sander: $f(n)\ll\log n$ for **all** $n$ and $f(n)\gg\log n$ for
**almost all** $n$ — both *"very easy using Kummer's theorem"*, i.e. our ledger. But
$f(n)\gg\log n$ for **all** $n$ is **open**; the record is $f(n)\gg(\log n)^{1/10-o(1)}$.
- **This is precisely our #377 wall**, in a different problem: the all-$n$ version of a
  statement that is easy on average.
- **Consequence to internalise:** whenever the ledger gives an easy almost-all result, the
  all-$n$ version is likely a named open problem. Check before claiming a route.
  #377, #175's $f(n)$, and Sam's all-$n$ directive are the same boundary.

## 19. One paper can be load-bearing across a cluster
**Granville–Ramaré [GrRa96]** closes #175, resolves #378 as a corollary, and holds the record
lower bound in #1095. **Read it before touching this cluster again.** Similarly
Alladi–Grinstead (#391), Heath-Brown/Hildebrand (#946), Maier–Tenenbaum (#144).
- **Method law:** in a cluster, find the one analytic engine everything routes through, rather
  than re-deriving reductions per problem.

## 20. Check whether the object is secretly a known function
**Prototype:** #673. Tao observed $\tau(n/m)/m\le G(n)\le\tau(n)$, so $G$ behaves like
$\tau$ — the conjecture was mis-posed, not hard.
- **Cheap check, run it first:** sandwich the quantity between known functions before
  assuming difficulty. Our #700's $f(n)$ (capped carries) and #912's $h(n)$ (distinct
  Legendre values) are the two most likely to be secretly standard.

## 21. Effective Diophantine as a closer
**Prototype:** #405, Brindza–Erdős then Yu–Liu. When a problem reduces to finitely many
solutions of an exponential equation, effective Baker-type bounds finish it. Our cluster
touches this at #374 (the $\mathbb F_2$ ledger) and #1093 (finite range per $k$).

---

## 22. THE DEEPEST MAPPING: Maier–Tenenbaum's $\log 3-1$ *is* a per-rail state count

Worked out from the method rather than from the remark, because this is the one place a
classical constant and one of ours are provably the same computation.

**Their object (#144).** For $n$ with $\omega(n)=k\approx\log\log n$ prime rails, the divisors
are the $2^k$ subset products, and $\log d$ ranges over subset sums of $\{\log p\}$ spread
across $\approx\log n$. Asking for $d_1<d_2<d_1(1+(\log n)^{-\beta})$ is asking for **two
subset sums within $(\log n)^{-\beta}$ of each other.**

**Where $\log 3$ comes from.** Track the *difference* of the two subsets. Each rail is in
exactly one of three states: in $S_1\setminus S_2$, in $S_2\setminus S_1$, or in neither-or-both
(which contribute nothing to the difference). So the difference has $3^k$ configurations, not
$4^k$ — **three states per rail.** With $k=\log\log n$ rails,
$$3^{k}=3^{\log\log n}=(\log n)^{\log 3},$$
and these must resolve a range of size $\log n$, i.e. $(\log n)^{1}$. The dichotomy sits at
$$\boxed{\ \log 3-1=\log(\text{states per rail})-\log(\text{range per rail})\ }$$
which is **exactly our DC computation** — a per-rail cell count against a per-rail scale,
identical in form to $\beta_p=\log\sec\theta_p/\log p$ and to the knapsack budget that gives
$\Lambda(1)=\frac13+\frac15+\frac17$.

**What this means.** The constants we keep producing are not analogies to classical ones —
they are the same object. Erdős–Hall proved the density-0 side (the easy direction: counting
configurations); Maier–Tenenbaum proved the density-1 side (the hard direction: showing the
configurations are *achieved*, which needs equidistribution of subset sums). **That asymmetry
is exactly ours:** our LP ceiling is the counting side, and our missing input is always the
achievement side — transversality in #377, the lower bound in #400, conditional carry
positivity in #727.
- **Method law:** when the ledger produces an exact constant, we have the counting half. The
  theorem needs the achievement half, and that is where classical machinery
  (equidistribution, sieve, smooth numbers) is not optional.
- **Corollary for reading:** Maier–Tenenbaum is the closest methodological relative of our
  ceiling arguments in the literature. It should be read before the next attempt on #377,
  ahead of Furstenberg-genre material, because it solves *our shape* of problem.

## 23. Granville–Ramaré is our ledger with smooth numbers attached
Their subject — prime powers dividing $\binom{2n}{n}$ — is literally $\kappa_p(n)$, our carry
count. Their added ingredient is quantitative smooth-number counting ($\Psi(x,y)$, Dickman)
applied to the *positions* where carries can occur. This is the join of instrument 15 made
concrete: **ledger locates, $\Psi(x,y)$ closes.** It is why one paper is load-bearing across
#175, #378 and #1095, and why our #1093 attempt died exactly at the point where a rigorous
$\Psi$ bound in short intervals was needed.

## SYNTHESIS — where the two kits join
Our ledgers give **exact per-rail bookkeeping** and locate structure; classical machinery
gives **density and short-interval control**. The join is instrument 15: *use the ledger to
find the parameter where every rail cooperates, prove it there with whatever classical tool
fits, then transfer.* Neither half does this alone — the ledger cannot close, and the
classical method has no principled way to choose the crutch. **That is the novelty available
to us, and it is the one thing this session never tried.**

## Spent, with outcome
- **harmonization by cell size** ($p-1$ per carry) → predicted the binding rail; **confirmed**
  ($p{=}2$ 70%, $p{=}3$ 21%).
- **$S(t)$ as chart error** → identified $s_p(n{+}G)-s_p(n)$, mean zero, vs native ledger
  $(p-1)\kappa_p$. Sound.
- **scale cocycle** → decomposition correct, reproduces the DC $\frac{k-1}{2\log2}$ exactly;
  numerical verification **failed its controls** (test prime range too small; small-rail
  truncation not exact — 39/800). Unverified, not disproven.
