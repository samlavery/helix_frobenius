# Corso–Shmerkin extraction: the two bridges

Source read: **E. Corso, P. Shmerkin, "Dynamical self-similarity, $L^q$-dimensions and
Furstenberg slicing in $\mathbb R^d$", arXiv:2409.04608v1 (6 Sep 2024), 43 pp.**
Read at source from the PDF (`tmp/corso_shmerkin_2409.04608.pdf`, text at `tmp/cs.txt`);
page/line references below are to that text. No statement below is used unless transcribed
verbatim in §B.

---

## A. Verdicts

| Task | Verdict |
|---|---|
| **(1) Verification pass** on Cor 1.17 ⟸ Thm 1.15 ⟸ Thm 5.4 ⟸ inverse-theorem engine | **CLOSES WITH TWO DEFECTS**, both repaired here for our special case. (a) Hypothesis **(P1) of §5 is misprinted** — as written it is *false* for our measures; the intended hypothesis (confirmed by Remark 1.16 and by the proof of Lemma 5.1) is satisfied. (b) The last step of the proof of Theorem 5.4 **omits an a.e.-injectivity verification** that is genuinely needed; I supply it for our projection. Plus one harmless typo (`1/q'` for `1/q`, §6.2). |
| **(2) Constant extraction** | **GAP — the constant is ineffective, and the paper's own convention suppresses exactly the dependence we need.** Every *explicit* factor is harmless at our scale (all are $\exp(O((\log\log N)^2))\ll N^\varepsilon$). The blocker is the threshold scale $m_0$: $C\gtrsim 2^{m_0(1-\alpha-\varepsilon)}$, and $m_0$ is non-explicit, arising from (i) the inverse theorem of [19], (ii) a compactness argument, (iii) **unique ergodicity with no rate**. Separately, §2.2 declares "all implicit constants are allowed to depend on the ambient dimension $d$" — and our $d=k$ grows. |
| **(3) Truncation bridge** | **CLOSES.** Proved below (Lemma T). The proof does *not* go through the exact-fibre statement of Theorem 1.15 — that would not suffice — but through the **ball version in Lemma 6.1**, which is already $\delta$-robust. This is the correct consuming form. |

**Net:** the target theorem is in print (Corollary 1.17 with $d=k$, $g_j=\mathrm{id}$), and the
truncation bridge our assembly needs is derivable from the paper's Lemma 6.1. **The uniformity
in $(k,p_1,\dots,p_k)$ that our application requires is *not* available from this paper**, and
obtaining it is not a matter of bookkeeping: it requires an effective inverse theorem and an
effective equidistribution rate on the torus $X$.

---

## B. Transcribed statements relied on

All verbatim from arXiv:2409.04608v1.

**Theorem 1.15.** "*Let $p_1,\dots,p_d\ge2$ be pairwise multiplicatively independent integers.
Let $A_1,\dots,A_d\subset\mathbb T$ be closed sets which are invariant under the maps
$T_{p_1},\dots,T_{p_d}$, respectively. Write $s=\sum_{j=1}^d \dim_H(A_j)$. Then, for any
$1\le k\le d$ and any $(d-k)$-dimensional affine subspace $P\subset\mathbb R^d$ with
$Z(P^\perp)\le k-1$,*
$$\overline{\dim}_B\big(A_1\times\cdots\times A_d\cap P\big)\le\max\{s-k,0\}.$$
*Moreover, the previous holds uniformly in the following sense. Fix $\varepsilon>0$ and
$\eta>0$; then there is $C_{d,k,\varepsilon,\eta}>0$ such that, for all $\pi\in\mathbb G(d,k)$
with $Z_\eta(\pi)\le k-1$ and all affine subspaces $P$ orthogonal to $\pi$, the inequality*
$$\big|A_1\times\cdots\times A_d\cap P\big|_\delta\le C_{d,k,\varepsilon,\eta}\,
\delta^{-\max\{s-k,0\}-\varepsilon}$$
*holds for all $0<\delta\le1$.*"

**Corollary 1.17.** "*Let $p_1,\dots,p_d$, $A_1,\dots,A_d$ and $s$ be as in Theorem 1.15. Then,
for all affine maps $g_1,\dots,g_d:\mathbb R\to\mathbb R$,*
$$\overline{\dim}_B\big(g_1(A_1)\cap\cdots\cap g_d(A_d)\big)\le\max\{s-(d-1),0\}.$$
*Moreover, for any $\varepsilon>0$ and $K\ge1$, there is $C_{\varepsilon,K}>0$ such that, if the
slopes of the $g_j$'s are bounded above by $K$, then*
$$|g_1(A_1)\cap\cdots\cap g_d(A_d)|_\delta\le C_{\varepsilon,K}\,
\delta^{-\max\{s-(d-1),0\}-\varepsilon}$$
*for all $0<\delta\le1$.*"

**Remark 1.16.** "*As will emerge clearly from the proof of the theorem, presented in §6.2, the
sets $A_j$ can be replaced by homogeneous self-similar sets with contraction ratios $\lambda_j$,
under the assumption $\log\lambda_i/\log\lambda_j\notin\mathbb Q$ for all $i\ne j$, where the
generating IFS satisfies the open set condition.*"

**Definitions (§1.6, §1.8).** "$Z_\eta(v)=|\{j\in\{1,\dots,d\}:|v_j|<\eta\}|$";
"$Z_\eta(\pi)=\max\{Z_\eta(v):v\in\pi\cap S^{d-1}\}$"; "*the notation $|X|_\delta$ stands for the
$\delta$-packing number of $X$, that is, the largest cardinality of a $\delta$-separated subset
of $X$*"; "$N_m(X)=\Theta_d(1)|X|_{2^{-m}}$". For $\pi\in\mathbb G(d)$,
"$Z(\pi)=\sup\{Z(\pi_0):\pi_0\in\mathbb G(d,1),\ \pi_0\subset\pi\}$".

**Hypotheses of §5.** "*For the rest of this section, we fix $q>1$, and let
$\mu^{(1)},\dots,\mu^{(d)}$ be homogeneous self-similar measures on $\mathbb R$, described as in
(5.1), with the following properties:* **(P1)** *$\lambda_i/\lambda_j$ is irrational for all
$1\le i\ne j\le d$;* **(P2)** *the IFS generating $\mu^{(j)}$ satisfies exponential separation
for all $1\le j\le d$.*"

**Lemma 5.1.** "*Let $(\mu^{(j)})_{1\le j\le d}$ be as above, ordered so that
$\lambda_d=\max_{j}\lambda_j$. There exists a pleasant model
$\mathcal X=(X,\mathbf T,\mathbb P,\Delta,\lambda_d)$ in $\mathbb R^d$ such that: (1) $X$ is a
closed subgroup of $\mathbb T^{d-1}$, the map $\mathbf T$ is a translation on $X$, and
$\mathbb P$ is the unique probability Haar measure on $X$; (2) the generated measures are given
by $\mu_x=\lambda_1^{-x_1}\cdot\mu^{(1)}\times\cdots\times
\lambda_{d-1}^{-x_{d-1}}\cdot\mu^{(d-1)}\times\mu^{(d)}$ … In particular, for the identity
element we obtain $\mu_0=\mu^{(1)}\times\cdots\times\mu^{(d)}$.*"
Its proof sets "$a_j=|\log\lambda_j|$" and
"$\mathbf T(x_1,\dots,x_{d-1})=(x_1+\frac{a_d}{a_1},\dots,x_{d-1}+\frac{a_d}{a_{d-1}})$", with
$X$ "*the closure of the orbit of $0$ under $\mathbf T$*".

**Lemma 5.2.** "*If $\pi\in\mathbb G(d,1)$ satisfies $Z(\pi)=0$, then $\pi\mathcal X$ satisfies
projected exponential separation.*"

**Theorem 5.4.** "*Let $k\in\{1,\dots,d\}$, and suppose $\pi\in\mathbb G(d,k)$ satisfies
$Z(\pi)\le k-1$. Then,*
$$D_{\pi\mathcal X}(q)=\min\{k,D_{\mathcal X}(q)\}=\min\Big\{k,\sum_{j=1}^d
\dim(\mu^{(j)},q)\Big\}.$$"

**Theorem 1.9 (the engine).** "*Let $\mathcal X=(X,\mathbf T,\mathbb P,\Delta,\lambda)$ be a
pleasant model in $\mathbb R^d$ … Assume that $\mathcal X$ satisfies exponential separation and
is $q$-unsaturated on lines for some $q\in\mathbb R_{>1}$. Then,*
$$D_{\mathcal X}(q)=\frac{\int_X\log\|\Delta(y)\|_q^q\,d\mathbb P(y)}{(q-1)\log\lambda},$$
*and $\lim_{m\to\infty}-\frac{\log\sum_{Q\in\mathcal D_m}\mu_x(Q)^q}{m(q-1)}=D_{\mathcal X}(q)$
uniformly in $x\in X$.*"

**Theorem 2.1 (inverse theorem), quantifier structure only.** "*Fix real numbers $q>1$ and
$\delta>0$. There is a positive integer $L_0=L_0(q,\delta)$ such that, for all $L\ge L_0$, there
is $\varepsilon=\varepsilon(q,\delta,L)>0$ such that the following holds for every integer
$S\ge S_0(q,\delta,L)$: Let $m=SL$, and let $\mu,\nu$ be $2^{-m}$-measures on $[0,1)^d$ such that
$\|\mu*\nu\|_q\ge2^{-\varepsilon m}\|\mu\|_q$. Then, there exist subsets $A\subset\mathrm{supp}\,\mu$,
$B\subset\mathrm{supp}\,\nu$ such that … *" — the source of these claims is
"*[19, Theorem 1.2]*" = P. Shmerkin, *Inverse theorems for discretized sums and $L^q$ norms of
convolutions in $\mathbb R^d$*, preprint.

**Lemma 6.1.** "*Let $(X,d)$ be a metric space. Suppose $\pi:X\to\mathbb R^k$ is an $L$-Lipschitz
map, $L>0$. Let $\mu$ be a Borel probability measure on $X$ with the following property: there
are real numbers $0\le t\le s$, $C_1,C_2>0$ and an integer $m_0\ge1$ such that
$\mu(B(x,r))\ge C_1r^s$ for all $x\in X$ and $0<r\le2^{-m_0}$ and $\pi\mu(Q)\le C_22^{-mt}$ for
all $m\ge m_0$ and all $Q\in\mathcal D_m$. Then, for any $m\ge m_0$ and any closed Euclidean
ball $B\subset\mathbb R^k$ of radius $2^{-m}$,*
$$\big|\pi^{-1}(B)\big|_{2^{-m}}=O_{k,L,C}(1)\,2^{m(s-t)}$$
*for $C=C_2/C_1$. In particular, for any $y\in\mathbb R^k$,
$\overline{\dim}_B(\pi^{-1}(y))\le s-t$.*"

**§2.2, standing convention.** "*we adopt the convention that all implicit constants are allowed
to depend on the ambient dimension $d$. Any other dependencies will be made explicit.*"

**§3.3.5, parameter recapitulation.** "*We start by the given data in the hypotheses of Theorem
3.7, namely the model $\mathcal X=(X,\mathbf T,\mathbb P,\Delta,\lambda)$, the real numbers
$q>1$ and $\sigma>0$ and the ambient dimension $d$. All subsequent parameters can depend on this
data, without further mention … Finally, $m=LS\ge LS_0$ or, equivalently, $S_0$, is at many
places taken large enough in terms of all the previously mentioned parameters.*"

**§6.2, proof of Theorem 1.15 (the passage we consume).** "*Let $\mu^{(j)}$ be the natural
uniform self-similar measure on $A_j$ … the measure $\mu^{(j)}$ satisfies the Ahlfors regularity
condition $r^{\dim_H(A_j)}\ll\mu^{(j)}(B(x,r))\ll r^{\dim_H(A_j)}$ … Then, for any $q>1$ we have
$D_{\mathcal X}(q)=s$, and $r^s\ll\mu_0(B(y,r))\ll r^s$ for all $y\in\mathrm{supp}\,\mu_0$ and
$0<r\le1$. **Here the implicit constants depend on the $p_j$'s, but not on $y,r$.** … Take $q$
large enough that $1/q'<\varepsilon/(3d)$. By Proposition 3.2, for large enough $n$ (depending on
$\eta$ but not on $\pi$) … Since $m(n)$ has bounded gaps, this extends to all $m$ …*"

---

## C. Task 1 — verification pass

Our instance: $k\ge3$ odd primes $p_1<\cdots<p_k$; $D_j=\{0,\dots,(p_j-1)/2\}$,
$|D_j|=(p_j+1)/2\ge2$; $C_j=\{x:\text{all base-}p_j\text{ digits in }D_j\}$;
$s_j:=\dim_H C_j=\frac{\log|D_j|}{\log p_j}$, $s=\sum_j s_j$. We take $d=k$ in the paper's
notation and $g_j=\mathrm{id}$.

### C.0 Hypotheses of Theorem 1.15 for our sets — CLOSES
$C_j$ is closed; $T_{p_j}(C_j)\subset C_j$ (the shift deletes the leading digit, the rest stay in
$D_j$) ✓. $p_1,\dots,p_k$ distinct primes are pairwise multiplicatively independent ✓. So
Theorem 1.15 and Corollary 1.17 apply as stated.

### C.1 Cor 1.17 ⟸ Thm 1.15 — CLOSES
With $g_j=\mathrm{id}$, $\bigcap_j C_j$ is the image of $(C_1\times\cdots\times C_k)\cap P$,
$P=$ the diagonal line, under $(x_1,\dots,x_k)\mapsto x_1$. If $\{y_i\}$ is $\delta$-separated in
$\bigcap_jC_j$ then $\{(y_i,\dots,y_i)\}$ is $\delta\sqrt k$- hence $\delta$-separated in
$(\prod_jC_j)\cap P$, so
$$\big|\textstyle\bigcap_jC_j\big|_\delta\le\big|(\textstyle\prod_jC_j)\cap P\big|_\delta .$$
No metric loss in this direction. The hypothesis: $\pi=P^\perp=\{x:\sum_jx_j=0\}\in\mathbb G(k,k-1)$,
and a unit $v\in\pi$ cannot have $k-1$ zero coordinates (the last would be forced to vanish), so
$Z(\pi)=k-2=(k-1)-1$ ✓ — the hypothesis $Z(P^\perp)\le k-1$ is met with the parameter
$k_{\text{paper}}=k-1$.

**Quantitative form.** For the uniform statement we need $Z_\eta(\pi)\le k-2$. If $v\in\pi$ is a
unit vector with $|v_j|<\eta$ for $j\ne j_0$, then $|v_{j_0}|=|\sum_{j\ne j_0}v_j|<(k-1)\eta$, so
$1=|v|^2<(k-1)\eta^2+(k-1)^2\eta^2<k^2\eta^2$; hence
$$\boxed{\eta<1/k\ \Longrightarrow\ Z_\eta(P^\perp)\le k-2 .}$$
**Ledger note:** the admissible $\eta$ is forced to be $\lesssim1/k$, so the "$\eta$-dependence"
of $C_{d,k,\varepsilon,\eta}$ is a $k$-dependence in disguise. (For general slopes bounded by
$K$ one gets $\eta\lesssim1/(Kk^{3/2})$.)

### C.2 Thm 1.15 ⟸ Thm 5.4 + Prop 3.2 + Lemma 6.1 — CLOSES, with one typo
Step by step through §6.2 for our instance:

1. **Reduction to restricted-digit sets.** *Not needed.* The paper first embeds a general
   $T_p$-invariant set into a restricted-digit set of dimension $<s+\varepsilon$ "*after replacing
   $p_j$ by suitable powers*", with an exponent $j=j(\varepsilon)$. Our $C_j$ **is already**
   $A_j(p_j,D_j)$. This removes one ineffective step ($j(\varepsilon)$ is not quantified in the
   cited argument) and is a genuine simplification for us. ✓
2. **Ahlfors regularity.** OSC holds with open set $(0,1)$ ✓. Explicitly, for
   $p_j^{-(n+1)}<r\le p_j^{-n}$: a ball $B(x,r)$ meets at most $3$ level-$n$ cylinders, whence
   $\mu^{(j)}(B(x,r))\le3|D_j|^{-n}<3|D_j|\,r^{s_j}$; and for $x\in C_j$ the level-$(n+2)$
   cylinder of $x$ lies in $B(x,r)$, whence $\mu^{(j)}(B(x,r))\ge|D_j|^{-(n+2)}\ge|D_j|^{-2}r^{s_j}$.
   So
   $$|D_j|^{-2}r^{s_j}\ \le\ \mu^{(j)}(B(x,r))\ \le\ 3|D_j|\,r^{s_j},\qquad 0<r\le1 .$$
   Passing to $\mu_0=\prod_j\mu^{(j)}$ on $\mathbb R^k$ via
   $\prod_j[y_j\pm r/\sqrt k]\subset B(y,r)\subset\prod_j[y_j\pm r]$:
   $$C_1r^s\le\mu_0(B(y,r))\le C_2'r^s,\qquad
   C_1=k^{-s/2}\prod_j|D_j|^{-2},\quad C_2'=3^k\prod_j|D_j| .$$
   This makes the paper's "*the implicit constants depend on the $p_j$'s*" explicit. ✓
3. **$D_{\mathcal X}(q)=s$.** With $\Delta_j$ uniform on $|D_j|$ points,
   $\|\Delta_j\|_q^q=|D_j|^{1-q}$, so
   $\log\|\Delta_j\|_q^q/((q-1)\log\lambda_j)=\log|D_j|/\log p_j=s_j$ ✓. Integrating the model of
   Lemma 5.1 (using $\mathbb P(j\in J(x))=a_d/a_j$ and $\log\lambda=-a_d$) gives
   $\int\log\|\Delta\|_q^q\,d\mathbb P/((q-1)\log\lambda)=\sum_js_j=s$ — I verified this
   computation independently; it is the identity the paper asserts at (5.1)ff. ✓
4. **Theorem 5.4 gives $D_{\pi\mathcal X}(q)=\min\{k-1,s\}$** for all $\pi$ in the compact set
   $\mathbb G'_\eta(k,k-1)=\{Z_\eta(\pi)\le k-2\}$, since $Z(\pi)\le Z_\eta(\pi)$. ✓ (subject to
   C.3 below).
5. **Choice of $q$.** From $\sum_Q\mu(Q)^q\le2^{-m(q-1)(\min\{k',s\}-\varepsilon/3)}$ one gets
   $\max_Q\mu(Q)\le2^{-m(1-1/q)(\min\{k',s\}-\varepsilon/3)}$, and this is
   $\le2^{-m(\min\{k',s\}-2\varepsilon/3)}$ iff
   $\tfrac1q(\min\{k',s\}-\tfrac\varepsilon3)\le\tfrac\varepsilon3$, for which
   $$q\ \ge\ 3k/\varepsilon$$
   suffices. **The paper writes "$1/q'<\varepsilon/(3d)$"; with $q'$ the Hölder conjugate this
   says $q\lesssim1+\varepsilon/(3d)$, the wrong direction. It is a typo for $1/q$.** Harmless,
   but note the consequence: **$q$ must be taken $\gtrsim3k/\varepsilon$, and every constant in
   the engine depends on $q$.**
6. **Uniformity over $\pi$.** Proposition 3.2 gives, for each $\pi$, a *neighbourhood* $U$ on
   which $\liminf_m-\frac1m\log\|(\pi'\mu_x)^{(m)}\|_q^q\ge T_{\pi\mathcal X}(q)-\varepsilon$
   uniformly in $x$ and $\pi'\in U$ — note the right side is evaluated at the *centre* $\pi$.
   Covering the compact $\mathbb G'_\eta$ by finitely many such $U_i$ centred at
   $\pi_i\in\mathbb G'_\eta$, and using step 4 at each $\pi_i$, yields the uniform bound. The
   logic closes ✓, but **this is a covering-by-compactness step and contributes no rate.**
7. **From $m(n)$ to all $m$.** $m(n)=\lceil n\log\lambda^{-1}\rceil$ with
   $\lambda=\lambda_d=\max_j\lambda_j=1/p_1$ (smallest prime), so the gaps of $m(n)$ are
   $\le\lceil\log_2p_1\rceil$. Absorbing the resulting factor $2^{\,\text{gap}\cdot\min\{k',s\}}$
   into $2^{m\varepsilon/3}$ requires
   $$m\ \ge\ 3k\lceil\log_2 p_1\rceil/\varepsilon .$$
   **This is an explicit, unavoidable $p$-dependence of the threshold**, and it is the *only*
   explicit one I found. ✓
8. **Lemma 6.1** with $L=1$, $t=\min\{k-1,s\}-\varepsilon$, $C=C_2/C_1$ gives
   $|\cdot|_{2^{-m}}=O_{k,1,C}(1)2^{m(s-t)}=O(1)2^{m(\max\{s-(k-1),0\}+\varepsilon)}$ ✓. The
   $O_{k,L}(1)$ is the number of $\mathcal D_m$-cubes meeting a ball of radius $(L+1)2^{-m}$ in
   $\mathbb R^{k-1}$, i.e. $\le6^{k-1}$. ✓

### C.3 Theorem 5.4 — TWO DEFECTS

**(a) Hypothesis (P1) is misprinted, and as printed it fails for us.**
§5 requires "*$\lambda_i/\lambda_j$ is irrational*". For $\lambda_j=1/p_j$ we have
$\lambda_i/\lambda_j=p_j/p_i\in\mathbb Q$ — **the hypothesis as printed is violated by the very
measures Theorem 1.15 applies it to.** The intended hypothesis is
$\log\lambda_i/\log\lambda_j\notin\mathbb Q$ (multiplicative independence). Evidence, all
internal to the paper:
   * Remark 1.16 states the condition for self-similar sets as
     "$\log\lambda_i/\log\lambda_j\notin\mathbb Q$" (transcribed above).
   * Theorem 1.15 hypothesises "*pairwise multiplicatively independent integers*" $p_j$ and its
     proof applies Lemma 5.1 with $\lambda_j=p_j^{-1}$; under the literal (P1) the proof would
     contradict its own hypothesis.
   * Lemma 5.1's translation vector is $(a_d/a_1,\dots,a_d/a_{d-1})$ with $a_j=|\log\lambda_j|$;
     the orbit closure $X$ is a positive-dimensional subtorus — which Lemma 5.2's proof requires
     ("*By the irrationality assumption (P1), the phase space $X$ … is a sub-torus*") — precisely
     when the $a_d/a_j=\log\lambda_d/\log\lambda_j$ are irrational.
   * The remark preceding (P1) says $\lambda_i/\lambda_j\in\mathbb Q$ is "*upon suitable
     iterations of the corresponding models, equivalent to*" $\lambda_i=\lambda_j$ — true for
     $\log\lambda_i/\log\lambda_j\in\mathbb Q$, false for $\lambda_i/\lambda_j\in\mathbb Q$.

   **Verdict: typographical, not mathematical. Under the corrected reading our $\lambda_j=1/p_j$
   satisfy (P1)** ($\log p_i/\log p_j\notin\mathbb Q$ for distinct primes). *Do not consume the
   printed form.*

**(P2)** holds for us **with an explicit constant and no exceptional set**: the level-$n$ atoms of
$\mu^{(j)}$ are $\sum_{i\le n}a_ip_j^{-i}$, $a_i\in D_j$, which are distinct and
$p_j^{-n}=\lambda_j^{\,n}$-separated. So exponential separation holds with $R=1$ for *every*
$n$ — the strongest possible form. ✓ No ineffectivity enters here.

**(b) The final step of the proof of Theorem 5.4 omits an a.e.-injectivity check — GAP in
exposition, closable for our $\pi$.**
The induction ends: "*We have verified that $\pi\mathcal X$ satisfies the assumptions of Theorem
1.9. Therefore, $D_{\pi\mathcal X}(q)=\min\{k,s(d)\}$*". Theorem 1.9 delivers
$D_{\pi\mathcal X}(q)=\int\log\|\pi\Delta(y)\|_q^q\,d\mathbb P/((q-1)\log\lambda)$. Merging atoms
*increases* $\|\cdot\|_q$ for $q>1$, so $\|\pi\Delta\|_q\ge\|\Delta\|_q$, and since
$\log\lambda<0$ the formula value for $\pi\mathcal X$ is $\le$ that for $\mathcal X$, **with
equality iff $\pi$ is injective on $\mathrm{supp}\,\Delta(y)$ (with multiplicity) for
$\mathbb P$-a.e. $y$.** The paper does not verify this, and it explicitly warns two paragraphs
earlier of "*the presence here of exact overlaps, resulting from the non-injectivity of every
coordinate projection $\pi$ restricted to the support $\Delta(x)$*". So the step is not
self-contained as written.

*Verification for our $\pi$* (the hyperplane orthogonal to the diagonal), which is all we need.
$\ker\pi=\mathrm{span}\{(1,\dots,1)\}$. By Lemma 5.1,
$\mathrm{supp}\,\Delta(x)\subset\prod_{j\in J(x)}\big(p_j^{x_j}\mathrm{supp}\,\Delta_j\big)\times
\prod_{j\notin J(x),j<d}\{0\}\times\mathrm{supp}\,\Delta_d$, so every difference of two points of
$\mathrm{supp}\,\Delta(x)$ has $j$-th coordinate $0$ for $j\notin J(x)\cup\{d\}$.
 * If $J(x)\ne\{1,\dots,d-1\}$, no nonzero multiple of $(1,\dots,1)$ is such a difference (all its
   coordinates are nonzero) — injective, for *every* such $x$.
 * If $J(x)=\{1,\dots,d-1\}$, non-injectivity forces a common value
   $c=p_j^{x_j}(a_j-b_j)/p_j$ for all $j<d$ and $c=(a_d-b_d)/p_d$, with
   $a_j,b_j\in D_j$. For each of the finitely many integer tuples $(a_j,b_j)_j$ this pins
   $x_j$ to a single value, a $\mathbb P$-null condition (the translation on $X$ is by an
   irrational vector, so $X$ surjects onto each coordinate circle).
   
   Hence $\pi$ is $\mathbb P$-a.e. injective on $\mathrm{supp}\,\Delta(x)$, the formula value for
   $\pi\mathcal X$ equals $s$, and the step closes. ∎

*Also noted (minor):* the base case $k=1$ writes
"$D_{\pi\mathcal X}(q)=\sum_{j\le d-\ell}\dim(\mu^{(j)},q)$", but Theorem 1.9 requires
$q$-unsaturation, which for a $1$-dimensional model means $D<1$; the correct reading is the
contradiction argument the authors flag after Theorem 1.9 ("*simply by arguing by
contradiction*"), which yields $D_{\pi\mathcal X}(q)\ge\min\{1,\sum_{j\le d-\ell}\dim(\mu^{(j)},q)\}$
— exactly what (5.6) asserts. Repaired by the $\min$ on the left of (5.6). ✓

### C.4 The engine — Theorem 1.9 / Theorem 3.7 / Theorem 2.1
No mathematical defect found in the chain for our instance. The relevant structural facts for
task (2) are: Theorem 1.9's convergence is a bare limit "*uniformly in $x\in X$*" with **no
rate**; Theorem 3.7's $\eta,m_0$ "*depend on $\mathcal X$, $q$ and $\sigma$*"; and
Theorem 2.1's $\varepsilon=\varepsilon(q,\delta,L)$ is imported from [19] without an explicit
value.

---

## D. Task 2 — the constant ledger

Write $\alpha=\max\{s-(k-1),0\}\in[0,1]$, $N$ the ambient parameter of our application,
$k\le K(N)\sim\log\log N$, $p_j\in[B_0,(\log N)^C]$.

### D.0 Quantifier order — do not misread Corollary 1.17
Corollary 1.17 writes its constant as $C_{\varepsilon,K}$ and Theorem 1.15 writes
$C_{d,k,\varepsilon,\eta}$. **These subscripts are not a uniformity claim.** In both statements
the primes $p_1,\dots,p_d$ and the sets $A_1,\dots,A_d$ are fixed by the opening sentence
("*Let $p_1,\dots,p_d\ldots$ Let $A_1,\dots,A_d\ldots$*"), and only afterwards does the text say
"*Fix $\varepsilon>0$ and $\eta>0$; then there is $C_{d,k,\varepsilon,\eta}>0$*". The constant
therefore depends on the $p_j$ and $A_j$ as well; the subscripts merely record the dependencies
the authors chose to display. This reading is confirmed inside the proof, which states
plainly: "*Here the implicit constants depend on the $p_j$'s, but not on $y,r$.*"
Reading $C_{\varepsilon,K}$ as prime-independent would be the single most costly error an
assembly could make with this corollary.

### D.0′ When the bound is non-trivial
$s-(k-1)=1-\sum_j(1-s_j)$ with $1-s_j=\log\frac{2p_j}{p_j+1}/\log p_j\sim\log2/\log p_j$. So the
conclusion is a genuine (sub-trivial) bound precisely when $\sum_j\log2/\log p_j\lesssim1$, and it
collapses to the trivial $\delta^{-1-\varepsilon}$ once $k$ primes of size $\approx B_0$ satisfy
$k\log2/\log B_0\ge1$, i.e. $k\gtrsim\log B_0/\log2$. **The regime $k\le\log B_0$ named in our
application sits exactly at this threshold** — worth checking against the intended constants
before relying on the bound.

### D.1 Explicit factors (all safe)

| Factor | Origin | Value | Growth at our scale |
|---|---|---|---|
| $\prod_j|D_j|^{2}$ | $1/C_1$, Ahlfors lower bound (C.2 step 2) | $\prod_j\big(\tfrac{p_j+1}2\big)^{2}$ | $\le\exp\!\big(2Ck\log\log N\big)=\exp(O((\log\log N)^2))$ ✓ |
| $k^{s/2}$ | ball-vs-cube in $\mathbb R^k$ | $\le k^{k/2}$ | $\exp(O(\log\log N\cdot\log\log\log N))$ ✓ |
| $6^{k-1}$ | $O_{k,L}(1)$ in Lemma 6.1 | $6^{k-1}$ | $\exp(O(\log\log N))$ ✓ |
| $3^k\prod_j|D_j|$ | $C_2'$, Ahlfors upper bound | — | as row 1 ✓ |
| $q\ge3k/\varepsilon$ | C.2 step 5 | $3k/\varepsilon$ | $O(\log\log N/\varepsilon)$ — **enters the engine's constants** ⚠ |
| $\eta<1/k$ | C.1 | $1/k$ | **enters $C_{d,k,\varepsilon,\eta}$** ⚠ |
| $m\ge3k\lceil\log_2p_1\rceil/\varepsilon$ | C.2 step 7 ($m(n)$ gaps) | explicit | $O(\log\log N\log\log\log N/\varepsilon)$ ✓ |
| $\lceil\log_2 p_1\rceil$ | $\lambda=1/p_1$ | — | ✓ |

**Everything in this table is $\exp(O((\log\log N)^2))$, hence $\ll N^\varepsilon$.** If the
threshold were explicit, the uniformity we need would hold comfortably.

### D.2 The blocker

The conclusion must hold "*for all $0<\delta\le1$*", but the argument produces it only for
$\delta\le2^{-m_0}$; the constant absorbs the trivial bound on the complementary range:
$$C\ \gtrsim\ \max_{2^{-m_0}<\delta\le1}\delta^{\,\alpha+\varepsilon}\delta^{-1}
\ =\ 2^{\,m_0(1-\alpha-\varepsilon)} .$$
**$C$ is exponential in the threshold scale $m_0$.** And $m_0$ is ineffective. Its ineffectivity
has four independent sources, all of which must be removed for our application:

1. **Inverse theorem** (Theorem 2.1 ⟸ [19, Thm 1.2]): $\varepsilon=\varepsilon(q,\delta,L)>0$ is
   asserted to exist, not computed. This is the deepest obstruction; effective inverse theorems
   for $L^q$-norms of convolutions are not available. **Ineffective.**
2. **Unique ergodicity, no rate** (proof of Prop 3.2):
   "*By the unique ergodicity of $(X,\mathbf T,\mathbb P)$,
   $\lim_{n}A(\tilde\Psi_N^\pi,x,n)=\int\tilde\Psi_N^\pi\,d\mathbb P$ uniformly in $x\in X$*."
   The rate of uniform convergence of Birkhoff averages for the translation by
   $(\log p_1/\log p_j)_j$ on $X$ is governed by the **Diophantine type of ratios of logarithms of
   primes**. This is the one source that is *in principle* effectivisable: Baker's theorem on
   linear forms in logarithms gives $|n_1\log p_1+\cdots+n_k\log p_k|\ge
   \exp(-\mathcal C(k)(\log\max_jp_j)^{k}\log H)$ for integer vectors of height $\le H$, which
   would yield an effective (very weak) equidistribution rate. **Ineffective as written;
   effectivisable in principle, at Baker strength.**
3. **Compactness** (twice): the construction of $\tilde\Psi_n$ "*by a well known compactness
   argument*"; and the finite subcover of $\mathbb G'_\eta(d,k)$ in §6.2 and of
   $\mathbb G(d,d-1)$ in Corollary 3.3. **Ineffective**; the second is a modulus-of-continuity
   question on the Grassmannian and is probably the least serious.
4. **The unsaturation gap $\eta=\eta(\mathcal X,q)$** (Corollary 3.3), obtained from a *strict*
   inequality by compactness, and feeding $m_0$ through
   $\delta=\delta(\eta)$, $L=L(L_0,\delta)$, $\varepsilon=\varepsilon(\delta,L)$,
   $S_0=S_0(\dots)$ (§3.3.5). **Ineffective**, but see the correction below for how large it
   actually is.

   *Correction (entered after the pass; supersedes the earlier reading of this item).* An
   earlier version of this ledger claimed the gap degenerates as
   $1-s_j=\log\frac{2p_j}{p_j+1}/\log p_j\sim\log2/\log p_j\to0$, and flagged that as the danger
   point most specific to our application. **That computation is correct but mis-located.** It is
   the unsaturation gap of the *full* model $\mathcal X$ on $\mathbb R^d$ tested against
   coordinate hyperplanes — and Theorem 1.9, hence Corollary 3.3, is never applied to
   $\mathcal X$. It is applied to the *projected* models $\pi\mathcal X$ (proof of Theorem 5.4),
   whose unsaturation is supplied by the induction (5.6) and, in the base case $k=1$, by the
   contradiction argument for a $1$-dimensional model, where "$q$-unsaturated on lines" means
   simply $D_{\pi\mathcal X}(q)<1$. There the operative $\eta$ is the *assumed deficit* in the
   counter-assumption — i.e. the target accuracy $\varepsilon_0$ — not a function of the $p_j$.
   I found no point in the chain at which $1-s_j$ enters as $\eta$. **So this item is plausibly
   void, and certainly is not the $p$-degeneration I claimed.** It should be confirmed, not
   inherited: see auditor item 3. The genuine $p$-dependence of $m_0$ runs through source 2
   (equidistribution rate), not through the unsaturation gap.

### D.3 The suppressed $d$-dependence
§2.2: "*all implicit constants are allowed to depend on the ambient dimension $d$*", and §3.3.5
lists $d$ among the "given data" on which all parameters may depend without mention. Our
$d=k\sim\log\log N$ **grows**. So even setting aside $m_0$, the paper's constants are not
declared uniform in $d$, and the $d$-dependence is not tracked anywhere in §§2–3. Any attempt to
use Corollary 1.17 with $k\to\infty$ must re-audit §§2–3 for $d$-uniformity from scratch. In
particular $C_d$ in Theorem 2.1(2.1) and the $\Theta_d(1)$ in $N_m(X)=\Theta_d(1)|X|_{2^{-m}}$
are undetermined.

### D.4 Verdict for (B-i)
$$\sup_{\substack{k\le K(N)\\ p_j\in[B_0,(\log N)^C]}}C_{k,\varepsilon,\eta}\ \ \text{is NOT
shown to be}\ \ N^{o(1)}\ \text{by this paper, and cannot be so shown without new input.}$$
The explicit part is $\exp(O((\log\log N)^2))$ ✓; the ineffective part is unbounded as far as the
paper is concerned. **GAP, located at: Theorem 2.1's $\varepsilon(q,\delta,L)$ (via [19]);
Proposition 3.2's unique-ergodicity limit; Corollary 3.3's $\eta$; and the global $d$-convention
of §2.2.**

---

## E. Task 3 — the truncation bridge (B-ii)

### E.1 What the assembly needs, and why Theorem 1.15 as stated is not enough
Our assembly produces points satisfying **finitely many** digit conditions: for each $j$, the
first $J_j$ base-$p_j$ digits lie in $D_j$. Write
$$C_j^{(J)}:=\bigcup_{w\in D_j^{J}}\big[0.w,\ 0.w+p_j^{-J}\big]\ \supset\ C_j$$
(the depth-$J$ tree truncation; a union of $|D_j|^{J}$ closed intervals of length $p_j^{-J}$).
The assembly needs a bound on $N_\delta\big(\bigcap_jC_j^{(J_j)}\big)$, **not** on
$N_\delta\big(\bigcap_jC_j\big)$. These differ: the truncations are strictly larger and
$\bigcap_jC_j^{(J_j)}$ need not lie in any small neighbourhood of $\bigcap_jC_j$ — intersections
of neighbourhoods are not neighbourhoods of intersections. So the *exact-fibre* conclusion of
Theorem 1.15 (a statement about $(\prod A_j)\cap P$, $P$ an honest affine subspace) does **not**
transfer.

**The fix: consume Lemma 6.1's first assertion, not Theorem 1.15's conclusion.** Lemma 6.1 bounds
$|\pi^{-1}(B)|_{2^{-m}}$ for $B$ a *ball* of radius $2^{-m}$ — i.e. it already controls the
$\delta$-thickened slice. This is the robust form, and it is exactly what the proof of Theorem
1.15 establishes en route.

### E.2 The bridge lemma

> **Lemma T (truncation bridge).** Let $p_1,\dots,p_k$ be distinct odd primes, $C_j$, $D_j$, $s$
> as above, and let $\varepsilon>0$. Let $C^\star=C^\star(k,\varepsilon,p_1,\dots,p_k)$ be the
> constant furnished by the proof of Theorem 1.15 (i.e. $C^\star=6^{k-1}C_2/C_1$ in the notation
> of Lemma 6.1, with $C_1=k^{-s/2}\prod_j|D_j|^{-2}$), valid for all $\delta\le2^{-m_0}$. Then for
> all integers $J_1,\dots,J_k\ge1$ and all $\delta$ with
> $$\max_j p_j^{-J_j}\ \le\ \delta\ \le\ 2^{-m_0},$$
> we have
> $$N_\delta\Big(\bigcap_{j=1}^kC_j^{(J_j)}\Big)\ \le\ 7\,(3\sqrt k)^{\,k-1}\,C^\star\;
> \delta^{-\max\{s-(k-1),\,0\}-\varepsilon}.$$
> In particular, with a single depth $J$ and $J_j=\lceil J\log p/\log p_j\rceil$,
> $\delta=p^{-J}$, the hypothesis $\max_jp_j^{-J_j}\le\delta$ holds and the conclusion applies at
> $\delta=p^{-J(1+o(1))}$.

**Proof.**

*Step 1 (truncation is a $\delta$-neighbourhood).* Let $x\in C_j^{(J_j)}$, so $x$ lies in
$[0.w,0.w+p_j^{-J_j}]$ for some $w\in D_j^{J_j}$. Put $y:=0.w\,000\cdots$ (base $p_j$). Since
$0\in D_j$, all digits of $y$ lie in $D_j$, so $y\in C_j$; and $|x-y|\le p_j^{-J_j}\le\delta$.
Hence
$$C_j^{(J_j)}\subset\{x:\operatorname{dist}(x,C_j)\le\delta\}. \tag{T1}$$
(This is the only place the hypothesis $\max_jp_j^{-J_j}\le\delta$ is used, and the only place
$0\in D_j$ is used — both hold for the lower-half-digit sets.)

*Step 2 (lift to the product).* Let $x\in\bigcap_jC_j^{(J_j)}$. By (T1) choose $y_j(x)\in C_j$
with $|x-y_j(x)|\le\delta$, and set $\Phi(x):=(y_1(x),\dots,y_k(x))\in\prod_jC_j$. Let
$\pi\in\mathbb G(k,k-1)$ be the orthogonal projection onto $\{v:\sum_jv_j=0\}$, i.e. the
orthogonal complement of the diagonal. Since $\Phi(x)$ lies within $\delta\sqrt k$ of the
diagonal point $(x,\dots,x)$, and $\pi$ kills the diagonal and is $1$-Lipschitz,
$$|\pi(\Phi(x))|\le\delta\sqrt k,\qquad\text{i.e.}\qquad
\Phi(x)\in\pi^{-1}\big(B(0,\delta\sqrt k)\big)\cap\textstyle\prod_jC_j. \tag{T2}$$

*Step 3 (separation is preserved).* If $|x-x'|\ge3\delta$ then
$|y_1(x)-y_1(x')|\ge|x-x'|-2\delta\ge\delta$, so $|\Phi(x)-\Phi(x')|\ge\delta$. Hence $\Phi$ maps
a $3\delta$-separated subset of $\bigcap_jC_j^{(J_j)}$ to a $\delta$-separated subset of the set
in (T2):
$$\big|\textstyle\bigcap_jC_j^{(J_j)}\big|_{3\delta}\ \le\
\big|\pi^{-1}(B(0,\delta\sqrt k))\cap\textstyle\prod_jC_j\big|_{\delta}. \tag{T3}$$

*Step 4 (apply Lemma 6.1).* Cover $B(0,\delta\sqrt k)\subset\mathbb R^{k-1}$ by at most
$(2\sqrt k+1)^{k-1}\le(3\sqrt k)^{k-1}$ balls of radius $\delta$. Lemma 6.1 — applied with
$X=\mathrm{supp}\,\mu_0=\prod_jC_j$, $\mu=\mu_0$, $L=1$, $s$ as above,
$t=\min\{k-1,s\}-\varepsilon$, and $C_1,C_2$ as in §C.2 — bounds $|\pi^{-1}(B)|_\delta$ for each
such ball by $C^\star\delta^{-(s-t)}=C^\star\delta^{-\max\{s-(k-1),0\}-\varepsilon}$. Summing,
$$\big|\textstyle\bigcap_jC_j^{(J_j)}\big|_{3\delta}\le(3\sqrt k)^{k-1}C^\star
\delta^{-\max\{s-(k-1),0\}-\varepsilon}.$$

*Step 5 (packing at $3\delta$ to covering at $\delta$).* For subsets of $\mathbb R$,
$N_\delta(S)\le7\,|S|_{3\delta}$ (each $3\delta$-ball of a maximal $3\delta$-separated net is
covered by $7$ intervals of length $\delta$). Combining gives the claim. $\blacksquare$

### E.3 Remarks on Lemma T
* **It is the correct consuming form.** The output is a bound on the *finite-depth* object, at
  the scale where the depth-$J$ tree resolves, which is what an assembly over $\delta$-cells
  needs. Nothing in the proof requires the truncation depths to be equal or comparable beyond
  $p_j^{-J_j}\le\delta$.
* **The $k$-dependent losses are benign**: $(3\sqrt k)^{k-1}=\exp(O(k\log k))$ and the factor $7$.
  At $k\sim\log\log N$ this is $\exp(O(\log\log N\log\log\log N))\ll N^\varepsilon$ ✓.
* **The restriction $\delta\le2^{-m_0}$ is inherited from D.2 and is the same blocker.** Lemma T
  does not create it and does not remove it.
* $0\in D_j$ is essential to Step 1. For a digit set not containing $0$ one would replace $y$ by
  the constant continuation of the smallest digit; the constant in (T1) changes by a bounded
  factor. Not needed here.

---

## F. Auditor priority list

1. **The (P1) misprint (C.3a).** Highest priority because it is the one place where consuming the
   paper *literally* gives a false application. Confirm from Remark 1.16 and the proof of Lemma
   5.1 that the intended hypothesis is $\log\lambda_i/\log\lambda_j\notin\mathbb Q$. If a later
   version of the paper says otherwise, everything downstream must be re-examined.
2. **The a.e.-injectivity gap in the proof of Theorem 5.4 (C.3b).** Check the norm-monotonicity
   claim ($\|\pi\Delta\|_q\ge\|\Delta\|_q$ with equality iff injective, $q>1$) and then my
   verification for $\ker\pi=\mathrm{span}(1,\dots,1)$. If the general-$\pi$ case matters to
   anyone else, it is genuinely open as written.
3. **Which model Corollary 3.3's $\eta$ actually belongs to (D.2 item 4 + its correction).**
   Confirm that $\eta$ is the projected model's gap — hence the target deficit $\varepsilon_0$ —
   and not the full model's $1-s_j$. If that is right, the $p$-degeneration I originally
   asserted does not exist and the whole $p$-dependence of $m_0$ sits in the equidistribution
   rate (source 2). If it is wrong, the application is in much worse shape than §D suggests.
   Either way, check whether the $\eta$-dependence in §3.3.5's chain
   ($\delta=\delta(\eta)$, $L=L(L_0,\delta)$, $\varepsilon=\varepsilon(\delta,L)$) is polynomial
   or worse.
4. **$d$-uniformity of §§2–3 (D.3).** The paper's blanket convention makes every constant in the
   engine potentially $d$-dependent in an untracked way. Since our $d=k\to\infty$, someone must
   decide whether $C_d$ in (2.1) and the constants in Theorem 3.7 are polynomial in $d$.
5. **The typo $1/q'\to1/q$ (C.2 step 5)** and the consequence $q\gtrsim3k/\varepsilon$. Trivial
   to confirm; matters only because $q$ then grows with $k$ and feeds the engine's constants.
6. **Lemma T, Steps 1 and 3.** Both are elementary; Step 1's use of $0\in D_j$ and Step 3's
   $3\delta\to\delta$ bookkeeping are the only places to slip.
7. **The quantifier order in Corollary 1.17 (D.0)** and the non-triviality threshold
   $k\gtrsim\log B_0/\log2$ (D.0′). Both are cheap to check and both bear directly on whether
   the corollary says anything in our parameter range.

---

## G. Papers noted in passing (not a survey)
* The $k$-fold statement is **also** effectively present in the 1-D predecessor: P. Shmerkin,
  *On Furstenberg's intersection conjecture, self-similar measures, and the $L^q$ norms of
  convolutions*, Ann. of Math. **189** (2019), 319–391 — **§7.2 is titled "Convolutions of
  several self-similar measures"**, and Corso–Shmerkin's Lemma 5.1 explicitly says its argument
  "*runs along similar lines to the appearing in the proof of [18, Theorem 7.5], which concerns
  one-dimensional linear images of such products*". **[18, Theorem 7.5] is the natural
  alternative source for the $d=k$, $g_j$ affine case and should be read** — it may give the
  target theorem with a shorter chain (no $\mathbb R^d$ machinery), which could shorten the
  constant audit considerably. I did not read it at source in this pass.
* P. Shmerkin, *Inverse theorems for discretized sums and $L^q$ norms of convolutions in
  $\mathbb R^d$*, preprint — cited as [19]; **this is where the ineffective
  $\varepsilon(q,\delta,L)$ lives.** Any effectivity programme starts here.
* T. Austin, *A new dynamical proof of the Shmerkin–Wu theorem*, J. Mod. Dyn. **18** (2022) —
  cited as [2]; a soft proof, unlikely to give constants.
* H. Yu, cited as [22, Corollary 9.1]; Theorem 1.15 with $k=d-1$ is stated to be "*a substantive
  generalization*" of it.
* Hochman–Shmerkin, *Local entropy averages and projections of fractal measures*, Ann. of Math.
  (cited [13]) — the entropy analogue, relevant only if one retreats from $L^q$ to Hausdorff
  dimension (which would lose the covering-number form we need).
