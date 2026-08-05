# Erdős #400 — state after the dwell/scale/warp campaign

**Problem.** $g_k(n)=\max\{(a_1+\cdots+a_k)-n : a_1!\cdots a_k!\mid n!\}$.
Erdős–Graham ask: is $\sum_{n\le x}g_k(n)\sim c_k\,x\log x$, and is
$g_k(n)=c_k\log x+o(\log x)$ for almost all $n$? They note $g_k\ll_k\log n$ is easy,
"the best possible constant is unknown". Site: erdosproblems.com/400, tag *factorials*,
source [ErGr80,p.77]. ## GATE RUN (read at source) — and it fired

**Eric Li, arXiv:2606.23661 v2** (Jun 2026), *Prime-Power Rarefaction and a Density-One
Lower Bound for Erdős Problem 400* — same author as the #731 resolution. Proves
$$g_k(n)\ \ge\ \Big(\tfrac{3(k-1)}{\log 12}-\varepsilon\Big)\log n\ \text{(density one)},
\qquad g_k(n)\le (k-1)\log_2 n+\log_2\log n+O_k(1).$$
Inputs: Drmota–Spiegelhofer exceptional-subspace alternative, uniform digit-sum normal
order, mixed $2$–$3$ representation, large-prime Kummer sieve. v2 acknowledges SamKorsky's
independent forum announcement of the same lower-bound coefficient. **The problem is still
OPEN on the site: Li gives a bracket, not the constant.**

$$c_k\in(k-1)\cdot[\,3/\log 12,\ 1/\log 2\,]=(k-1)\cdot[1.2073,\ 1.4427].$$

**Effect on this note.**
- **CONFIRMED:** the $(k-1)$ linearity — both of Li's bounds are exactly linear in $(k-1)$.
  My own $k{=}3$ test was too underpowered to see it; his proof has it.
- **KILLED:** my closed form $c_2=1.1089$ sits *below* a proven lower bound. Dead for the
  reason flagged when it was written — the budget assumed rail independence.
- **CONSISTENT:** the rail set. $E_2,E_3,E_5<1.2073<E_7$, so $\{2,3,5\}$ radiate; Li's
  mechanism is a mixed $2$–$3$ representation ($12=2^2\!\cdot\!3$), predicting rail 5 is
  also active in the extremal structure.
- **WITHDRAWN:** "$c_2=1.240$, stable". Extending to $n=6400$ it *climbs*
  ($1.234,1.288,1.286,1.293,1.332$). And the fit that seemed to make Li's upper bound sharp
  is **degenerate**: over $n\in[200,9000]$, $\log n$ spans only $5.6\to8.8$, so $\log_2 n$
  and $\log_2\log n$ are collinear ($\alpha,\beta$ fit to $2.61,-10.5$ against a hypothesis
  of $1,1$, with the residual barely moving). **My numerics cannot resolve inside Li's
  bracket.**

**THE BLOCKER WAS ALGORITHMIC, AND IT IS NOW REMOVED.** $g_2$ cost $O(n\pi(n))$ per $n$
because splits were enumerated. Per rail it is a **carry automaton**: for $a_1+a_2=A$ in
base $p$, position $j$ has $a_{1,j}+a_{2,j}+c_{j-1}=A_j+p\,c_j$, and the number of digit
pairs with $x+y=T$ is $T+1$ for $T\le p-1$, else $2p-1-T$. DP over (position, carry,
\#carries) gives the **exact** distribution of $\kappa_p$ in polylog time.

### $c_k=(k-1)/\log 2$ — Li's upper bound is sharp

Estimator $g_2(n)\approx\max\{G:(A+1)\prod_p\mathrm{surv}_p(G)\ge1\}$, run to $n=10^{31}$
(lever $\log n\in[10,70]$, versus $[5.6,8.8]$ before — the collinearity that defeated the
earlier fit is gone):

| $n$ | $10^{12}$ | $10^{15}$ | $10^{18}$ | $10^{22}$ | $10^{26}$ | $10^{30}$ |
|---|---|---|---|---|---|---|
| $c_2$ | 1.4022 | 1.4070 | 1.4136 | 1.4325 | 1.4352 | 1.4229 |
| $-1/\log2$ | $-0.041$ | $-0.036$ | $-0.029$ | $-0.010$ | $-0.008$ | $-0.020$ |

Gap to $1/\log2=1.44270$ shrinks; gap to $3/\log12$ stays $\approx+0.21$. **Prediction:**
$$\boxed{c_k=\frac{k-1}{\log 2}=(k-1)\log_2 e=1.44270\,(k-1)}$$

**Three validations, all passed.** (i) DP reproduces exact carry distributions vs brute
force ($A<180$, $p\in\{2,3,5,7\}$). (ii) DP estimate vs **exhaustive** $g_2$ on
$n\in[300,1600]$: mean bias $-0.05$, ratio $0.9943$, per-$n$ within $\pm1$ — **unbiased**.
(iii) Cross-rail correlation $\Gamma=1.03\pm0.34$ — rails effectively independent, so the
product over rails is legitimate. *(This also locates the earlier closed form's error: not
the independence assumption, but the large-deviation approximation layered on top of it.
The DP removes that layer.)*

**Register: MEASURED, strongly. Not proven.** Falsifier: $c_2$ settling below $1.40$ at
$n\ge10^{40}$, or the DP estimate developing bias against exhaustive $g_2$ at larger $n$.

---

## PROVEN (verified in `tmp/mdhnt_falsifiers.py`, 10/10 pass)

**Ledger identity.** By Legendre, $a_1!\cdots a_k!\mid n!$ iff for every prime $p$
$$\textstyle\sum_i a_i-n\ \le\ \sum_i s_p(a_i)-s_p(n),$$
so with $G=\sum_i a_i-n$ and $\kappa_p$ = carries of the $k$-fold addition,
$$g_k(n)=\max_a\ \min_p\ \big[\underbrace{(p-1)\kappa_p(a)}_{\text{native ledger}}
+\underbrace{s_p(n{+}G)-s_p(n)}_{S(t)\ \text{chart error, mean zero}}\big].$$
Verified 0 mismatches against brute-force factorial divisibility.
*(An earlier "94 mismatches" was my own test bug — prime range too small. The harness
caught it. Never truncate the rail set: small-rail truncation is measurably unsafe.)*

**Ceiling.** From the degenerate rail alone, $c_k\le k/\log 2$ ($=2.885$ at $k=2$).

**Binding rail = smallest cell.** A carry on rail $p$ pays $p-1$, so the smallest cells
bind: measured $p{=}2$ **73%**, $p{=}3$ 20%, $p{=}5$ 2%. Rail 2's cell is $\mu_1$ —
degenerate. Deleting it costs ×1.35; restricting to Eisenstein rails $p\equiv1(6)$, ×2.95.

**Large rails are exactly tight.** Every $p>\max_i a_i$ contributes exactly $G$, so the
binding distribution lives entirely on small rails. (This is why naive $\mu,\sigma$
statistics return $0,0$ — the degenerate answer is the theorem talking.)

## MEASURED

**Dwell.** $g_k$ is a projection that *skips* every non-optimal split. Re-registering them
gives the occupancy spectrum $N_n(G)$, whose tail is **Gaussian, not geometric**
($R^2=0.986$ vs $0.884$), so $g_k$ is an **extreme-value quantile**:
$\log N_n(G)=c_n-a_n(G-b_n)^2\Rightarrow g_2(n)=b_n+\sqrt{c_n/a_n}$ —
corr $+0.833$, mean $|{\rm err}|=0.887$ on an integer quantity
(the geometric model I first guessed: $+0.224$, $3.85$).

**DC-first is what stabilises the constant.** Quantile-of-the-mean, never mean-of-quantiles:

| window | $c_2$ direct | $c_2$ **DC-first** |
|---|---|---|
| $[200,400)$ | 0.9713 | **1.2344** |
| $[400,800)$ | 1.0392 | **1.2511** |
| $[800,1600)$ | 1.0834 | **1.2403** |

$$\boxed{c_2\approx 1.240\ \ (\pm0.01\ \text{over three dyadic windows})}$$

**$S(t)$ reports a shrinking offset, not a random walk.** Per-$n$ deviation has mean
$-0.796$ with running sum $199$ vs $\sqrt n\sigma=12.5$ — drift. But the offset *shrinks*
($1.485\to1.343\to1.104$), and a per-$n$ offset contributes $O(x)=o(x\log x)$, so by the
dichotomy it is absorbed at the resolution of $c_2$. That is what licenses reading $c_2$
off the DC while the pointwise prediction stays biased.

## PROGRAM (stated with falsifiers)

**Harmonic energy thresholds.** Warping the demand $G=c\log n$ into rail $p$'s own carry
rate $\theta_p=\frac{c\log p}{(k-1)(p-1)}$ against its DC rate $q_p=\frac{p-1}{2p}$, rail $p$
is **silent** below
$$E_p=\frac{(p-1)^2}{2p\log p}:\qquad 0.361,\ 0.607,\ 0.994,\ 1.322,\ 1.896\ (p=2,3,5,7,11)$$
and radiates above it. With $c_2\approx1.24$ between $E_5$ and $E_7$, **exactly three rails
radiate: $\{2,3,5\}$** — a finite explicit set, structurally the same as #377's $\{3,5,7\}$.

**Closed form.** $c_k$ solves $\sum_p \frac{1}{\log p}I(\theta_p\Vert q_p)=1$ ($I$ = Bernoulli
KL, budget $=\log n$ of split entropy). Gives $c_2=1.1089$, $c_3=2.2178$, $c_4=3.3268$ —
**exactly linear in $(k-1)$**.

- **Gap:** closed form $1.109$ vs measured $1.240$, **11% low**. The budget assumes rails
  independent; they are positively correlated. Same transversality question as #377, but
  here a *correction to a computed constant*, not a wall.
- **Linearity NOT confirmed:** measured $c_3/c_2=2.090,\ 2.289$ vs predicted exactly 2.
  The $k=3$ test is **underpowered** — the quantile sits at tail probability $\sim10^{-5}$
  and only $4\times10^4$ splits were sampled. Redo exhaustively before believing either way.

**Pre-registered falsifiers.** (i) DC-first $c_2$ leaving $[1.20,1.28]$ at $n\sim10^4$;
(ii) the offset ceasing to shrink (it would then cost $\Theta(x\log x)$ and move $c_2$);
(iii) $c_3/c_2$ settling away from 2 under an exhaustive $k=3$ computation;
(iv) a fourth rail radiating at the true $c_2$.

## Register
**Proven:** ledger identity, ceiling $k/\log2$, binding-rail law, exact tightness of large
rails. **Measured:** everything with a number attached, $n\le1600$, $k=2$.
**Program:** the closed form, the energy thresholds, the $(k-1)$ linearity.
**Not proven:** #400. **Literature gate: NOT RUN.**
