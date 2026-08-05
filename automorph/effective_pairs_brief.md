# Effective pairs: what #377 needs vs. what Baker delivers

Not a referee report. One question: **can the effective pair bound carry the gap zone?**
Answer below is a number, and it forces a decision.

---

## 1. What the gap zone demands

The second-moment argument consumes, for each pair $(p,q)$ of primes in the band range and at
working scale $\delta\approx N^{-c}$:
$$\#\{n\le N:\ n\ \text{carry-constrained in base }p\ \text{and base }q\ \text{to depth }J\}
\ \le\ C(p,q,\varepsilon)\cdot N^{\max(0,\,s_p+s_q-1)+\varepsilon}.$$
Summed over $\mathrm{polylog}$-many pairs, this gives all but $N^{1-c/\log\log N}$ clean — provided
$$\boxed{C(p,q,\varepsilon)\le N^{o(1)}\quad\text{for all }p,q\ \text{in the band range.}}$$
Your stated range is $p,q\in[B_0,(\log N)^{C}]$. **That range is the load-bearing assumption, and
it is where this fails.**

Equivalently, and more usefully: the bound is proved only for $\delta\le2^{-m_0}$, so what must
hold is
$$m_0(p,q,\varepsilon)\ \lesssim\ \log N .$$
The whole question is the size of $m_0$.

---

## 2. The $d=2$ trace — three ineffectivity sources, and what Baker does to each

Native setting is Shmerkin (Ann. Math. 189, 2019) **§7.1**, not the $\mathbb R^d$ paper. Lemma 7.1
builds the model: $X=[0,a_2)$ with $a_i=|\log\lambda_i|$, $\mathbf T(x)=x+a_1 \bmod a_2$ — after
normalising, **rotation of the circle by $\alpha=\log\lambda_1/\log\lambda_2=\log p/\log q$**, and
$\mu_x=\eta_1*S_{e^x}\eta_2$. Your structural read is right, and stronger than you put it:

* **Closure needs no transcendence theory.** Density of the orbit needs only
  $n_0\log p+n_1\log q\ne0$ — unique factorization. Baker is needed for the *rate*, not the
  closure. (Contrast $k\ge3$: Shmerkin's own $k$-fold Theorem 7.5 hypothesises
  "*$(1/\log\lambda_j)_{j=1}^k$ is linearly independent over $\mathbb Q$*" — a relation among
  **products** of logs once denominators are cleared, unknown for $\ge3$ primes. That is the
  Schanuel shadow, confirmed in print. Corso–Shmerkin's advance is precisely to work with the
  unknown closure instead. Your instinct to drop to pairs is sound.)

* **Source 1 — the ergodic step is *subadditive*, not Birkhoff.** It is Lemma 4.7 (Furman's
  uniform subadditive ergodic theorem) feeding Corollary 4.8. This has **two** limits inside it,
  and Baker only touches one:
  * the Birkhoff part — iterating subadditivity gives
    $\tfrac1n\varphi_{nN}(x)\le\tfrac1n\sum_{i<n}\varphi_N(\mathbf T^{iN}x)$, a Birkhoff average of
    a **fixed** function over rotation by $N\alpha$. Koksma's inequality bounds the error by
    $\operatorname{Var}(\varphi_N)\cdot D_n(N\alpha)$ — **effectivizable**, given a Diophantine
    bound on $\alpha$. This is where Baker goes.
  * the Fekete part — $\tfrac1N\int\varphi_N\,d\mathbb P\to L$. This is a property of the
    cocycle, not of the dynamics; **Baker says nothing about it.** It is not obviously fatal
    (identifying $L$ is what Theorem 1.11 does), but "substitute Baker for ergodicity" removes
    one of two ineffectivities, not both. Worth knowing before budgeting.

* **Source 2 — compactness: removable, and I can name the fix.** Lemma 4.7's proof builds a
  continuous majorant $\varphi_{n,\varepsilon}\ge\varphi_n$ "*using compactness*". At $d=2$,
  $X$ is a circle and Lemma 7.1 gives $x\mapsto\mu_x$ **a single discontinuity, at $a_1$**. So the
  majorant can be written down by hand — linear interpolation across an interval of length
  $\varepsilon/(2\|\varphi_n\|_\infty)$ around $a_1$. No compactness needed. ✓ Your "likely
  removable once identified" is correct; that is the identification.

* **Source 3 — the inverse theorem: your expectation is confirmed in print.** Shmerkin 2019
  proves its own inverse theorem in **§3** (10 pp.), and says of it, verbatim:
  > "*We emphasize that the proof of Theorem 2.1 (including the proofs of the results it relies
  > on) is elementary, in particular avoiding any use of the Fourier transform or quantitative
  > probabilistic estimates such as the Berry-Esseen Theorem … **The value of $\varepsilon$ is
  > effective in principle, although it is certainly very poor; the worst loss occurs in the
  > application of the asymmetric Balog-Szemerédi-Gowers Theorem** (Theorem 3.2 below).*"

  So: finitary, elementary, effective — and the worst loss is asymmetric BSG, which is
  *polynomial* (Tao's version), not tower. Better than you budgeted. Crucially this source is
  **$p$-independent**: it costs $\varepsilon$-dependence only. **Lowest priority, and not the
  obstruction.**

---

## 3. The number that decides it

$\alpha=\log p/\log q$. Matveev for two logarithms:
$|b_1\log p-b_2\log q|>\exp(-C\log p\log q\,\log B)$ for heights $\le B$. Hence
$$\mu(\alpha)\ \le\ 2+C\log p\log q ,$$
effective — but with the **exponent** proportional to $\log p\log q$. (No elementary substitute:
$p^b\ne q^a$ gives only $\|b\alpha\|\gtrsim p^{-b}$, exponentially weak, useful only for
$b=O(1)$.) Erdős–Turán then puts the threshold for discrepancy $\le\varepsilon$ at
$$n_0\ \approx\ \varepsilon^{-(1+\mu)}\ =\ \exp\!\big(C\log p\log q\,\log(1/\varepsilon)\big),
\qquad m_0\approx n_0\log_2 p .$$
Impose $m_0\lesssim\log N$:
$$C\log p\log q\,\log(1/\varepsilon)\ \lesssim\ \log\log N
\qquad\Longrightarrow\qquad
\boxed{\ \log p\cdot\log q\ \lesssim\ \frac{\log\log N}{\log(1/\varepsilon)}\ }$$
i.e. for $p\approx q$ and $\varepsilon$ fixed,
$$p,q\ \lesssim\ \exp\!\big(c\sqrt{\log\log N}\big).$$

**Compare the demand: $p,q\le(\log N)^{C}=\exp(C\log\log N)$.** The available range is the *square
root* of the exponent. This is not a constant-chasing shortfall; it is a different regime.

*Reality check on the constants.* The $c$ above is $1/\sqrt{C_{\text{Baker}}\log(1/\varepsilon)}$,
and it bites. Taking $C_{\text{Baker}}=1$ and $\varepsilon=0.1$ — both generous —
$\log m_0\approx(\log p)^2\log(1/\varepsilon)$ against $\log\log N$:

| $N$ | $p\le(\log N)^2$ | $p\le\log N$ | $p\le e^{\sqrt{\log\log N}}$ | budget $\log\log N$ |
|---|---|---|---|---|
| $10^{12}$ | 101 | 25 | 7.6 | 3.3 |
| $10^{50}$ | 207 | 52 | 10.9 | 4.8 |
| $10^{1000}$ | 552 | 138 | 17.8 | 7.7 |

Every column fails at these $N$; $\exp(\sqrt{\log\log N})$ only enters the budget asymptotically,
and only after the constant $c$ is taken small. So the honest statement is **stronger than §3's
box**: with Baker's constant as it stands, the usable prime range is
$\exp\big(c\sqrt{\log\log N}\big)$ with a *small* $c$, and at any $N$ one would actually compute
with, it is a handful of primes. Treat the box as an asymptotic ceiling, not a working range.

Using Denjoy–Koksma along continued-fraction denominators removes the Diophantine loss *at* those
denominators, but re-imports it in locating one: the first denominator $\ge X$ is
$\le X^{\mu-1}=X^{C\log p\log q}$, giving the same $\exp(\Theta(\log p\log q))$. I do not see a
route around it with current transcendence technology.

---

## 4. What this means for #377 — the decision

Effective pairs is real, and at $p,q\le\exp(c\sqrt{\log\log N})$ it is genuinely provable and
genuinely new. But **it does not, by itself, cover the band range the gap-zone argument was
written for.** Three ways forward, in the order I'd rank them:

1. **Check whether the second moment can be run with the primes restricted to
   $p\le\exp(c\sqrt{\log\log N})$.** This is the highest-value hour in the campaign right now.
   The pairs carrying "excess tail mass" — do they have to be large? If the $K^2/2$ balanced
   pairs can be taken from the small end of the band, effective pairs closes the gap zone and the
   brief is worth writing. If the argument structurally needs $p$ near $(\log N)^C$, it does not,
   and no amount of effectivization work changes that.
2. **Re-examine what the gap zone needs from equidistribution.** The Birkhoff count in the model
   is $n'(x)=\#\{i\le n:\{x+i\alpha\}\in[0,a_1/a_2)\}$ — literally "how often does a power of $p$
   land in a given multiplicative window between powers of $q$". If the assembly needs only that
   these counts are right *to within a constant factor* rather than to accuracy $\varepsilon$,
   the threshold drops enormously and the prime range opens back up. Worth pinning before
   accepting §3's number as binding.
3. Only then: write the effective-pairs theorem for whatever range survives.

**My recommendation: do not commission the effective-pairs paper yet.** Settle (1) first. The
theorem is publishable, but if it lands at $\exp(c\sqrt{\log\log N})$ and the gap zone needs
$(\log N)^C$, it is a good paper that does not feed #377 — and the campaign's scarce resource is
your attention, not theorems.

---

## 5. What I'd want checked if you disagree

* The exponent $\mu(\alpha)\le2+C\log p\log q$ — that the $\log p\log q$ sits in the *exponent*
  and not in a multiplicative constant. Everything in §3 turns on this.
* Whether $m_0$ really scales like $n_0$ (I assumed the threshold in scales is the ergodic
  threshold times $\log_2 p$). If $m_0$ enters only logarithmically, §3 collapses and the prime
  range is fine.
* Whether the Fekete rate (source 1, second bullet) is genuinely benign.
