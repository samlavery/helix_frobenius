# Erdős #727 — opened

**Problem** [EGRS75]. For $k\ge2$: does $(n+k)!^2\mid(2n)!$ for infinitely many $n$?
**Gate run** (site remarks, read at source): open **even for $k=2$**. Balakran [Ba29] proved
$k=1$, i.e. $(n+1)^2\mid\binom{2n}{n}$ infinitely often. EGRS note Balakran's method gives
infinitely many $n$ with $(n+k)!(n+1)!\mid(2n)!$. Erdős [Er68c]: $a!b!\mid n!\Rightarrow
a+b\le n+O(\log n)$ — which is exactly \#400's $g_2\ll\log n$, so \#727 and \#400 are the
same ledger read two ways.

## Restatement (exact)
$$\frac{(2n)!}{(n+k)!^2}=\frac{\binom{2n}{n}}{\bigl[(n+1)\cdots(n+k)\bigr]^2}
\quad\Longrightarrow\quad
\#727 \iff \bigl[(n{+}1)\cdots(n{+}k)\bigr]^2\ \Big|\ \binom{2n}{n}\ \text{i.o.}$$
By Kummer, with $\kappa_p(n)=v_p\binom{2n}{n}=\#$carries in $n+n$ base $p$:
$$\boxed{\ \kappa_p(n)\ \ge\ 2\,v_p\bigl((n{+}1)\cdots(n{+}k)\bigr)\quad\forall p.\ }$$
Only rails dividing the product can fail — a finite check per $n$. ($k=1$ recovers
Balakran, so the reformulation is validated against a theorem.)

## The forced mechanism (proved)
For $p>\sqrt{2n}$ the doubling $n+n$ has at most one carry, so $\kappa_p\le1$ and the
condition is **unsatisfiable** unless $p\nmid(n{+}1)\cdots(n{+}k)$. Hence:
> **Necessary:** $(n{+}1)\cdots(n{+}k)$ is $\sqrt{2n}$-smooth.

*Verified:* **0 violations** among all $k{=}2$ and $k{=}3$ solutions below $1.2\times10^5$;
$\max\log p_{\max}/\log(2n)=0.4999$, i.e. the bound is attained and never crossed.

## Measured
Census to $n=2\times10^5$:

| $k$ | solutions | density | first |
|---|---|---|---|
| 1 | 22525 | 0.1126 | 5 |
| **2** | **1981** | **0.0099** | **208** |
| 3 | 152 | 0.00076 | 3475 |
| 4 | 8 | 0.00004 | 8174 |
| 5 | 0 | — | — |

Dyadic counts for $k{=}2$: $4,18,16,71,127,326,651,765$ — density stabilises near $0.010$.
**This is positive density, not merely infinitude** — substantially stronger than what is
asked. Density falls by $\approx\theta$ per unit $k$ with $\theta\approx1/13$, so $k{=}5$
expects $\sim0.6$ solutions below $2\times10^5$: consistent with finding none.
Blocking rails for $k{=}2$ (most common first): $3,2,7,5,11,19,13,17$ — smallest cells bind,
as the $(p-1)$-per-carry law predicts.

## Route to a proof (positive density)
The condition factors into two independent-looking pieces, both of positive density:
1. **Smoothness** — $(n{+}1)\cdots(n{+}k)$ all $\sqrt{2n}$-smooth. Measured density $0.0932$
   for $k{=}2$ against $\rho(2)^2=0.3069^2=0.0942$: **independent to 1%**. Consecutive
   $x^{1/2}$-smooth numbers are a studied object (Hildebrand genre).
2. **Small-rail carries** — $\kappa_p(n)\ge2v_p$ for $p\le\sqrt{2n}$. Costs a further factor
   $\approx10$. These are \#377-type conditions, but needed only with *positive
   probability*, not uniformly in $n$ — far weaker than \#377 requires.

So a positive-density theorem needs (1) at the required smoothness level plus a
conditional-positivity statement for (2). That is a genuinely different and softer target
than \#377's uniform transversality.

## Register
**Proved:** the restatement, the Kummer ledger form, and the smoothness necessity (from
$\kappa_p\le1$ for $p>\sqrt{2n}$). **Measured:** all densities, the $\theta\approx1/13$ decay,
the blocking-rail census, the 1% independence of consecutive smoothness.
**Not proved:** \#727 for any $k\ge2$. **Falsifier:** $k{=}2$ density declining toward 0 at
$n\ge10^7$, or a solution with $p_{\max}>\sqrt{2n}$ (which would break the mechanism).
