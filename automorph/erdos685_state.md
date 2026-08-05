# Erdős #685 — opened, and the measurement disagrees with the conjecture at reachable sizes

**Problem.** Let $\varepsilon>0$ and $n$ large. Is it true that for all
$n^\varepsilon<k\le n^{1-\varepsilon}$,
$$\omega\!\left(\binom nk\right)=(1+o(1))\,k\sum_{k<p<n}\frac1p\ ?$$
Or perhaps even for $k\ge(\log n)^c$?

**Gate** (site, read at source). Trivially $\omega\binom nk>\log\binom nk/\log n$, and this
becomes asymptotic equality if $k>n^{1-o(1)}$. Nothing else recorded.

## Ledger form
$p\mid\binom nk$ iff $k\not\preceq_p n$ (Kummer domination fails), so
$$\omega\!\left(\binom nk\right)=\#\{p\le n:\ k\not\preceq_p n\}.$$
No binomial is evaluated. The conjecture then reads: **the density of rails on which $k$
fails to dominate $n$ is $k/p$ for $p\in(k,n)$** — i.e. each rail fails independently with
probability $\approx k/p$, which is exactly the heuristic that a random residue of $n$ mod
$p$ lands below $k$.

## Measured
| $n$ | $k$ | $\omega\binom nk$ | $k\sum_{k<p<n}1/p$ | ratio |
|---|---|---|---|---|
| 5000 | 20 | 26 | 19.0 | 1.369 |
| 5000 | 70 | 61 | 47.3 | 1.288 |
| 5000 | 300 | 166 | 117.7 | 1.410 |
| 20000 | 50 | 53 | 44.7 | 1.187 |
| 20000 | 140 | 120 | 94.5 | 1.270 |
| 20000 | 900 | 456 | 334.4 | 1.364 |

**The ratio sits at $1.19$–$1.41$ with no visible trend toward 1.** This does not refute the
conjecture — it is asymptotic, and $n\le2\times10^4$ is small — but it is worth recording
that the predicted constant is *not* yet visible, and the excess is systematic (every entry
above 1, none approaching it).

**Reading the excess.** The prediction counts only rails in $(k,n)$. Rails $p\le k$ also
divide $\binom nk$ generically, and there are $\pi(k)$ of them; at $n=5000,k=300$ that is
$62$ rails against an excess of $166-118=48$. So the discrepancy is roughly *the small rails
the prediction omits* — suggesting the correct statement carries an additive $\pi(k)$-type
term, or that the $o(1)$ is genuinely slow.

## Register
**Proved:** the domination form of $\omega\binom nk$. **Measured:** the table; the
systematic $1.19$–$1.41$ excess. **Not proved:** anything asymptotic.
**Falsifier, pre-registered:** the ratio failing to approach 1 as $n\to\infty$ along
$k=n^{1/2}$ would be evidence against the conjecture as stated.
**Next:** run $k=n^{1/2}$ for $n$ up to $10^7$ (cheap — domination only) and test whether
the ratio tends to 1 or to a constant $>1$; and separately test the corrected form
$\omega=\pi(k)+(1+o(1))k\sum_{k<p<n}1/p$.
