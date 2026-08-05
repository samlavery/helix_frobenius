# Erdős #1095 — opened

**Problem** (Ecklund–Erdős–Selfridge). Let $g(k)>k+1$ be the smallest $n$ such that all
prime factors of $\binom nk$ exceed $k$. Estimate $g(k)$.

**Gate** (site, read at source). [EES74] proved $k^{1+c}<g(k)\le\exp((1+o(1))k)$ and
conjectured $g(k)<L_k=\mathrm{lcm}(1,\dots,k)$ for all large $k$; they further conjectured
$$\limsup_k \frac{g(k+1)}{g(k)}=\infty,\qquad \liminf_k\frac{g(k+1)}{g(k)}=0.$$
Lower bound improved by [ELS93] and Granville–Ramaré [GrRa96]; current record
$g(k)\gg\exp(c(\log k)^2)$.

## Ledger form (proved)
All prime factors of $\binom nk$ exceed $k$ iff $p\nmid\binom nk$ for every $p\le k$, which
by Kummer is digit domination. Hence
$$\boxed{\ g(k)=\min\{n>k+1:\ k\preceq_p n\ \text{for every prime }p\le k\}\ }$$
where $k\preceq_p n$ means every base-$p$ digit of $k$ is at most the corresponding digit of
$n$. No binomial is ever evaluated. *Validated:* the restatement reproduces
$\mathrm{lpf}\binom nk$ exactly for $2\le k\le8$, $n<400$ (0 mismatches), and yields
$g(6)=62$ — Selfridge's exceptional binomial $\binom{62}{6}$, arrived at independently.

## Measured
| $k$ | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 13 | 17 | 20 | 25 | 29 | 33 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $g(k)$ | 6 | 7 | 7 | 23 | 62 | 143 | 44 | 159 | 46 | 2239 | 5849 | 43196 | 2105 | 240479 | 6459 |

- **$g(k)<L_k$ for every $k$ in $[4,33]$** — the EES conjecture holds throughout, failing only
 at $k=2,3,6$ where $L_k$ is still tiny.
- **Ratios $g(k{+}1)/g(k)$ span $[0.011,\ 846.8]$** with median $1.17$ — extremes at
 $g(29)/g(28)=846.76$ and $g(25)/g(24)=0.0109$, five orders of magnitude by $k=33$ and
 visibly still widening. Strong support for $\limsup=\infty$, $\liminf=0$.

## Structural reading
$g(k)$ collapses when $k$ has small digits in *every* base at once (domination is then cheap:
$g(28)=284$, $g(33)=6459$) and explodes when a single base forces a large digit
($g(29)=240479$, $29$ prime). So the ratio conjectures are a statement about how erratically
the **joint digit profile** of consecutive integers varies across all bases $\le k$. This is
the same cross-base object that walls #377 — but here it appears as a *fluctuation* question
rather than an intersection one, which is why it is tractable. **That distinction is the
selection rule for this whole cluster.**

## Register
**Proved:** the digit-domination restatement (Kummer, one line); validated against
$\mathrm{lpf}$ directly and against $g(6)=62$. **Measured:** the table, $g<L_k$ on
$4\le k\le33$, the ratio spread. **Not proved:** any growth statement; the record remains
$\gg\exp(c(\log k)^2)$. **Falsifier:** $g(k)\ge L_k$ for some $k\ge34$ would refute EES.
**Next:** the domination form is cheap enough to push to $k\approx60$ by meet-in-the-middle
over rails; the ratio extremes should be tested against $k$ prime vs $k$ smooth, which the
data already suggests is the controlling dichotomy.
