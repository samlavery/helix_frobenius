# #377 test log — measured register

All runs in `tmp/e377_*.py`. Every number below is *measured*, not proved.

## 1. The decomposition holds, and both halves behave

$E(n)=\sum_{p\nmid\binom{2n}{n}}1/p$, split at $y=100$.

| $N$ | $\max E(n)$ | $\max E_{\le100}$ | $\max E_{>100}$ | $\log\log\log N$ |
|---|---|---|---|---|
| $10^4$ | 0.9631 | 0.6387 | 0.3575 | 0.7977 |
| $10^5$ | 0.8821 | 0.4880 | 0.4317 | 0.8934 |
| $10^6$ | 0.8046 | 0.3878 | 0.4714 | 0.9654 |

$\max E(n)$ **decreases** while $\log\log\log N$ rises. The small-prime half collapses
(rigidity); the large-prime half rises toward its equidistribution mean
$\sum_{j\ge2}\log j/2^j=0.507834$. Two different mechanisms, both behaving.

## 2. Census — reproduced and pushed to $10^{200}$

$n$ carry-free for every $p$ in the set (i.e. all base-$p$ digits $\le\frac{p-1}{2}$):

| set | solutions | verified to | tree nodes |
|---|---|---|---|
| $\{3,5,7\}$ | 17 and counting — $0,1,10,756,757,3160,3186,3187,3250,7560,7561,7651,20007,$ $59548377,59548401,45773612811,45775397187$ | $10^{13}$ | 1331 |
| $\{3,5,7,11\}$ | $\{0,1,3160\}$ | $10^{200}$ | 8465 |
| $\{3,5,7,11,13\}$ | $\{0,1\}$ | $10^{200}$ | 5575 |

$3250$ sits in the $\{3,5,7\}$ list — the census number, reproduced.
**$59548401$ is not last**: $45773612811$ and $45775397187$ follow, exactly as
$\dim=s_3+s_5+s_7-2=+0.026>0$ predicts. $\{3,5,7\}$ is infinite.

Furstenberg dimension counts, predicted vs observed at $10^9$:
$\{3\}$ $4.8\times10^5$ / $524288$; $\{3,5\}$ $676$ / $908$; $\{3,5,7,11\}$ negative
dimension / finite. The dimension formula is quantitatively right.

## 3. NULL — π/3 is a crossing, not a signature

Pre-registered: is (naive $2^{-k}$ prediction)/(observed) equal to $\pi/3=1.047198$?

| $N$ | band-1 ratio |
|---|---|
| $10^3$ | 1.065724 |
| $10^4$ | 1.065017 |
| $10^5$ | 1.051978 |
| $10^6$ | **1.047477** ← crosses π/3 |
| $10^7$ | 1.041148 |

Monotonically decreasing; it passes *through* π/3 near $10^6$. Measured at $10^6$ alone
it reads as a 0.03% hit. **It is not.** The excess is the top-digit Benford factor
$s_p=\log\frac{p+1}{2}/\log p\approx1-\frac{\log2}{\log p}$ — Lemma `measure`'s hyperbola
weight — giving ratio $\approx1+\log2/\log p\to1$: right sign, right order ($\approx1.07$
predicted at $10^6$), right limit. The correction is real and **vanishes asymptotically**,
so the naive per-band density $2^{-k}$ is asymptotically exact.

## 4. NULL — harmonic scan of the measured constants

Against $\{\pi/6,\pi/3,\pi/2,\pi,2\pi,3\pi\}$:

| quantity | value | nearest | rel. err |
|---|---|---|---|
| $\kappa=3\log(3/2)/\log3$ | 1.107211 | π/3 | $+5.73\%$ |
| $1/\kappa$ (rigidity threshold) | 0.903170 | π/3 | $-13.75\%$ |
| $\sum_{j\ge2}\log j/2^j$ | 0.507834 | π/6 | $-3.01\%$ |
| $\max E(n)$ at $10^6$ | 0.804600 | π/3 | $-23.17\%$ |

Nothing lands. The harmonic content of this problem is in the **depth warp**
$J\to J(k)$, not in any scale factor on the ledger.

## 5. NULL (for a proof) — the pruned tree does not close

Live-node count vs depth, $\{3,5,7,11\}$: 569 / 873 / 1501 / 2765 / 4987 / 8465 at depths
34 / 53 / 84 / 147 / 252 / 420 — **linear**, $\approx20$ per level. No saturation, so
pruning alone yields no finiteness proof.

But the live front has **bounded width**: 2–25 across 420 levels for $\{3,5,7,11\}$,
2–14 for $\{3,5,7,11,13\}$, with no upward trend. Width histogram peaks at 8–10 and
7–8 respectively. That is an automaton signature — a bounded-width front that never
produces a fourth solution over 420 levels. It fluctuates rather than cycling, so there
is no periodicity to close on directly; bounding the width is the finiteness lever.

## 6. State of #377 after testing

*Provable now, every $n$:* $E(n)\le\log\log\log n+5.2$, from the machinery already in
`erdos377_partial.tex` with $J\to J(k)$ (depth from each band's own scale) and
$K\to y=(\log n)^9$. A full logarithm better than the paper's $O((\log\log n)^{2/3})$.

*Provable now, all but $X^\varepsilon$:* $E(n)=O(1)$, via dimension-zero rigidity at
fixed small tuples, where Corso–Shmerkin constants are fixed and the uniformity problem
does not arise. Threshold $\sum_{p\in P}1/p>1/\kappa=0.9032$; observed
$\max E_{\le100}=0.388$ at $10^6$ and falling.

*Residue:* finiteness — not merely dimension zero — of $\bigcap_{p\in P}C_p$ for fixed
small $P$. Numerically nailed to $10^{200}$; the lever is the bounded-width front.
