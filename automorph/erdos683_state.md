# Erdős #683 — opened

**Problem.** Is it true that for every $1\le k\le n$ the largest prime divisor satisfies
$$P\!\left(\binom nk\right)\ \ge\ \min\bigl(n-k+1,\ k^{1+c}\bigr)$$
for some constant $c>0$?

**Gate** (site, read at source). Sylvester–Schur: $P\binom nk>k$ for $k\le n/2$.
Erdős [Er55d]: there is $c>0$ with $P\binom nk\gg k\log k$ for $k\le n/2$. Erdős [Er79d]
writes it "seems certain" this holds for *every* $c>0$ with only finitely many exceptions
depending on $c$; standard prime-gap heuristics support it.

## Ledger form
$P\binom nk=\max\{p\le n:\ k\not\preceq_p n\}$ — the **largest rail on which $k$ fails to
dominate $n$**. Note the contrast with #1094, which asks for the *smallest* such rail: the
two problems are the two ends of the same domination spectrum, and #1095 asks when the
spectrum is empty below $k$. Three problems, one object.

## Measured
Over $n<1200$, $3\le k<60$, restricted to pairs where the binding term is $k^{1+c}$ (i.e.
$P<n-k+1$), the smallest admissible exponent is
$$c_{\min}=0.4650\quad\text{at }(n,k)=(10,3),\ P\binom{10}{3}=P(120)=5.$$
So on this range $c=0.465$ suffices, and the extremal case is tiny — consistent with Erdős's
expectation that any fixed $c$ has only finitely many exceptions, since the worst case is not
drifting upward with $n$.

## Structural reading
The quantity is a **maximum over rails**, so by this session's rule the instrument is the
dwell: rather than tracking $\max_p$, re-register the whole failure spectrum
$\{p:\ k\not\preceq_p n\}$ and read its top order statistic. The spectrum's density near $p$
is $\approx k/p$ (a random residue of $n$ mod $p$ lands below $k$), so the expected largest
failing rail is where $\sum_{p>P}k/p\approx1$, i.e. $\log\log n-\log\log P\approx1/k$ —
giving $P\approx n^{e^{-1/k}}$, which is $\gg k^{1+c}$ for every $c$ once $k$ is large. That
heuristic is the same one the gate attributes to prime gaps, arrived at from the rail side.

## Register
**Proved:** the domination form of $P\binom nk$, and its duality with #1094 and #1095.
**Measured:** $c_{\min}=0.4650$ at $(10,3)$ over the stated range.
**Not proved:** the conjecture for any $c$. **Falsifier:** $c_{\min}$ declining with the
range would indicate no fixed $c$ works — it did not here.
**Next:** extend to $n<10^6$ tracking $c_{\min}$ as a function of the cutoff, and test the
dwell prediction $P\approx n^{\exp(-1/k)}$ directly against the measured top order statistic.
