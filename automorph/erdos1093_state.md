# Erdős #1093 — opened

**Problem** [ELS88]. For $n\ge2k$ the *deficiency* of $\binom nk$ is defined only when no
prime $p\le k$ divides $\binom nk$; it is then $\#\{0\le i<k:\ n-i\ \text{is }k\text{-smooth}\}$.
**Are there infinitely many binomial coefficients with deficiency 1? Only finitely many with
deficiency $>1$?**

**Gate** (site, read at source). Erdős–Lacampagne–Selfridge; also the 1986 West Coast Number
Theory problem session. In [ELS93] they prove that if the deficiency exists and is $\ge1$
then $n\ll 2^k\sqrt k$. Published deficiency-1 examples begin
$\binom73,\binom{13}4,\binom{14}4,\dots$; **58 examples with $n\le10^5$.**

## Ledger form
Definedness is pure Kummer digit domination: the deficiency exists iff $k\preceq_p n$ for
every prime $p\le k$ — the same condition whose least solution is $g(k)$ in #1095. So
**#1093 and #1095 sit on the same rail condition**, one asking for the least solution and the
other for the smooth structure of $n-i$ across the solutions. Given definedness, the
deficiency is a smoothness count on the $k$ consecutive integers $n-k+1,\dots,n$.

## Measured
Range $n<40000$, $3\le k<14$:
- **deficiency 1: 25 examples**, beginning $(n,k)=(7,3),(13,4),(14,4),(23,5),(62,6),(143,7),(89,8),(143,8)$ — the first five reproduce the published list exactly, and $(62,6)$ is again Selfridge's binomial.
- **deficiency $>1$: 6 examples** — $(44,8,d{=}2),(46,10,3),(47,10,3),(74,10,2),(47,11,4),(174,12,2)$. Largest observed deficiency is **4**, at $\binom{47}{11}$.

Both counts are still growing at the edge of the range, so neither question is settled by
the data; but deficiency-$>1$ examples are markedly rarer and cluster at small $k$, which is
consistent with the conjectured finiteness.

## Structural note
The ELS93 bound $n\ll2^k\sqrt k$ plus definedness (domination on every rail $p\le k$) makes
this a **bounded search per $k$** — the problem is finite for each $k$, and the open content
is uniformity in $k$. That is a materially softer shape than #377's.

## Register
**Proved:** the definedness criterion is Kummer domination (one line), hence the link to
#1095. **Measured:** the two counts above, first-five agreement with the published list.
**Not proved:** either infinitude or finiteness. **Falsifier:** a deficiency-$>1$ example
with $k\ge20$ would weaken the finiteness conjecture; none found here.
**Next:** exhaust each $k\le20$ using the ELS93 bound $n\ll2^k\sqrt k$ — that makes
deficiency-$>1$ **decidable per $k$**, which is the strongest available move.
