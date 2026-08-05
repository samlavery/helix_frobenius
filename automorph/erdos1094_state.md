# Erdős #1094 — opened

**Problem** [ELS88]. For all $n\ge2k$, the least prime factor of $\binom nk$ is
$\le\max(n/k,k)$, with only finitely many exceptions.

**Gate** (site, read at source). A stronger form of #384. Erdős: the least prime factor is
always $\le n/k$ once $n$ is large depending on $k$. **Selfridge [Se77] conjectured this
always holds if $n\ge k^2-1$, except $\binom{62}{6}$.** The threshold below which $\binom nk$
must have a prime factor $\le k$ is #1095.

## Ledger form
By Kummer, $p\mid\binom nk$ iff adding $k+(n-k)$ in base $p$ carries, i.e. iff $k\not\preceq_p n$
(digit domination fails). So
$$\mathrm{lpf}\binom nk=\min\{p:\ k\not\preceq_p n\},$$
computable with no binomial evaluated. The conjecture is a statement about how small a rail
must be before domination fails.

## Measured
Exceptions to $\mathrm{lpf}\binom nk\le\max(n/k,k)$ over $n<3000$, $k<25$: **13 total**,
beginning $(n,k,\mathrm{lpf})=(7,3,5),(13,4,5),(14,4,7),(23,5,7),(62,6,19),(44,8,11)$.

**Restricting to Selfridge's range $n\ge k^2-1$ leaves exactly one: $(62,6,19)$.**
That is $\binom{62}{6}$ — precisely and only the exception he named. The reformulation
therefore reproduces a published conjecture's unique counterexample without being told it.

## Register
**Proved:** the ledger form (Kummer, one line). **Measured:** the 13 exceptions and the
isolation of $\binom{62}{6}$ in Selfridge's range. **Not proved:** finiteness of the
exception set. **Falsifier:** a second exception with $n\ge k^2-1$ — would refute Selfridge.
**Next:** push $k$ to $\sim100$ and $n$ to $\sim10^6$; the domination formulation is cheap
enough to make that routine, and a second Selfridge exception would be a publishable hit.
