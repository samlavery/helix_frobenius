# Erdős #700 — opened

**Problem** (Erdős–Szekeres). Let
$$f(n)=\min_{1<k\le n/2}\gcd\!\left(n,\binom nk\right).$$
Characterise the composite $n$ with $f(n)=n/P(n)$, where $P(n)$ is the largest prime factor.
Are there infinitely many composite $n$ with $f(n)>n^{1/2}$? Is $f(n)\ll_A n/(\log n)^A$?

**Gate** (site, read at source). $f(n)\le n/P(n)$ for composite $n$, since taking $j=p^a\|n$
gives $\gcd(n,\binom nj)=n/p^a$; hence $f(n)\le(1+o(1))n/\log n$. Known that
$f(n)=n/P(n)$ when $n$ is a product of two primes; **another example is $n=30$**.

## Ledger form
For $p\mid n$ with $p^a\|n$,
$$v_p\!\left(\gcd\!\left(n,\binom nk\right)\right)=\min\bigl(a,\ \kappa_p(k,n{-}k)\bigr),$$
where $\kappa_p$ counts carries in the base-$p$ addition $k+(n-k)$ (Kummer). So
$$f(n)=\min_{1<k\le n/2}\ \prod_{p^a\|n}p^{\min(a,\,\kappa_p(k,n-k))},$$
a minimisation over $k$ of a product of *per-rail carry counts capped by the rail's exponent
in $n$*. The cap is the new feature relative to #400/#727: rail $p$ contributes at most
$v_p(n)$ no matter how many carries occur, so **the rails saturate**, and $f$ is governed by
how few rails can be made to carry simultaneously.

## Measured ($n<600$, composite)
- **$f(n)=n/P(n)$ for 307 composite $n$**, beginning $4,6,9,10,14,15,20,21,22,25,26,28,30,33$
 — consistent with the gate (semiprimes, and $n=30$ present).
- **$f(n)>\sqrt n$ for 30 composite $n$**: $30,70,84,105,132,140,154,165,168,182,\dots$ with
 $f=6,10,12,15,12,14,14,15,21,14$. These are squarefree or near-squarefree with several
 small prime factors — the structure that lets *every* rail saturate its cap at once.
 The count is still growing at the top of the range, so the infinitude question looks
 affirmative on the data.

## Structural reading
$f(n)>\sqrt n$ requires a $k$-free obstruction: for **every** $k$ some large sub-product of
$n$ must carry. Rails with $v_p(n)=1$ cap at $p^1$, so $f(n)\le\prod_{p\mid n}p=\mathrm{rad}(n)$
with equality only if every rail carries for every $k$ — which is why the $f>\sqrt n$ list is
squarefree-dominated and why $f(n)\le n/P(n)$ is tight so often.

## Register
**Proved:** the capped-carry formula for $f(n)$ (Legendre/Kummer, one line).
**Measured:** the two censuses above. **Not proved:** the characterisation, the infinitude of
$f(n)>\sqrt n$, or the $n/(\log n)^A$ bound.
**Falsifier:** $f(n)>\sqrt n$ ceasing at larger $n$ would contradict the apparent growth.
**Next:** census to $n=10^5$ and test whether $\{n:f(n)>\sqrt n\}$ has positive density; and
characterise the $f(n)=n/P(n)$ set by $\Omega(n)$ and squarefreeness — the data suggests a
clean statement is available there, which is exactly what Erdős asks for.
