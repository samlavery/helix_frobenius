# Refutation spec: can a real-node configuration reach a complex-conjugate pair without a transversal wall crossing?

**Self-contained.** No background beyond undergraduate linear algebra and
polynomial algebra is needed. Nothing here refers to any particular research
program; the question is about finite discrete measures on the line.

## The claim to be tested

Let `μ_t = Σ_{i=1}^{n} w_i(t) δ_{x_i(t)}`, `t ∈ [0,1]`, be a continuous
one-parameter family of discrete measures on `ℂ` with

* `n` fixed,
* nodes `x_i(t)` and weights `w_i(t)` depending continuously on `t`,
* the moment sequence `m_k(t) = Σ_i w_i(t) x_i(t)^k` REAL for every `k` and `t`
  (equivalently, non-real nodes occur in conjugate pairs with conjugate weights),
* at `t = 0` all nodes are real and distinct, and all weights are positive,
* at `t = 1` at least one conjugate pair of non-real nodes is present.

Let `H(t)` be the `n × n` Hankel matrix `H(t)_{ij} = m_{i+j}(t)`,
`0 ≤ i, j ≤ n−1`.

**CLAIM (C):** every such family satisfies both

1. there exists `t* ∈ (0,1)` at which two nodes coincide (`x_i(t*) = x_j(t*)`
   for some `i ≠ j`); and
2. `det H(t)` changes sign at such a transition — i.e. the passage from the
   all-real configuration to the conjugate-pair configuration cannot occur
   through a zero of `det H` of even order (a "touch").

Consequently no choice of path, and no genericity/transversality perturbation
argument, can route from configuration 0 to configuration 1 while keeping
`det H > 0` throughout.

## Why this is not vacuous

Note (2) does NOT claim that node coincidence always produces a sign change.
A path may merge two real nodes and re-separate them as real nodes; then
`det H` touches zero and stays nonnegative. The claim is specifically about
transitions that END with a conjugate pair.

## Procedure

1. **Symbolic check, `n = 2`.** With nodes `±s` and unit weights, compute
   `m_0, m_1, m_2` and `det H = m_0 m_2 − m_1²`. Verify `det H = 4s²`.
   Reparametrise by `τ = s²` (real `τ > 0` ↔ two real nodes; `τ < 0` ↔ a
   conjugate pair `±i√(−τ)`). Report `d(det H)/dτ` at `τ = 0`.
2. **Symbolic check, conjugate pair.** For `μ = w δ_z + w̄ δ_z̄` with
   `z = x + iy`, `w = u + iv`, compute `det H` in closed form and report it.
3. **General `n`, discriminant argument.** For real monic `p` of degree `n`
   with roots the nodes, compute `sign(disc p)` for (a) all roots real and
   distinct, (b) exactly one conjugate pair, (c) exactly two conjugate pairs.
   Report the three signs.
4. **Search for a counterexample to (1).** Attempt to construct, numerically
   or symbolically, a continuous family meeting the hypotheses in which no two
   nodes ever coincide. Use `n = 3` and `n = 4`, and try paths in coefficient
   space, in node-and-weight space, and in moment space.
5. **Search for a counterexample to (2).** Attempt to construct a family in
   which the transition to a conjugate pair occurs at a zero of `det H` of
   even order, so that `det H ≥ 0` throughout.

## Decision rule, fixed in advance

* If step 4 produces a family with no node coincidence, **(C.1) is REFUTED**.
* If step 5 produces a family whose `det H` has an even-order zero at the
  transition and remains `≥ 0`, **(C.2) is REFUTED**.
* If step 3 returns signs `+, −, +` for (a), (b), (c), and steps 4 and 5
  return no counterexample after honest effort, **(C) is SUPPORTED**.
* Any outcome in which `det H` and `(∏_i w_i)·disc(p)` disagree numerically
  indicates an error in the executor's setup, not evidence either way.

## Predicted outcome, recorded before the fact

I predict **(C) is SUPPORTED**, and specifically:

* step 1 returns `det H = 4s² = 4τ`, so `d(det H)/dτ = 4 ≠ 0` — transversal;
* step 2 returns `det H = −4y²(u² + v²)`, strictly negative for `y ≠ 0`;
* step 3 returns `+`, `−`, `+`;
* steps 4 and 5 fail, because `sign(disc) = (−1)^{r₂}` with `r₂` the number of
  conjugate pairs, and `disc` is a polynomial in the coefficients hence
  continuous: going from `r₂ = 0` to `r₂ = 1` forces `disc = 0`, which is
  exactly a repeated root, and a sign change cannot occur at a zero of even
  order.

## Reason the prediction might be wrong

The weakest point is step 5 at `n ≥ 3`: `det H = (∏_i w_i)·disc(p)`, so a
family in which some weight `w_i(t)` passes through zero at the same `t` could
in principle keep `det H` from changing sign while the nodes go complex. The
executor should test that case explicitly — weights vanishing simultaneously
with a node merge — since it is the one mechanism that could separate the sign
of `det H` from the sign of `disc`. If such a family exists and meets all the
hypotheses (including positivity of weights at `t = 0`), (C.2) fails and the
conclusion drawn from it does not hold.
