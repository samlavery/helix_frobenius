# Sweep and explicit-anchor update review — 2026-09-06

The latest dependency build of `RequestProject.BoundedIffRH` exited zero:
`Build completed successfully (9556 jobs).` Its printed audit includes exactly
`[propext, Classical.choice, Quot.sound]` for the jet-to-atom identity, the explicit
ladder theorem, and the explicit boundedness theorem. This verifies those
statements and their hypotheses; it does not establish the coefficient estimate.

## What the new source establishes

- `HerglotzSweep.lean`: the multiplicity-weighted, summed sweep identity, with
  the original, reflected, and moved anchors off the zero set.
- `JetsAreAtoms.lean`: the explicit prime-and-Gamma jet coefficients equal the
  multiplicity-weighted atom coefficients. The positive-order derivative series
  is proved on zero-free neighborhoods. Its theorem has `1 ≤ k`; order zero
  uses the regularized partial fractions and the mirror identity.
- `BoundedIffRH.lean`: one bound uniform in the coefficient index is sufficient
  for the zero-location conclusion. The proof isolates a maximal transported
  atom by Cesaro averaging, controls the infinite tail, and retains analytic
  multiplicities. It does not assume simple zeros.

The explicit Dirichlet series is absolutely convergent at `Re s < 0`, after
reflection to `1-s`. In `xiHerglotz_explicit`, replacing the moved logarithmic
derivative by that explicit series also requires `Re (movedAnchor s z) < 0`.
The meromorphic sweep identity has a larger domain, with its poles excluded.

## Exact normalization and sign

Writing `c = 1-conj(s)` and `u = (s+zc)/(1+z)`, the inverse is
`z = (s-u)/(u-c)`. For `Re s, Re u < 1/2`, this inverse lies in the open disc.

The precise seat normalization is

`Re Phi_s(z) = ((1-|z|^2)/|1+z|^2) * seatMass(u)`.

The factor is strictly positive in the disc. Thus the signs agree, while the
numerical masses differ by this factor. Ledger 626 already writes the depth
ratio in its summed formula; the short note and the `xiHerglotz_re` docstring
should keep that qualification too.

Ledger 626(ii)'s `Re G_r ≤ 0` had the wrong sign and is corrected to `> 0`.
For positive clock length,
`|beta| ≤ 1`, and a channel point, `Re G_beta > 0`. With
`logDeriv(cond) = -G_r - ell/2` and `d_s < 0`, this gives the stated lower bound
for the swept real part normalized by the original anchor.

Angular scale `1/N` corresponds to far-height reach of order `N*(1-2 sigma)`
near the antipode. It is not uniform resolution in height: the exact boundary
map is `t + ((1-2 sigma)/2)*tan(theta/2)`.

## Numerical and carrier claims to keep precise

`tmp/att631_results.txt` lists 15 cutoffs from 2 through 2,000,000. Every listed
six-dimensional matrix has a negative computed minimum eigenvalue. This is
numerical evidence against positivity of all these truncations, not a theorem
about every finite cutoff or every finite construction. The listed value at
`P=30` is `-0.398583`, rather than the attachment's `-0.34`.

The per-prime carrier identity is a useful normalization check. In its DC
cancellation, the normalized transported Lebesgue density is
`|d|/(2*pi) * |s-1/2-iy|^(-2)`, and its multiplier `ell/|d|` gives the
`ell/(2*pi)` constant Fourier term of the Poisson density.

Passing from each prime to `Re sum_n Lambda(n)*n^(-1/2-iy)` requires a specified
summation procedure and test-function space. Degreewise tested identities do
not supply continuity on the full smooth circle test space or a bound uniform
in degree. Keep those convergence and continuity assertions explicit when
constructing the carrier functional.

## Polynomial-growth continuation

The maximal-atom proof uses boundedness only to obtain
`mu_k/R^k -> 0` for every real `R > 1`. A polynomial estimate
`|mu_k| <= C*(1+k^p)`, for one fixed `C` and natural `p`, supplies this decay.
`SubexponentialAnchor.lean` formalizes this extension, including a consumer at
`s = -1+20i` that concludes Mathlib's literal `RiemannHypothesis` from the
polynomial estimate. Both new Lean files passed `lake env lean` with exit code
zero; all printed footprints are `[propext, Classical.choice, Quot.sound]`.
The complete outputs are in [SWEEP_UPDATE_VERIFICATION.md](SWEEP_UPDATE_VERIFICATION.md).

A concrete next construction is a finite-order bound for the completed carrier
functional on the modes `w^k`. Such a bound must have constants independent of
`k`, and the functional must be identified with the existing explicit
coefficients. This permits a polynomial estimate; total-variation boundedness
of an ordinary finite measure is stronger than this route needs.

The remaining arithmetic estimate is:

```lean
∃ C : ℝ, ∃ p : ℕ, ∀ k,
  ‖toeplitzCoeff (-3) (jets explicitLogDeriv ((-1 : ℂ) + 20 * I)) k‖ ≤
    C * (1 + (k : ℝ) ^ p)
```

The geometric sweep and growth consumers do not establish this displayed
estimate. No unconditional RH or GRH discharge is asserted in this review.
