# The height extractor

Reference implementation for *A carrier readout for the zeros of ζ, and a
machine-checked index-to-ordinate extractor* (`automorph/zero_extractor.tex`).

Given an index `i`, returns an interval containing the `i`-th ordinate of ζ on the
critical line.

## Two layers, and the difference matters

**The locator** (`helix_extractor.py`) is float64 and fast. It finds the bracket and
narrows it. Its internal guard is a measured noise floor — a heuristic, not a proof.

**The certifier** (`certified_zeta.py`, `region_bounds.py`) carries explicit error
bounds and *proves* what the locator found. Nothing in the locator is trusted by it.

Read the validation table below as evidence that the locator works. The certificates
come from the second layer.

## Requirements

`python3`, `numpy`, `mpmath`. Nothing else — in particular no ball-arithmetic library
is needed: the certified evaluator is built here from Euler–Maclaurin with its explicit
remainder.

## Usage

```
python3 helix_extractor.py 1 10 100 1000 --verify
```

| flag | meaning |
|---|---|
| `--delta` | carrier scale Δ (default π/3). Output is Δ-free; `--scales` tests that. |
| `--tol`   | head tolerance, setting head length via `X = 2(T+K)/π`, `K = (ln(1/tol)/1.43)²` |
| `--x`     | Selberg cutoff for the prime clocks (default 100) |
| `--m`     | jet order (default 9) |
| `--verify`| compare against `mpmath.zetazero(i)` |
| `--scales`| rerun across several carrier scales |

**`--tol` sets the head *length*, not the accuracy achieved.** The float64 bank floors
near `1e-13` relative (≈`3e-10` at T = 1.5e4), because the phase `T·log(Δn)` carries
error ~`T·log(X)·2.2e-16`. Past the floor a longer head buys nothing.

## The certified layer

- `certified_zeta.py` — `zeta_enclosure(s) -> (value, radius)` with `|ζ(s) − value| ≤ radius`,
  from Euler–Maclaurin with the classical explicit remainder plus a rounding allowance.
- `region_bounds.py` — `xi_region_bound(m, r)`: an explicit `M` with `|Ξ(z)| ≤ M` on a
  disc. Needs `|h| + r < 1/2`, which is exactly Stirling's `Re(s/2) > 0`, not a coding
  limit. Validated as a true upper bound; loose by 25×–520×, which costs step size only.

What these certify, on the extractor's own output: **signs** (margins 7e11–6e36),
**`Ξ' ≠ 0`** on the returned intervals (margins 1e4–2e8), and the **count** by contour.

## Validation

```
python3 extractor_validate.py
```

Exhaustive `1 ≤ i ≤ 200`, 90 random in `201 ≤ i ≤ 2×10⁴`, spot checks to `i = 10⁶`, and
Lehmer's pair. **297 indices, 0 failures.** Reference ordinates from `mpmath.zetazero`,
which shares no code with anything here.

Lehmer's pair is the one that matters: `7005.062866174921` and `7005.100564672656`,
0.042 of a mean spacing apart. A fixed-step march at 0.30 spacings returned γ₆₇₁₁ for
i = 6710 — a real failure of an earlier version, and why stage 2 is bisection on a
monotone predicate.

## Checks

Each has its decision rule fixed before it runs.

| script | claim |
|---|---|
| `checks/theta_identity.py` | `arg Γ_ℝ(½+it) = ϑ(t)` to 2.5e−57 |
| `checks/jet_sweep.py` | ratio-enclosure contraction = κ (1.2–2.7%); **refuted at κ=0.882** |
| `checks/count_error_grid.py` | `max\|S_x − S\|` = 0.502, 0.518 |
| `checks/Sx_bounded.py` | `\|S_x\| ≤ B(x)`; B(100) = 12.43 |
| `checks/Sx_growth.py` | `max\|S_x − S\|` already > ½ at every height |
| `checks/root_number_rays.py` | χ₅, χ₇ rays 0.088104π, 0.186840π |
| `checks/balance_law_refuted.py`, `checks/balance_law_independent.py` | the μ6 balance law is **false** |
| `checks/pencil_lane_control.py` | lane nodes at `Im y = −½` to 2e−14 |
| `checks/rank_drop.py` | rank = #**distinct** nodes; σ₂/σ₁ ≈ 4.2ε² |
| `checks/lehmer_rank.py` | the pair resolves at rank 2 |
| `checks/head_law_decay.py`, `checks/head_law_moments.py` | `−ln(err)/s ∈ [1.400, 1.485]` |
| `checks/head_threshold.py` | `X_min` vs `2T/π`, by tolerance |
| `checks/deriv_in_cell.py` | `Ξ'` **does** vanish in the stage-2 bracket |
| `checks/two_ended_head.py` | two-ended head, **198×** at T = 5.76e5 |
| `checks/region_bounds_val.py` | `M` is a true upper bound |
| `checks/certified_signs.py`, `checks/certified_deriv.py`, `checks/certified_count.py` | the certificates |
| `checks/certified_bisect.py` | narrowing is evaluator-limited, not bank-limited |
| `checks/winding_unsound.py` | the naive winding criterion is **unsound** |
| `checks/sx_formula.py` | the printed `S_x` formula equals the code's |

`checks/UNSOUND_winding_attempt.py` is kept as a record of a criterion that looked sound
and was not. **Do not use it as a certifier**; `checks/certified_count.py` is the sound
version.

## Things worth knowing before trusting a number here

- **The locator instantiates the product theorem, not the capstone.** The capstone needs
  `Ξ' ≠ 0` across the cell, and that is *false* on the stage-2 bracket — a critical point
  of Ξ sits inside it at i = 10, 100, 1000. It holds on the narrow returned interval, and
  that is where `checks/certified_deriv.py` certifies it.
- **Rank detects coincidence, not multiplicity.** A double node and a simple node give
  bit-identical singular-value profiles.
- **Three propositions here were refuted, not proved**: the μ6 balance law, the naive
  winding criterion, and `|S_x − S| < 1` at fixed cutoff. All three by the same move —
  a finite object cannot track an unbounded one.
