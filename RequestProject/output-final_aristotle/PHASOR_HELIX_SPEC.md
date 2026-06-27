# L-function Phasor Helix — Specification & Reproduction Guide

A self-contained description of a model that represents Dirichlet L-functions as
**phasor arrows carried on a 3-D Archimedean helix**, where the **cancellations**
(the `+` and `−` channels annihilating) are the **zeros of the L-function**.

This document is written so a second agent can **independently verify** every
claim — either by running the reference module `lfunction_phasor_bank.py`, or by
re-deriving the numbers from the formulas below (do not trust the code blindly;
the verification recipe in §7 recomputes the zeros from an independent definition).

---

## 1. The model in one screen

On the critical line `s = σ + i y` with `σ = 1/2`, term `n` is a **phasor**:

```
phasor(n, y) = chi(n) · magnitude(n) · exp(−i · y · spin(n))
             = chi(n) · n^(−σ)       · exp(−i · y · ln n)      (defaults)

S(y) = Σ_{n≥1} phasor(n, y) = L(chi, σ + i y)
```

- **`chi(n)` — the channel/sign**, one of `+1` / `−1` / `0` (for a real character).
- **`magnitude(n) = n^(−σ)` — the arrow length** (decays).
- **`spin(n) = ln n` — the spin rate** (each phasor spins at its own `ln n`).

**Cancellation criterion (this is the whole point):** a zero is **not** "one
channel is small." It is `P = M`, the `+`-channel vector sum equal to the
`−`-channel vector sum:

```
P(y) = Σ_{chi(n)=+1} n^(−σ) e^(−i y ln n)
M(y) = Σ_{chi(n)=−1} n^(−σ) e^(−i y ln n)
S = P − M ;   L(chi, ½+iy) = 0  ⇔  P = M   ("negative = positive")
```

Each lane `P`, `M` **individually diverges** (`~ N^(1−σ) = √N`); only the
difference converges. The zero is where the two divergent spirals coincide.

---

## 2. The carrier: a genuine 3-D Archimedean helix

The integer `n` is the **unit step**. Phasor `n` sits at **3-D arc length**
`s_n = unit_distance · n` along an Archimedean spiral. Fixed constants:

| constant | symbol | value | meaning |
|---|---|---|---|
| unit distance | `u` | `π/3` | **radial-plane arc length per integer** (constant, NOT 1) |
| height law | `z` | `z_n = n` | **constant height law**: `Δz = 1` per integer `n` → `z = e^y` |
| radial growth | `g` | **`e^(mod q)`** | radial gap per **turn**; `mod = conductor` → **L-dependent** |
| base radius | — | `0` | pure spiral `r = b·θ`, starts at origin |

`g = e^(mod q)` is **not universal** — `e²` for `eta`, `e³` for `chi3`, `e⁴` for
`chi4`, … (the original "`e³`" was `e^(mod 3)`). Derived: `b = g/(2π) = e^(mod)/(2π)`.

```
arc(θ)   = ∫₀^θ b·sqrt(t²+1) dt                    (radial-plane Archimedean arc)
θ_n      = arc⁻¹(u · n)                            (solve numerically; Newton)
R_n      = b · θ_n                                  radius  (~√n; +e^(mod) per TURN)
z_n      = n                                        CONSTANT HEIGHT LAW (Δz=1 per integer n)
point_n  = ( R_n cos θ_n , R_n sin θ_n , z_n )       a real 3-D helix
phasors_per_turn(n)        = 2π·R_n / u             GEOMETRIC count (L-dep via e^(mod))
active_phasors_per_turn(n) = 2π·R_n/u · (φ(q)/q)    LIVE: only χ(n)≠0 actually spin
```

**Constant height law `z_n = n` (default, `align_z_to_ey=True`).** Every integer
slot rises by the same `Δz = 1` — **per integer `n`, not per phasor**: the neutral
bucket `χ(n)=0` carries no arrow but still occupies its slot and still ticks the
height. (Counting per *active* phasor instead would climb by `φ(q)/q` per integer
and land the resonance at `(φ(q)/q)·e^(γ_k)` — wrong by the active fraction.) Since
phasor `n` resonates at `y = ln n`, this puts `z_n = n = e^(yₙ)` — each integer at
the height of its own resonant frequency — and the **zeros land at `z = e^(γ_k)`**.
This holds for **ALL L-functions** (it rides on `spin = log n`, shared by every
Dirichlet series; only the arrows/zeros differ). The growing per-turn pitch
(`64.9, 181.8, 301.9, … ` for `chi3`) is the *same fact* seen per-turn: more
integers per turn × constant `Δz`. Setting `align_z_to_ey=False` reverts to
`z = p·θ/(2π) ~ √n = e^(y/2)` (constant pitch-per-turn instead).

**phasors-per-turn is L-function dependent TWO ways:**
1. **the radial gap is `e^(mod q)`**, so the *geometric* count scales with `e^(mod)`:
   at `n=1000` → `eta 297, chi3 489, chi4 803, chi5 1309, chi8 4664`.
2. **the neutral bucket `χ(n)=0`** drops the inactive integers, so the *live* count
   is `geometric · active_fraction`, `active_fraction = #{a:χ(a)≠0}/q`
   (`chi3 2⁄3, chi4 1⁄2, chi5 4⁄5, chi8 1⁄2, eta 1`):
   at `n=1000` → `eta 297, chi3 326, chi4 401, chi5 1047, chi8 2332`.

**Other forced geometric facts (checkable):**
- radius is **non-decaying** and grows as `√n`; radial gap per turn is the
  constant `e^(mod)` (`= 2πb`), so it differs by L-function.
- the geometric count grows with `n` (for `chi3`: ≈ `41, 489, 4909` at `n = 10,
  10³, 10⁵`), because the unit distance is constant arc length.
- the **radial-plane** step is exactly `u = π/3`; with `z_n = n` the per-phasor
  vertical step is a constant `Δz = 1`, so the full 3-D step is `√((π/3)²+1) ≈ 1.45`.

**Why the radius can grow while cancellation needs decay:** the decay lives in
the **arrow length** `n^(−σ)`, *transverse* to the helix — **not** in the radius.
This is the key. A helix that is *Archimedean (non-decaying) AND* whose own
radius does the cancelling is impossible (cancellation needs the net to return
to 0, i.e. radius → 0). Separating arrow-decay from radius-growth resolves it.

**Division of labor (both halves matter):**
- The **arrows** (magnitude, spin models) decide **WHICH** frequency `y` cancels
  → the value of `L`, the zeros `γ_k`. Carrier shape does not change `L`.
- The **carrier** (unit, pitch, growth) decides **WHERE** on the fiber each
  phasor and each cancellation sits → the fiber position of zero `k` is
  `u · e^(γ_k)`. Without the carrier there is no "height/position" at all.

---

## 3. Characters (how the ± channels are assigned)

`chi(n)` depends only on `n mod q`. Real (quadratic) characters give `±1/0`:

| name | q | values `[chi(0..q−1)]` | L-function |
|---|---|---|---|
| `chi3` | 3 | `[0, 1, −1]` | mod-3 odd |
| `chi4` | 4 | `[0, 1, 0, −1]` | Dirichlet beta |
| `chi5` | 5 | `[0, 1, −1, −1, 1]` | mod-5 even |
| `chi8` | 8 | `[0, 1, 0, −1, 0, −1, 0, 1]` | `(2/n)` |
| `eta`  | 2 | `g(n) = (−1)^(n+1)` (NOT a character) | `(1−2^(1−s))·ζ(s)` |

**`eta` = the principal / `chi1` / `ζ` case.** The trivial character `chi(n)=1`
has no `−` channel, so `Σ n^(−s)` diverges and never cancels. Replacing the sign
with the **alternation** `g(n) = (−1)^(n+1)` supplies the `±` channels and yields
the Dirichlet eta. On `Re s = ½` the factor `(1−2^(1−s))` never vanishes, so
**eta's zeros there are exactly the nontrivial zeros of `ζ`.**

**Reference L-value (for independent verification), via Hurwitz zeta:**
```
L(chi, s) = q^(−s) · Σ_{a=1}^{q−1} chi(a) · zeta(s, a/q)        (chi3/4/5/8)
L(eta, s) = (1 − 2^(1−s)) · zeta(s)                              (eta / ζ)
```

---

## 4. Verified results — zeros `γ_k` on `Re s = ½` and fiber heights `e^(γ_k)`

(Found by computation; reproduce per §7. Heights = resonant term `n* = e^(γ_k)`.)

| character | `γ₁, γ₂, γ₃, γ₄` | `e^(γ_k)` (cancellation heights) |
|---|---|---|
| `chi3` | 8.039737, 11.249206, 15.704619, 18.261997 | 3.10e3, 7.68e4, 6.61e6, 8.53e7 |
| `chi4` | 6.020949, 10.243770, 12.988098, 16.342607 | 4.12e2, 2.81e4, 4.37e5, 1.25e7 |
| `chi5` | 6.648453, 9.831444, 11.958846, 16.033821 | 7.72e2, 1.86e4, 1.56e5, 9.19e6 |
| `eta`/`ζ` | 14.134725, 21.022040, 25.010858, 30.424876 | 1.38e6, 1.35e9, 7.28e10, 1.64e13 |

The `eta` row are the first four **Riemann zeta nontrivial zeros**.

---

## 5. Minimal reference implementation (standalone, ~20 lines)

An agent can reproduce the cancellation with only numpy:

```python
import numpy as np
def chi3(n):            # the channel/sign
    r = n % 3
    return np.where(r==0, 0.0, np.where(r==1, 1.0, -1.0))
def S(y, N=2_000_000, sigma=0.5, chi=chi3):
    n = np.arange(1, N+1, dtype=np.float64)
    return np.sum(chi(n) * n**(-sigma) * np.exp(-1j*y*np.log(n)))

# cancels at a zero, not off it (values at N=2e6; they shrink ~ 0.667/√N):
print(abs(S(8.039737155681)))   # ≈ 0.0002   (chi3 gamma_1)
print(abs(S(9.5)))              # ≈ 1.25     (off a zero, O(1))
```

For `eta`/`ζ`: use `chi(n) = np.where(n%2==1, 1.0, -1.0)` and test
`y = 14.134725141734` → `|S| ≈ 0.0004` at `N=2e6`.

Convergence at a zero is slow (conditional): `|S_N| ≈ 0.667 / √N`, so the exact
magnitude depends on `N` (and fluctuates within that envelope). No finite `N`
gives exactly 0; it decays as `N^(−σ)`. The robust signal is the **contrast**:
`|S_N(γ_k)| → 0` while `|S_N(off)| = O(1)`. Off the zeros `S_N → L ≠ 0`.

---

## 6. Reference module and commands

`lfunction_phasor_bank.py` (Python 3, needs `numpy`; `mpmath` for analytic
ground truth). Key objects: `RealCharacter`, `EtaCoefficient`, `CHARACTERS`,
`PhasorBank` (the sum), `PhasorHelix` (the 3-D carrier + arrows),
`analytic_zeros` (independent zero finder), `REPRODUCTION` (constants).

```bash
python3 lfunction_phasor_bank.py --test                 # 12-check pressure suite (≈6 s)
python3 lfunction_phasor_bank.py --constants            # the constants block (JSON)
python3 lfunction_phasor_bank.py --char chi3 --N 200000 --sweep 0.5 20
python3 lfunction_phasor_bank.py --char eta  --N 300000 --sweep 12  26   # zeta zeros
```

```python
from lfunction_phasor_bank import PhasorHelix, PhasorBank, CHARACTERS, analytic_zeros
h = PhasorHelix(CHARACTERS["chi3"], sigma=0.5, N=200_000)
h.net(8.039737)          # ≈ 0  (a zero)
h.carrier_point()        # (N,3) array — the actual 3-D helix points
h.phasors_per_turn(10_000)   # grows with radius
analytic_zeros(CHARACTERS["chi3"], 0.5, 0.5, 20.0)   # independent ground truth
```

---

## 7. Independent verification recipe (don't trust the code)

For each character, an agent should confirm **two independent computations agree**:

1. **Analytic zeros** — define `L` from the Hurwitz/zeta formula in §3 (e.g.
   `mpmath`), scan `|L(½+it)|` for `t ∈ [0, T]`, refine local minima with a root
   finder. These are the ground-truth `γ_k`.
2. **Phasor cancellation** — independently, the truncated phasor sum `S(γ_k)`
   (from §5) should be small and shrinking as `N` grows, while `S(γ_k ± δ)` is
   `O(1)`. Specifically `|S_N(γ_k)| ≈ 0.667/√N`.
3. **Channel equality** — at a `γ_k`, the regularized lane values coincide:
   `q^(−s)·zeta(s, a₊/q) == q^(−s)·zeta(s, a₋/q)` (for `chi3`: `zeta(s,1/3)=zeta(s,2/3)`),
   i.e. `P = M`. Off a zero they differ by `|L| ≠ 0`.
4. **Geometry** — `PhasorHelix.net(y)` must equal the plain `PhasorBank.net(y)`
   for several `y` (the carrier shape must not change `L`); but two helices with
   different `pitch/unit/growth` give different `resonance_arc_position` (the
   carrier *does* fix the fiber position).

Expected from the bundled suite (`--test`): **all 12 checks PASS**, including
- `chi3, chi4` zeros recovered by the bank sweep,
- `P = M` at the zero (`|P−M| ≈ 1e-16`) and `P ≠ M` off it,
- lanes diverge `~√N` in lockstep (`|P−M| → 0`, `|P| → ∞`),
- helix radius grows, turn gap `= e³`, phasors/turn grows,
- arrow sum `== L` (`err = 0`), cancels at the zero (`~1e-3`) not off it.

---

## 8. Honest caveats (what is and isn't load-bearing)

- **Load-bearing:** the two arrow models `magnitude = n^(−σ)`, `spin = ln n`,
  and the character `chi(n)`. These determine `L` and its zeros. Using a wrong
  spin (e.g. the spiral's winding angle `~√n` instead of `ln n`) does NOT cancel.
- **Carrier (geometry):** `unit, pitch, growth, base` set the 3-D placement and
  the fiber positions / heights, but do **not** change `L`'s value. They are
  required to give the cancellation a *location* (`u·e^(γ_k)`), not to produce it.
- **No exact finite zero:** at `σ=½` the series is conditionally convergent;
  `|S_N| ~ 0.667/√N`, so a truncation is never exactly 0 — it has to be read as a
  shrinking dip. The *exact* zero is the `N→∞` limit (or the analytic value).
- **A single lane is meaningless:** each diverges `~√N`. Only `P − M` converges.
- **`σ` is pinned to `½`:** the nontrivial zeros live there; off the critical
  line there is nothing to cancel (and a different `σ` changes the decay rate).

---

## 9. Provenance

This is the phasor view of the statements formalized (no `sorry`, no `axiom`) in
`LFunctionPhasor.lean`: `phasorTerm`, `spin`/`spin_mul`, `phasorTerm_norm`,
bucket trichotomy, `character_block_sum_eq_zero` / bounded partial sums, the
strip-extension by Abel summation, and the eta mechanism (Section 10) for the
principal/`ζ` case. The Lean file proves the analytic facts; this model is their
geometric realization on a 3-D Archimedean helix.
```
