# Verifying the Lean development matches `carrier_fiber.py`

This note records the cross-check requested ("read the Python implementation, understand
it, verify the Lean matches the Python"). It compares `carrier_fiber.py` (and its test
suite `test_carrier_fiber.py`) against the Lean sources under `RequestProject/`.

Toolchain unchanged: `lean-toolchain` is `leanprover/lean4:v4.31.0`.

## What the Python implements

`carrier_fiber.py` is a "character-agnostic finite carrier/fiber harness for the π/3 helix
model" with three layers:

1. **C1 cumulative cell-clock layer** — finite Dirichlet phasors with clock
   `exp(-i·(π/3)·T·log n)`, read with `T = γ/(π/3)`.
2. **Native carrier layer** — integer `n` on the pitch-1 helix with cell phase
   `exp(i·n·π/3)` (the `ζ₆` six-cell marker, exact in `ℤ[ζ₆]`).
3. **Continuous finite focal layer** — height `z` absorbs `floor(z)` integer slots.

The module also exposes the **analytic harmonic channels** that it explicitly labels
"Lean-aligned" (method `CarrierFiber.analytic_channels`), with `γ = (π/3)·T`:

```
Aχ(T) = Lχ(3/2 + i·(π/3)·T)
Bχ(T) = (π/3) · Lχ(1/2 + i·(π/3)·T)
```

and the diagonal harmonic pencil `H = [[A, B], [μA, λB]]`, `det H = (λ−μ)·A·B`,
`det Gram(H) = |det H|²`, with the focal/rank-drop marker = `A ≠ 0` (admissible) and `B = 0`.

The readout map is `γ ↦ z = exp(γ)`, so `log z = γ`, with `T = γ/(π/3)`.

## Point-by-point correspondence

| Concept | Python (`carrier_fiber.py`) | Lean (`RequestProject/…`) | Match |
|---|---|---|---|
| Cell unit | `UCELL = π/3` | `Ucell χ Z = π/3` (`HarmonicPencilCell`) | ✓ |
| Readout point | `γ ↦ z=exp(γ)`, point `1/2 + iγ` | `criticalReadout Z = reprPoint χ Z = 1/2 + i·log Z` (`GeometricPhasorClosure`, `HarmonicPencilCell`) | ✓ (`log z = γ`) |
| Unsigned channel `A` | `Aχ = Lχ(3/2 + iγ)` | `Achan χ Z = Lχ(3/2 + i·log Z)` | ✓ |
| Signed channel `B` | `Bχ = (π/3)·Lχ(1/2 + iγ)` | `Bchan = scalarClosure = Ucell·Phi = (π/3)·Lχ(1/2+i·log Z)` | ✓ |
| Admissibility | `admissible = (|A| > tol)`; `A ≠ 0` in abs.-conv. region | `Achan_ne_zero` (re = 3/2 > 1), `Admissible χ Z := Achan χ Z ≠ 0` | ✓ |
| Focal marker | `focal = admissible & (|B| < tol)` | `Bchan_zero_iff_L_zero`, rank-drop ⇔ `Φχ = 0` | ✓ |
| Harmonic pencil | `H=[[A,B],[μA,λB]]` | `harmonicPencil A B μ lam = !![A,B; μ*A, lam*B]` | ✓ |
| Pencil determinant | `det H = (λ−μ)·A·B` | `harmonicPencil_det : det = (lam−μ)*A*B` | ✓ |
| Gram | `Gram(H)=HᴴH`, `det = |det H|²` | `GramH = LhMatᴴ * LhMat`, PSD, `gramH_rank_drop_iff_L_zero` | ✓ |
| Pencil rank-drop ⇔ L-zero | numeric: `|detH|≈0 ⇔ |B|≈0` | `harmonic_pencil_det_zero_iff_L_zero` (needs `λ≠μ`, `A≠0`) | ✓ |
| Finite cell clock | `(π/3)·Σ χ(n)·n^(−1/2)·exp(−iγ·log n)` | `aTerm t n = (π/3)·n^(−1/2)·exp(−i·t·log n)`; `channel_diff` = `(π/3)·Σ readoutTerm` | ✓ |
| Abel limit of finite clock | `→ Bχ` | `channel_diff_tendsto → (π/3)·Φχ(Z)` | ✓ |
| Lane split | real character lanes `+1 / −1 / 0` | `Pchan` (`χ(n)=1`), `Mchan` (`χ(n)=−1`); hypothesis `hsign : χ(n) ∈ {1,−1,0}` | ✓ |
| Helix speed | `√(p²+r²+(2πr k)²)` | `speed p r k` (`ClosedForm`) | ✓ |
| Arclength | integral; closed form `(k/2)√(…)+((p²+r²)/(4πr))·arsinh(2πr k/√(p²+r²))` | `arclength` / `arclengthClosed`, `arclength_closed_form` | ✓ |
| Winding | solve `S(k)=n·π/3`, radius `r·k` | `windParameter`, `windIntegerSite`, `windIntegerSite_cyl_radius` (`AreaLaw`) | ✓ |
| Area law | `radius²/n → r·δ/π` | `carrierRadius_sq_div_tendsto → r·(π/3)/π` | ✓ |
| Unit gauge | `p=1, r=3, δ=π/3 ⇒ target = 1` | `windIntegerSite_radius_sq_tendsto_unit_gauge` (→ 1) | ✓ |
| Native cell spin | `exp(i·slot·π/3)`, `ζ₆` six-cell marker | `cellAngle n = (π/3)·n` carrier spin (`FocalEigenheight`) | ✓ |

### Notes on the two "carrier" geometries
The Python has two distinct geometric layers, and so does the Lean:
- the **simple linear cell spin** `exp(i·n·π/3)` (Python native phase) ↔ Lean
  `FocalEigenheight.cellAngle`/`carrierRadius` (linear placeholder spin used for the
  focal moments), and
- the **arclength-wound helix** `HelixSettings.point` ↔ Lean `AreaLaw.windIntegerSite`,
  whose emergent radius satisfies the same `radius²/n → r·δ/π` area law (unit gauge → 1).

These are deliberately separate layers in both sources; the names `carrierRadius` appear in
two Lean namespaces (`Focal` vs `Geometry`) for the two layers, mirroring the two Python
layers. This is a naming overlap, not a conflict.

## Independent numeric cross-checks (run here)

- `python3 carrier_fiber.py test` → all **11** unit tests pass, including
  `test_analytic_channels_match_lean_scaling` (the Lean-aligned `Aχ,Bχ`),
  `test_pitch_one_unit_gauge_area_law` (`radius²/n → 1`), and
  `test_harmonic_pencil_family_eta_crossings` (`det H = (λ−μ)AB`, Gram `= |det H|²`).
- `python3 carrier_fiber.py validate --mode analytic` on `eta_trivial` and `chi3`: at each
  reference zero `γ`, the Lean-aligned `|Bχ| ≈ 10⁻¹⁵ ≈ 0` while `|Aχ| = O(1) ≠ 0` and
  `|det H| ≈ 0`. This is exactly the content of the Lean theorems `Bchan_zero_iff_L_zero`,
  `Achan_ne_zero`, and `harmonic_pencil_det_zero_iff_L_zero`.

## Verdict

The Lean development faithfully matches the Python implementation. The core model — the
π/3 cell unit, the readout `1/2 + i·log Z`, the unsigned channel `Lχ(3/2+iγ)`, the signed
channel `(π/3)·Lχ(1/2+iγ)`, the diagonal pencil with `det = (λ−μ)AB` and Gram `|det|²`, the
admissible/focal rank-drop marker, the finite cell-clock partial sum and its Abel limit, the
real-character lane split, and the arclength helix with its unit-gauge area law — is encoded
in Lean with the same definitions and the same constants, and the numeric behaviour of the
Python "Lean-aligned" channels matches the proved Lean theorems. The Lean additionally proves
(unconditionally) the equivalences that the Python only checks numerically (e.g.
`Bchan = 0 ⇔ Lχ-zero`, `Achan ≠ 0`, pencil rank-drop ⇔ L-zero, area-law limit).
