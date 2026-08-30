# C3 / IsHB long batch — 2026-08-24

Target: an unconditional Lean proof of RH via
`CriticalLinePhasor.XiStructure.rh_of_xiStructure_isHB` and its sole input
`IsHB CriticalLinePhasor.XiStructure.xiStructure`.

Registers below are exactly four: **COMPILED**, **OPEN**, **EQUIV**, **FAILED**.
Everything else (skeleton, attack table, paper map, commands, diff) follows them.

**Calibration notes governing this whole file.**
* A statement is called *proved* only with a compiler transcript or a cited source read
  at source. Numerics are labelled **evidence**, never proof.
* `L1(x) := Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0 for all real x` is **NOT** claimed here. See
  OPEN-1 and FAILED-6. An earlier draft of this session's prose called it
  "unconditional (Csordas–Varga 1988)"; that was a misattribution — CV 1988 Thm 2.1 is
  about the **kernel** (`hp_pencil.tex:1739-1741`), and CNV 1986 is about the
  **Maclaurin coefficients** (`hp_pencil.tex:1741-1744`). Neither is the pointwise
  statement. Corrected throughout.
* The single-crossing shape of `r ↦ S_60(r)` is **evidence** (11 quadrature points),
  not a theorem.

---

## COMPILED

All in `tmp/XiStructureSeatBridge.lean` (393 lines), compiled against the existing
`.lake` oleans. Not yet promoted into `RequestProject/` — see NOTE-A.

**Command (literal):**
```
lake env lean tmp/XiStructureSeatBridge.lean
```
**Exit code:** `0`. **Error count:** `0` (`grep -c 'error' tmp/bridge_compile.log` → `0`).
Two warnings only, both `push_neg has been deprecated` at `:235:4` and `:366:6`.

**Escape-hatch source scan (literal):**
```
rg -n -e 'axiom |sorry|admit|@\[implemented_by\]' tmp/XiStructureSeatBridge.lean
```
→ no output, exit status `1` (no match). Same command over `tmp/AxiomAuditC3.lean` →
no match.

**Literal axiom footprint** (from `tmp/bridge_compile.log`; every line reproduced):
```
'CriticalLinePhasor.XiStructure.norm_sub_lt_norm_add_iff_re_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiStructure.norm_sub_le_norm_add_iff_re_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiStructure.isHB_xiStructure_iff_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiStructure.isHB_xiStructure_iff_halfplane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiStructure.re_logDeriv_mul_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiStructure.re_mul_conj_pos_iff_re_logDeriv_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiStructure.seat_anchor_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiStructure.chart_conj_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiStructure.dominates_of_seat_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiStructure.xiStructure_dominates_of_deep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiStructure.seat_energy_conj_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiStructure.xiStructure_dominates_interior_rung' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CriticalLinePhasor.XiStructure.xiStructure_dominates_of_rh' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalLinePhasor.XiStructure.rh_iff_xiStructure_dominates' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All fourteen are **bucket A** (exactly `[propext, Classical.choice, Quot.sound]`).
No bucket B, no bucket C, in this file.

### C-1 `isHB_xiStructure_iff_halfplane` — `tmp/XiStructureSeatBridge.lean:94`
Hypotheses: none.
```
IsHB xiStructure ↔ ∀ s : ℂ, 1/2 < s.re →
  0 < (ZD.riemannXi s * (starRingEnd ℂ) (deriv ZD.riemannXi s)).re
```
Converts the de Branges **modulus** inequality into a **real-part sign condition**.
Proof = polarization `‖a+b‖²−‖a−b‖² = 4·Re(a·conj b)` (`Complex.normSq_add`,
`Complex.normSq_sub`) applied to the components read off by `xiStructure_Estar`
(`RequestProject/XiStructureFunction.lean:72`), plus the chart bijection
`z ↦ ½ − iz` from the open upper half plane onto `{Re s > ½}`.

### C-2 `rh_iff_xiStructure_dominates` — `tmp/XiStructureSeatBridge.lean:316`
Hypotheses: none.
```
(∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2)
  ↔ ∀ z : ℂ, 0 < z.im → ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖
```
**Strictly improves `rh_of_xiStructure_isHB`** (`RequestProject/XiStructureFunction.lean:109`),
which consumes the *strict* `IsHB`. The strict inequality is not needed: **non-strict
domination already gives RH**, and conversely. This shrinks the target hypothesis.
Converse runs through `SeatScalar.exists_seat_energy_neg`
(`RequestProject/SeatScalarCriterion.lean:386`); note the strictly negative seat value
itself forces `ξ ≠ 0` at the anchor, so no separate non-vanishing input is consumed.

### C-3 `xiStructure_dominates_interior_rung` — `tmp/XiStructureSeatBridge.lean:288`
Hypotheses: none.
```
∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, 0 < z.im → Real.exp 4 + 2 ≤ |z.re| →
  1/2 - c / Real.log (|z.re| + 1/2) ≤ z.im →
  ‖Estar xiStructure z‖ ≤ ‖xiStructure z‖
```
**Unconditional Hermite–Biehler domination inside the critical strip.** Transport of the
compiled `DVP.seat_interior_rung_one'` (`RequestProject/DVPSeatRungOne.lean:953`) through
the chart dictionary `w = −z`. This is the first statement in this repository giving a
*region* on which the HB hypothesis is discharged with no hypothesis; `DeBranges.lean:189-192`
previously recorded only "discharging `IsHB` unconditionally is RH and is neither assumed
nor proved here."

### C-4 `xiStructure_dominates_of_deep` — `tmp/XiStructureSeatBridge.lean:247`
Hypothesis: `1/2 < z.im`.
```
‖Estar xiStructure z‖ ≤ ‖xiStructure z‖
```
Unconditional domination outside the closed strip; transport of
`SeatScalar.seat_energy_nonneg_of_outside_strip` (`RequestProject/SeatScalarCriterion.lean:1004`).

### C-5 supporting, same file
`norm_sub_lt_norm_add_iff_re_pos` (:41), `norm_sub_le_norm_add_iff_re_nonneg` (:56),
`isHB_xiStructure_iff_chart` (:73), `chart_re` (:88), `re_logDeriv_mul_normSq` (:111),
`re_mul_conj_pos_iff_re_logDeriv_pos` (:123), `seat_anchor_chart` (:136),
`seat_anchor_im` (:142), `seat_anchor_eq_neg` (:171), `dominates_of_chart_zero` (:175),
`chart_conj_mem_iff` (:184), `dominates_of_seat_nonneg` (:200),
`seat_energy_conj_eq` (:270), `xiStructure_dominates_of_rh` (:302).

### C-6 Axiom bucket audit of every consumed declaration
File `tmp/AxiomAuditC3.lean`; command `lake env lean tmp/AxiomAuditC3.lean`; errors `0`.
**All 27 probed declarations are bucket A.** Probed:
`rh_of_xiStructure_isHB`, `xiStructure_Estar/_Acomp/_Bcomp`,
`DeBranges.Acomp_zero_im_eq_zero`, `norm_eq_imp_im_zero`, `hb_lower`,
`SeatScalar.seat_criterion_iff`, `seat_energy_identity`, `seat_energy_nonneg_of_online`,
`exists_seat_energy_neg`, `seat_energy_nonneg_of_outside_strip`,
`seat_energy_nonneg_of_depth`, `depth_criterion_iff`, `DVP.seat_energy_re_eq`,
`DVP.xi_logDeriv_one_sub_conj`, `DVP.seat_interior_rung_one'`,
`JKernel.jKernel_pairing_nonpos`, `jKernel_neg`, `phiEven_nonneg`,
`XiKernelBridge.riemannXiKernel_eq_psi_operator`,
`ThetaWronskianSuzukiGram.riemannXiKernel_pos`, `riemannXiKernel_neg`,
`ContourArgument.riemannXi_conj`, `DVP.deriv_xi_conj`, `DVP.deriv_xi_one_sub`,
`ZD.ZeroCount.riemannXi_one_sub`, `riemannXi_zero_of_mem_NontrivialZeros`.
**No bucket B and no bucket C anywhere in the consumed tree**, so there is no hidden
recursive target on this axis.

---

## OPEN

Smallest genuine holes only, with the literal next Lean text.

### OPEN-1 (THE SMALLEST ANALYTIC HOLE) — pointwise Laguerre sign for Ξ
`L1(x) := Ξ'(x)² − Ξ(x)Ξ''(x) ≥ 0` for all real `x`, where `Ξ(x) = ξ(½+ix)`.

**Why it is the smallest.** By the *proved* identity I5 (EQUIV-3) the target
`Khat(y,x) := −Im[Ξ'(x+iy)·conj Ξ(x+iy)]` satisfies `Khat(y,x) = y·L1(x) + O(y³)`.
So `L1 ≥ 0` is exactly the `y→0` boundary value of C3 — necessary for C3, hence
necessary for RH, and strictly weaker than C3 itself.

**Status here: NOT PROVED AND NO DISCHARGER LOCATED.**
* Repo search, 5 naming variants, all zero hits:
  `rg -n "laguerre_ineq|L1_nonneg|xi_laguerre|deriv_sq_sub|logDeriv_deriv_nonneg" RequestProject/`
  → `0 0 0 0 0`. `rg -l "Laguerre" RequestProject/` → only `JensenRungTwo.lean`, whose
  content (`:53-186`) is degree-two **Jensen polynomial** hyperbolicity in the
  coefficients `xiCentralCoeff`, not the pointwise function inequality.
* Source check of what `hp_pencil.tex` actually attributes: `:1739-1741` gives
  Csordas–Varga 1988 Thm 2.1 for the **kernel** hazard `−K'(u)/(2uK(u))`; `:1741-1744`
  gives CNV 1986 for the **Maclaurin coefficients**. Neither states `L1(Ξ)(x) ≥ 0` on ℝ.
* Evidence only: `L1(x) > 0` at `x = 0,2,5,9,14,20,30,60,100`
  (`tmp/att535_c3_exact_battery.py identities`).

**Literal next Lean declaration** (statement only; not attempted, would be `sorry`):
```lean
theorem xi_laguerre_nonneg (x : ℝ) :
    0 ≤ (deriv (fun v : ℝ => (ZD.riemannXi (1/2 + Complex.I * v)).re) x) ^ 2
      - (ZD.riemannXi (1/2 + Complex.I * x)).re
        * deriv (deriv (fun v : ℝ => (ZD.riemannXi (1/2 + Complex.I * v)).re)) x := by
  sorry
```

### OPEN-2 (THE SMALLEST PROOF-FACING ANALYTIC LEMMA for the monotone-weighted identity)
Requested explicitly. The identity `Khat(y,x) = 8 ∫₀^∞ g_y''(r) S_x(r) dr` with
`g_y(u) = u·sinh(2yu)` should **not** be attacked through integration by parts with
boundary terms at infinity. The smallest proof-facing form avoids them entirely: it is
**Fubini on the triangle `0 ≤ r ≤ u` plus Taylor with integral remainder**, since
`∫₀^u (u−r)·g''(r) dr = g(u) − g(0) − u·g'(0)`.

Stated abstractly (no `Ξ`, no zeros, no `y`), which is the right granularity:

```lean
theorem weighted_tail_primitive_identity
    (W g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0) (hg0' : deriv g 0 = 0)
    (hWint : IntegrableOn W (Set.Ioi (0 : ℝ)))
    (hprod : IntegrableOn (fun p : ℝ × ℝ => (p.2 - p.1) * deriv (deriv g) p.1 * W p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2}) :
    ∫ u in Set.Ioi (0 : ℝ), g u * W u
      = ∫ r in Set.Ioi (0 : ℝ),
          deriv (deriv g) r * ∫ u in Set.Ioi r, (u - r) * W u := by
  sorry
```

Two independent decompositions, both admissible as the first executable line:
* **(a) Fubini-first.** `rw [MeasureTheory.integral_integral_swap_of_hasCompactSupport]`
  — or, in the σ-finite form actually needed here,
  `MeasureTheory.integral_integral_swap hprod`, then discharge the inner integral by
  `intervalIntegral.integral_comp_smul_deriv` twice.
* **(b) Taylor-first.** `have hTaylor : ∀ u, 0 ≤ u → ∫ r in (0:ℝ)..u, (u - r) * deriv (deriv g) r = g u := ...`
  by `taylor_mean_remainder_integral` (Mathlib) specialised to `n = 1`, then substitute
  and swap.
Decomposition (b) is the one to try first: it isolates the only genuinely analytic step
into a named Mathlib lemma and leaves Fubini as bookkeeping.

**What this lemma does and does not buy.** It converts C3 into
`∀ y > 0, ∀ x, 0 ≤ ∫₀^∞ g_y''(r) S_x(r) dr`. It does **not** prove C3, and it is not
implied by `S_x(r) ≥ 0` (which is FALSE — FAILED-1).

### OPEN-3 — the target itself
`IsHB xiStructure`, equivalently (C-1) `0 < Re[ξ(s)·conj ξ'(s)]` on `Re s > ½`,
equivalently the seat sign condition. Compiled frontier: C-3 discharges it on
`|Re z| ≥ e⁴+2`, `Im z ≥ ½ − c/log(|Re z|+½)`. Residual region: the shallow channel
`0 < Im z < ½ − c/log(...)` plus the bounded box `|Re z| < e⁴+2`. This matches
`seat_criterion_split_iff` conjunct 2 exactly (`GOAL_HP_UNCONDITIONAL.md:340-342`).

### OPEN-4 — strictness
`xiStructure_isHB_of_rh : (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) → IsHB xiStructure`.
C-2 gives the non-strict version both ways; the strict forward direction additionally
needs `NontrivialZeros` nonempty (to make a sum of nonnegative terms strictly positive).
Repo search found upper-bound censuses (`stripZeroCountMult_*`,
`RequestProject/DVPExhaustion*.lean:224-227`) but no compiled existence witness. Not
load-bearing for RH: only C-2's already-compiled direction is used in the backward chain.

---

## EQUIV

Navigation reformulations. None of these is a stop; each moves the attack surface.

### EQUIV-1 `IsHB xiStructure ⟺ the seat sign condition` — **COMPILED as C-1 + C-2**
`E = ξ(½−iz) + ξ'(½−iz)` and `E* = ξ(½−iz) − ξ'(½−iz)` (`xiStructure_Estar`), so
`‖E*‖ < ‖E‖ ⟺ 0 < Re[A·conj P]`. Numerically audited against the Lean definitions
(att534 `audit`): `ξ(½−iz) = Ξ(z)` to `1.5e-33 / 5.9e-33 / 6.2e-32`, and
`ξ'(½−iz) = +i Ξ'(z)` to `0.0 / 1.9e-34 / 0.0` while the **opposite** sign misses by
`0.035 / 0.016 / 0.138` — confirming the sign that
`RequestProject/XiStructureFunction.lean:30-33` calls load-bearing.
Hence `E = Ξ + iΞ'`, `E* = Ξ − iΞ'`, and via `DVP.seat_energy_re_eq`
(`RequestProject/DVPSeatRealPart.lean:76`) the HB defect is the seat energy in the
chart `w = −z`. **The Hermite–Biehler hypothesis and the scalar seat are one object.**

### EQUIV-2 the Wigner transform pair (used, and independently checked)
`Ŵ_x(η) = G(η/2+x)·G(η/2−x)` with `G = Ξ/2` in the `Φ = P0` convention of
att530/att531. Checked by the two-route agreement in EQUIV-4.

### EQUIV-3 the target in three equal spellings — the `y`-DC
```
Khat(y,x) := −Im[Ξ'(x+iy)·conj Ξ(x+iy)]
           = Im[−Ξ'/Ξ]·|Ξ|²                     (att534 audit iii, rel 0.0 / 1.9e-31)
           = 8 ∫₀^∞ u·sinh(2yu)·W_x(u) du       (att534 audit iv, rel 1.1e-13)
Khat(y,x) = y·L1(x) + O(y³)                      (att535 identities, ratio → 1)
```
Verified `Khat(1e-3,x)/1e-3` vs `L1(x)`, ratio `1.000000045 … 1.000002151` across
`x = 0 … 100`, i.e. over **60 orders of magnitude** in the value (`0.0114` at `x=0` down
to `9.0e-61` at `x=100`); the residual `~4.5e-8` is exactly the predicted `O(y²)`.
Cross-check done **both** via Wigner integration and via the Ξ-derivative identity, with
**no division by Ξ** anywhere — so it is valid at Ξ-zeros.

### EQUIV-4 the second tail primitive in closed form — the corrected identity
```
S_x(r) = (1/2π) ∫₀^∞ [G(x)² − G(x+τ)G(x−τ)]·cos(2rτ)·τ^{-2} dτ            (form B)
       = (1/4π)·D̂_x(2r),   D_x(τ) := [G(x)² − G(x+τ)G(x−τ)]/τ²
```
so **global STP ⟺ `D_x` is a positive-definite function for every `x`**.
Derivation: `(|v|−c)_+ = |v| − c + (c−|v|)_+`, `|v| = (2/π)∫₀^∞(1−cos vτ)τ^{-2}dτ`,
`FT[(c−|v|)_+] = 2(1−cos cξ)/ξ²` (L¹, no regularisation), and
`∫₀^∞(1−cos 2rτ)τ^{-2}dτ = πr` cancels the two linear terms.
Consistency: `S_x'(0) = −G(x)²/2` (I6), checked to 0.26% at `x=0,2` — the residual being
the forward-difference `h/2·W_x(0)` term at `h=1e-3`, quantitatively as predicted.
`r = 0` validation against the independent Φ-plane checkpoints of att531:
rel `6.2e-5 / 1.3e-4 / 2.4e-4 / 4.2e-5 / 8.7e-5 / 2.4e-5` at `x = 0,2,5,9,14,20`
(att531 prints 4 significant figures, so this is checkpoint-limited).
`r > 0` validation: `1.6e-4` at `r=0.25`, `7.0e-6` at `r=0.5` (`x=2`).

### EQUIV-5 odd-order tail primitives are exact derivative expressions
`S^{(2m+1)}_x(0) = ½(−1)^m Ŵ_x^{(2m)}(0)/(2m)!`, needing no quadrature; `m=0` gives
`Ξ(x)²/8 ≥ 0` unconditionally, `m=1` gives `L1(x)/32` (OPEN-1). Cross-checked:
`S^{(3)}_x(0)` vs `L1(x)/32` agrees to rel `0.0 / 1.3e-36 / 0.0` at `x = 0,14,60` — two
independent computations (numerical 2nd derivative of `Ŵ` at 0; `Ξ`-derivatives).

### EQUIV-6 exact integral identity (I4)
`∫₀^∞ S_x(r) dr = D_x(0)/8 = L1(x)/32`, by Fourier inversion of `D̂_x` at `τ = 0`.
This is an **identity, proved by hand and numerically confirmed**; its *sign* is OPEN-1.

---

## FAILED

### FAILED-1 GLOBAL STP IS FALSE — `S_x(r) ≥ 0` does not hold
`S_60(0) = −6.102853678e-37 < 0`.
Reproduced **independently** of the reported tensor quadrature, by the Ξ-closed-form
route (EQUIV-4), agreeing with the reported `−6.102853677928e-37` to **13 digits**.
```
python3 tmp/att532_stp_xi_route.py point 60 0 50 150 5 0.5
  Xi(x)          = -2.9092748239358864396e-18
  Xi(x)^2        = 8.4638800011871830418e-36
  quad[0,T]      = -1.5394570091083774235e-35
  DC tail  (exact)= 5.6425866674581220278e-38
  AC tail  (bound)= 6.900472339e-97
  S_x(r)         = -6.1028536779278205914e-37
```
Second counterexample abscissa found on the sign scan: `S_88(0) = −7.063565766e-56`
(ratio to `Ξ(88)²`: `−0.0191`).
Scan command: `python3 tmp/att535_c3_exact_battery.py scan 30 0 100 2` →
`# NEGATIVE S_x(0) at x = [60.0, 88.0]` (51 abscissas).
**Consequence: global STP is FAILED and its nonnegativity is not formalized.**
It was a *sufficient*, strictly-stronger-than-RH condition; its falsity does not bear on
RH. `tmp/att531_stp.py` (double precision, `x ≤ 30`) could not have seen this: at `x=30`
its printed value `8.549e-17` is already at its own quadrature floor.

### FAILED-2 the pointwise route to STP is dead independently
`D_60(t) < 0` at `t = 2, 3, 8, 30` — quadrature-free, pointwise evaluation only:
`Ξ(62)·Ξ(58) = 1.1722e-34` against `Ξ(60)² = 8.4639e-36`, a **factor 13.8** violation of
the global log-concavity inequality `Ξ(x)² ≥ Ξ(x+t)Ξ(x−t)`. Control at `x=0` uniformly
positive at `t = 0.5, 2, 8, 30`. Command:
`python3 tmp/att535_c3_exact_battery.py defect`.

### FAILED-3 REJECTED IMPLEMENTATION — form (A0) of `S_x(r)` for `r > 0`
```
(A0)  S_x(r) =? (1/8π)∫₀^∞ [Ξ(x)² − Ξ(x+t)Ξ(x−t)·cos(2rt)] t^{-2} dt      -- WRONG
```
This is "cosine inside the bracket" **without** the linear term. It arises from applying a
bare Hadamard finite part to `FT[(|v|−c)_+] = −2cos(cξ)/ξ²` while assuming
`f.p.∫_ℝ ξ^{-2}dξ = 0`; that assumption drops a term `−c·G(x)²`. The correct
cosine-inside form is
```
(A1)  S_x(r) = (A0) − (r/8)·Ξ(x)²          and   (A1) ≡ (B)
```
**How it was caught:** (A0) was implemented first in `tmp/att532_stp_xi_route.py` and
cross-checked against the pre-existing independent direct-Φ checkpoints of
`tmp/att531_stp.py` at `x=2`: it missed by a factor **39** at `r=0.25` and **2.2e4** at
`r=0.5`. Re-implemented as (B) it agrees with the same checkpoints to `1.6e-4` and
`7.0e-6`. The file now carries an explicit `REJECTED FORM -- DO NOT USE FOR r > 0` block
(`tmp/att532_stp_xi_route.py:38-63`).
**Scope of the error:** at `r = 0` all three forms coincide (`cos 0 = 1`; the linear term
carries a factor `r`). **The `r = 0` counterexample of FAILED-1 is therefore unaffected**,
and no downstream output ever consumed an (A0) value at `r > 0` — the higher-tail
subcommand was written but never run under (A0).

### FAILED-4 over-resolved nested referee (att534 `adjudicate`) — terminated, no checkpoint
The first `S_referee` used `24 panels × 48 nodes` in `u` and `48 × 48` in `w` ⇒ ≈`2.65e6`
arbitrary-precision kernel evaluations **per point**. Killed after 600 s with no output.
Rewritten with a float64 vectorised referee, then superseded entirely: the adjudication
was settled from the existing att531 checkpoints (FAILED-3). **Design law recorded:** do
not build a nested arbitrary-precision referee when an existing checkpoint or an exact
identity decides the question.

### FAILED-5 `Φ ≥ 0` and even does NOT imply `L1 ≥ 0` — dead decomposition for OPEN-1
The tempting route "`Ξ` is the Fourier transform of a positive even kernel, hence the
Laguerre inequality" is refuted by an explicit two-line counterexample:
take `dμ = c·δ₀ + b(δ_a + δ_{−a})`, so `f(x) = c + 2b·cos(ax)` with `μ ≥ 0` and even.
Then `L1(f)(x) = 4a²b² + 2a²bc·cos(ax)`, which is negative at `cos(ax) = −1` whenever
`c > 2b` (e.g. `a=1, b=1, c=10` gives `4 − 20 = −16`). So positivity and evenness of the
kernel are not enough, and OPEN-1 genuinely needs more than `riemannXiKernel_pos`.

### FAILED-6 MISATTRIBUTION, corrected in this session
An earlier draft of this session's prose asserted "the `y→0` endpoint of C3 is the
Laguerre inequality, **which is unconditional** (Csordas–Varga 1988)". The *identity*
half is right (EQUIV-3, proved). The *unconditional* half was **wrong**: CV 1988 Thm 2.1
as cited at `hp_pencil.tex:1739-1741` is the **kernel** hazard statement, and CNV 1986 at
`:1741-1744` is about **Maclaurin coefficients**. Neither is `L1(Ξ)(x) ≥ 0` on ℝ.
Recorded as a failure of the novelty/absence discipline (CLAUDE.md rule 10, "abstracts
are not source"); the claim is retracted and the sign is now OPEN-1.

### FAILED-7 Γ-pole in the naive `ξ` spelling
`½·s·(s−1)·π^{−s/2}·Γ(s/2)·ζ(s)` raises `ValueError: gamma function pole` at `s = 0`,
reached in the margin scan at `z = 0 + i/2`. Replaced by the identical pole-free spelling
`π^{−s/2}·Γ(1+s/2)·(s−1)·ζ(s)` (using `½·s·Γ(s/2) = Γ(1+s/2)`), verified to agree at
`rel 0.0 / 0.0 / 2.5e-26 / 3.1e-26` and to give `ξ(0)=0.5`, `ξ(½)=0.4971207782`.

### FAILED-8 heat-flow deformation (attack 19) — INCOMPLETE, not a result
Only the `λ = 0` control row completed (`S^0_60(0) = −6.1030229e-37`, consistent with
FAILED-1 to 5 digits at coarser settings) before the run was stopped. **No conclusion is
drawn about `λ > 0`.** Recorded so the row is not mistaken for evidence.

---

## BACKWARD SKELETON (rule 11 — written from the last line backwards, every node tagged)

```
[TARGET]  ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2                              (RH)
   ↑ COMPILED  rh_of_xiStructure_isHB          RequestProject/XiStructureFunction.lean:109
[N1]  IsHB xiStructure                                                       EQUIV (=RH)
   ↑ COMPILED  C-2 rh_iff_xiStructure_dominates    tmp/XiStructureSeatBridge.lean:316
[N1'] ∀ Im z>0, ‖E* z‖ ≤ ‖E z‖   (NON-STRICT — weaker hypothesis suffices)   EQUIV (=RH)
   ↑ COMPILED  C-1 isHB_xiStructure_iff_halfplane   tmp/XiStructureSeatBridge.lean:94
[N2]  ∀ Re s > 1/2 : 0 ≤ Re[ξ(s)·conj ξ'(s)]                                 EQUIV (=RH)
   ↑ COMPILED  DVP.seat_energy_re_eq            RequestProject/DVPSeatRealPart.lean:76
[N3]  seat energy ≥ 0 at every admissible anchor                             EQUIV (=RH)
   |     ↑ COMPILED  seat_criterion_iff        RequestProject/SeatScalarCriterion.lean:702
   ├─[N3a] |Im w| > 1/2                        COMPILED (unconditional)  SeatScalarCriterion.lean:1004
   ├─[N3b] |Re w| ≥ e⁴+2, depth ≥ ½−c/log      COMPILED (unconditional)  DVPSeatRungOne.lean:953
   |        ⇒ C-3 xiStructure_dominates_interior_rung   tmp/XiStructureSeatBridge.lean:288
   └─[N3c] shallow channel + bounded box       OPEN-3  ← the residual region
[N4]  Khat(y,x) = −Im[Ξ'·conj Ξ] ≥ 0                                         EQUIV (=RH)
   ├─[N4a] y→0 boundary value:  L1(x) ≥ 0                          OPEN-1  ← smallest hole
   ├─[N4b] Khat = 8∫₀^∞ g_y''(r)·S_x(r) dr                         OPEN-2  ← smallest lemma
   |        (STRONGER-and-constructive candidate: exhibit the identity, not an estimate)
   └─[N4c] S_x(r) ≥ 0 pointwise (would suffice)                    FAILED-1  ✗ false
```

**Rule 11 guard, applied honestly.** Nodes N1–N4 are all `EQUIV`. The only nodes that are
not restatements are N3a/N3b (`COMPILED`, unconditional, region-valued) and N4b
(`STRONGER`-and-constructive: an identity to be *exhibited*, discharged by Fubini +
Taylor rather than by estimate). **This skeleton is therefore not yet a proof plan for
RH** — its live non-EQUIV content is one region-extension axis (N3b) and one identity
(N4b). Saying so is part of this session's output.

---

## 20-ROW CANDIDATE ATTACK TABLE (all executed unless marked)

| # | attack | instrument | disposition |
|---|---|---|---|
| 1 | tail primitives, orders 2–5, at `r=0` | att535 `tails` | **EXECUTED.** Only `n=2` negative at `x=60` (`−6.10e-37`); `n=1,3,5` positive at every tested `x`. Odd orders are exact `Ŵ`-derivatives (EQUIV-5) |
| 2 | signed cone decomposition of the test function | exact argument + rows of #1 | **EXECUTED (exact).** `(u−r)_+` is not in the cone spanned by `{u^{2m}}`; that non-smoothness at `u=r` is precisely why `n=2` fails where odd orders survive |
| 3 | sign map of `S_x(0)`, `x∈[0,100]` | att535 `scan 30 0 100 2` | **EXECUTED.** Exactly two negatives: `x=60`, `x=88`. Ratio `S/(L1/32) ∈ [−0.572, 10.55]` |
| 4 | `Khat` via the Ξ-derivative identity | att535 `khat` | **EXECUTED.** 190 grid points, `x∈[0,100]`, `y∈[1e-4,3]`: **zero negatives** |
| 5 | positive-definiteness of `K_y = −J_y` | att535 `khat`, normalised | **EXECUTED.** min `Khat/(y|Ξ|²) = 0.0456` at `x=0,y=3`. Positive control fires: at Ξ-zeros the ratio → `1/y²` exactly as predicted |
| 6 | `y→0` DC of the target | att535 `identities` | **EXECUTED.** `Khat/y → L1` verified over 60 decades, ratio `1.0000000–1.0000022`. **Sign of `L1` is OPEN-1, not proved** |
| 7 | exact theta-mode diagonal split | att536 `modes` | **EXECUTED.** Ground mode carries 99.97/99.96/99.94/99.77 % at `v=0,2,5,9` |
| 8 | quantitative diagonal domination | att536 `modes` | **EXECUTED.** Off-diagonal `|G_1−G_∞|/|G_∞|` = `3.5e-4 … 2.3e-3` away from zeros, but **0.647 at `v=14`** |
| 9 | single-mode control (`n=1` alone) | att536 `modes` | **EXECUTED, control REJECTED.** Signs of `D^{(1)}_3` and `D_3` agree at all `t`, but the mode fails to carry the object near a Ξ-zero — it misses exactly the structure the counterexample lives on (design law `weil-cell-probe-null`) |
| 10 | kernel moments + Hankel positive-definiteness | att535 `moments` | **EXECUTED.** `m_0 = 0.49712077818831 = ξ(½)` ✓; Cholesky OK for `n=2,3,4,5` — consistent with compiled `xiMomentMatrix_posDef` |
| 11 | Turán / `C_j` family | att535 `moments` | **EXECUTED.** `m_0m_4/m_2² = 2.791102858` (paper: 2.7911); `C_j` ratios `1.0748439, 1.0627437, 1.0543033, 1.0480505, 1.0432125, 1.0393451` vs paper `1.0748,1.0627,1.0543,1.0481,1.0432,1.0394` — **independent reproduction** |
| 12 | Jensen hyperbolicity at `n=0` | att535 `moments` | **EXECUTED.** `d=2,3,4` all-real roots (all negative), consistent with GORZ `d ≤ 8` |
| 13 | de Branges modulus inequality directly | att535 `margin` | **EXECUTED.** `‖E*‖/‖E‖ < 1` on the whole grid; `1−ratio = O(y)` (`9.24e-5, 9.24e-4, 9.20e-3` at `y=1e-3,1e-2,1e-1`) |
| 14 | margin structure / where it is thinnest | att535 `margin` | **EXECUTED.** Thinnest as `y→0`: the open content is the shallow channel, matching `seat_criterion_split_iff` conjunct 2 |
| 15 | IBP representation `∫gW = ∫g''S` | att534 `audit` (iv) + EQUIV-3 | **EXECUTED.** `Khat` via Wigner integration vs via the Ξ-derivative identity agree to **1.1e-13**, no division by Ξ |
| 16 | audited boundary terms | att535 `identities` (I6) | **EXECUTED.** `S_x'(0) = −Ξ(x)²/8` confirmed at `x=0,2` to 0.26% (= the forward-difference `h/2·W_x(0)` term). **Superseded by OPEN-2**, which removes boundary terms entirely via Fubini+Taylor |
| 17 | exhibit a positive-definite witness for `D_x` | att535 `defect` | **EXECUTED, NEGATIVE RESULT.** No such witness: `D_60` is not nonnegative (FAILED-2) |
| 18 | **construction route:** build the HB↔seat equivalence in Lean and transport the compiled positivity | `tmp/XiStructureSeatBridge.lean` | **EXECUTED — 14 theorems compiled, all bucket A.** C-1…C-5 |
| 19 | heat-flow (de Bruijn–Newman) deformation | att535 `lam` | **INCOMPLETE (FAILED-8).** Only the `λ=0` control completed; no conclusion drawn |
| 20 | renormalised / weighted repair of STP | att536 `profile` + att535 `scan` | **EXECUTED.** `S_60(r)` negative on `[0,~0.25]`, crosses in `(0.2,0.3]`, positive lobe peaks `+2.10e-36` at `r=0.7` (3.4× the negative lobe), `∫₀^∞S_60 = 1.067e-36`. Weight `g_y''(r)/g_y''(0)` is ≥1 and increasing (`1.00→1.77` at `y=0.3`), so it down-weights the negative lobe. **EVIDENCE ONLY** — 11 quadrature points, not a theorem |

---

## PAPER FILE:LINE MAP

| topic | anchor |
|---|---|
| Hypothesis (PSD) | `automorph/hp_pencil.tex:585` |
| conditional theorem (PSD ⇒ RH + census) | `automorph/hp_pencil.tex:583-612` |
| the seat, terminal defect | `automorph/hp_pencil.tex:613-640` |
| null-cone flow decomposition | `automorph/hp_pencil.tex:661` |
| cosine transport of the pair-fed flow | `automorph/hp_pencil.tex:702` |
| resonance necessity | `automorph/hp_pencil.tex:731` |
| scalar seat criterion `prop:scalarseat` | `automorph/hp_pencil.tex:1015` |
| Bombieri–Lagarias Laguerre-basis remark | `automorph/hp_pencil.tex:1074` |
| seat criterion split + certified channel | `automorph/hp_pencil.tex:1544-1600` |
| seat energy as `−Re[ξ'/ξ]/Im w` (sign condition) | `automorph/hp_pencil.tex:1655-1680` |
| ordered bank readout on `Re s > 0` | `automorph/hp_pencil.tex:1697-1719` |
| **theta-kernel Turán appendix** | `automorph/hp_pencil.tex:1720` |
| attribution: CV 1988 = **kernel** hazard | `automorph/hp_pencil.tex:1739-1741` |
| attribution: CNV 1986 = **Maclaurin coefficients** | `automorph/hp_pencil.tex:1741-1744` |
| GORZ `d ≤ 8`, Jensen at `n=0` is RH | `automorph/hp_pencil.tex:1747-1760` |
| PF∞/Schoenberg trap, explicitly spurious | `automorph/hp_pencil.tex:1761-1766` |
| compiled analytic layer / hazard gate / `C_j` | `automorph/hp_pencil.tex:1774-1836` |
| gate proved on `[1/4,∞)`; open on `(0,1/4]` | `automorph/hp_pencil.tex:1838-1880` |
| seat endpoint identification (v2) | `automorph/hp_pencil_v2.tex:538` |
| remaining analytic obligation (v2) | `automorph/hp_pencil_v2.tex:603` |
| `S(t)` scale mismatch / carrier register | `automorph/universal.tex:2438` |
| event count and phase registration | `automorph/universal.tex:3300` |
| exact prime–zero bridge | `automorph/universal.tex:3795` |
| Jensen disk count wire | `automorph/universal.tex:3648-3670` |
| de Branges conjugate-pair block, named | `automorph/universal.tex:5936` |
| formalization scope | `automorph/universal.tex:8442` |
| HP setup used by the companion | `automorph/grh_companion.tex:1384` |
| the two Gram operators | `automorph/grh_companion.tex:1225` |
| vanishing = focal alignment | `automorph/grh_companion.tex:1165` |
| Proof B: GRH under (HP-W) | `automorph/grh_companion.tex:1864` |

Reconciliation against `RH_LEDGER.md` (last entry **515**, 2026-08-21),
`BURNDOWN.md` (Sym^r proof map — not this axis),
`GOAL_HP_UNCONDITIONAL.md:338-342` (capstone state: `seat_criterion_split_iff`, two
conjuncts). **No paper claim was treated as compiled without a Lean check**; every
COMPILED row above carries its own transcript.

---

## EXACT COMMANDS

```
git status --short
lake env lean tmp/XiStructureSeatBridge.lean                      # exit 0, 0 errors
lake env lean tmp/AxiomAuditC3.lean                               # exit 0, 0 errors
rg -n -e 'axiom |sorry|admit|@\[implemented_by\]' tmp/XiStructureSeatBridge.lean   # no match, exit 1
rg -n -e 'axiom |sorry|admit|@\[implemented_by\]' tmp/AxiomAuditC3.lean            # no match, exit 1
rg -n "laguerre_ineq|L1_nonneg|xi_laguerre|deriv_sq_sub|logDeriv_deriv_nonneg" RequestProject/   # 0 hits
rg -l "Laguerre" RequestProject/                                  # JensenRungTwo.lean only
rg -n "seat_energy_re_eq" RequestProject/                         # DVPSeatRealPart.lean:76,119
rg -n "theorem seat_interior_rung_one" -A 25 RequestProject/DVPSeatRungOne.lean
rg -n "def feReflect" -A 3 RequestProject/FoliatedPolarization.lean
grep -n "riemannXiKernel_pos\|xiMomentMatrix_posDef" RequestProject/ThetaWronskianSuzukiGram.lean

python3 tmp/att531_stp.py                                         # pre-existing checkpoint
python3 tmp/att532_stp_xi_route.py validate
python3 tmp/att532_stp_xi_route.py point 60 0 50 150 5 0.5
python3 tmp/att534_stp_form_adjudication.py audit
python3 tmp/att535_c3_exact_battery.py identities
python3 tmp/att535_c3_exact_battery.py khat
python3 tmp/att535_c3_exact_battery.py defect
python3 tmp/att535_c3_exact_battery.py margin
python3 tmp/att535_c3_exact_battery.py tails
python3 tmp/att535_c3_exact_battery.py moments
python3 tmp/att535_c3_exact_battery.py scan 30 0 100 2
python3 tmp/att536_profile_modes.py profile
python3 tmp/att536_profile_modes.py modes
```

---

## GIT DIFF

```
$ git diff --stat
$ git diff
```
Both **empty**: no tracked file was modified. Nothing was committed, pushed, amended,
reset, checked out, cleaned, or discarded. All pre-existing changes preserved (the 13
untracked files present at session start are untouched).

```
$ git status --short
?? tmp/AxiomAuditC3.lean
?? tmp/XiStructureSeatBridge.lean
?? tmp/att532_stp_xi_route.py
?? tmp/att532_x60_convergence.txt
?? tmp/att533_c3_battery.py
?? tmp/att534_stp_form_adjudication.py
?? tmp/att535_c3_exact_battery.py
?? tmp/att535_out_khat_defect_margin.txt
?? tmp/att535_out_scan_lam.txt
?? tmp/att535_out_tails_moments.txt
?? tmp/att536_out.txt
?? tmp/att536_profile_modes.py
?? tmp/bridge_compile.log
```

**Reviewed new files** (all additive, all under `tmp/`):

| file | lines | review |
|---|---|---|
| `tmp/XiStructureSeatBridge.lean` | 393 | 14 theorems + 4 helper lemmas, 3 `#print axioms` sections. No `sorry`/`axiom`/`admit`/`implemented_by`. No `Prop`-valued hypothesis added to the fixed target signature: `rh_iff_xiStructure_dominates` and `isHB_xiStructure_iff_halfplane` are hypothesis-free; `xiStructure_dominates_interior_rung` is hypothesis-free (`∃ c`). Imports only modules already in the tree. |
| `tmp/AxiomAuditC3.lean` | 55 | `#print axioms` probes only, no definitions. |
| `tmp/att532_stp_xi_route.py` | 210 | Ξ-route closed form, implements **(B)**; carries the explicit `REJECTED FORM` block for (A0) at `:38-63`. |
| `tmp/att533_c3_battery.py` | 307 | **Superseded, never run to completion**; retained only because att535 documents its derivation lineage. Not a source of any claim in this ledger. |
| `tmp/att534_stp_form_adjudication.py` | 341 | Referees R1/R2 (R1 rewritten float64 after FAILED-4; the `adjudicate` sweep was NOT rerun) + the E/E*/Khat audit, which **was** run and is the source of EQUIV-1 and EQUIV-3. |
| `tmp/att535_c3_exact_battery.py` | 395 | Exact-identity-first battery; source of attacks 1,3,4,5,6,10,11,12,13,14,17. |
| `tmp/att536_profile_modes.py` | 177 | Source of attacks 7,8,9,20. |
| `*_out*.txt`, `bridge_compile.log` | — | Raw transcripts, reproducible from the commands above. |

**NOTE-A — promotion not performed.** `tmp/XiStructureSeatBridge.lean` is fully verified
against the real dependency oleans by `lake env lean`, but has **not** been moved into
`RequestProject/`. Promotion is a file move plus one `lake build`; it adds no new
external import. Left for explicit approval (CLAUDE.md ground rule 3), so the tracked
tree is byte-identical to the session start.

---

## WHAT THIS SESSION CHANGED, at exactly its proved strength

1. **The HB hypothesis and the scalar seat are the same object** — compiled, both
   directions, bucket A. The de Branges branch and the DVP/seat branch of this repository
   were being worked as two programmes; they are one.
2. **The strict `IsHB` hypothesis can be weakened to non-strict domination** without
   losing RH (C-2). The target hypothesis is strictly smaller than it was.
3. **A region of the upper half plane on which HB domination is unconditional**, reaching
   *inside* the critical strip (C-3), where `DeBranges.lean:189-192` previously recorded
   nothing proved.
4. **Global STP is false** — independently reproduced to 13 digits and extended to a
   second abscissa; not formalized, correctly.
5. **The `y→0` boundary value of C3 is exactly `L1(x)`** (proved identity), and the sign
   of `L1` is an *open* hole in this repository with no discharger — located, not assumed.
