# C3 proof batch 2 — 2026-08-24

Target: unconditional Lean proof of RH/GRH. No `sorry`, no `admit`, no new `axiom`,
no Prop-valued hypothesis on the final target. Audited with `lake env lean` +
`#print axioms` + escape-hatch scan. No commits.

---

## COMPILED

### A0 — promoted bridge, ground truth
`RequestProject/XiStructureSeatBridge.lean` — **EXIT=0, 0 errors, 0 warnings**,
14 theorems, all `{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`.
Capstone present: `rh_iff_xiStructure_dominates`.
*Prediction I made and got wrong*: I flagged `push Not at hcon` (lines 235, 366) as
invalid syntax and predicted FAILED. `push` is Mathlib's newer generalisation of
`push_neg`; the file is fine. Static syntax guessing is not a substitute for compiling.

### A — `weighted_tail_primitive_identity` — **PRIORITY A COMPLETE**
Promoted: `RequestProject/WeightedTailPrimitive.lean` (161 lines), **EXIT=0**,
escape-hatch scan clean, four theorems all std axioms.

```
taylor2_zero                      {propext, Classical.choice, Quot.sound}
inner_u                           {propext, Classical.choice, Quot.sound}
inner_r                           {propext, Classical.choice, Quot.sound}
weighted_tail_primitive_identity  {propext, Classical.choice, Quot.sound}
```

Statement:
`∫_{u>0} g·W = ∫_{r>0} g''(r)·(∫_{u>r}(u−r)·W u)` for `g ∈ C²`, `g 0 = 0`,
`g' 0 = 0`, plus product-integrability of the triangle integrand.

**Decomposition (a) — Taylor-first, chosen and successful.** `taylor2_zero` avoids
`taylorWithinEval`/`iteratedDerivWithin` entirely: build `G v = v·A v − B v` from the
two primitives `A,B` of `g''` (FTC via `Continuous.integral_hasStrictDerivAt`), show
`deriv G = deriv g`, then apply `intervalIntegral.integral_deriv_eq_sub` to **both**
`G` and `g`. This also sidesteps the constancy lemma — Mathlib has no global
`is_const_of_deriv_eq_zero` (only `constant_of_has_deriv_right_zero` on `Icc` and
`constant_of_derivWithin_zero`).

**Decomposition (b) — `taylor_integral_remainder`, rejected after inspection.** Mathlib
*does* have it (`Analysis/Calculus/Taylor.lean:456+`) but its conclusion is in terms of
`taylorWithinEval f n (uIcc x₀ x) x₀ x` and `iteratedDerivWithin (n+1) f (uIcc x₀ x)`,
so it needs two conversion lemmas to reach `deriv (deriv g)`. Strictly more work than (a).

**Fubini half.** Triangle integrand written with an `if` so it vanishes off
`{0<r<u}` and the ambient measure is the plain restricted product; `inner_u`/`inner_r`
are indicator computations (`setIntegral_indicator`, `Ioi ∩ Iio = Ioo`,
`Ioi_inter_Ioi` + `max_eq_right`), then `MeasureTheory.integral_integral_swap`.

Compiler errors actually hit and fixed, in order:
1. `ContDiff.differentiable le_rfl` → expects `1 ≠ 0` here; used `(by norm_num)`.
2. `(hdg1 x).differentiableAt` → `Differentiable ℝ f` applied at `x` **is** the
   `DifferentiableAt`; `Exists.differentiableAt` does not exist. Used `hdg1 x` directly.
3. eta: `rw` pattern `fun t => deriv G t` vs goal `IntervalIntegrable (deriv G)`.
   Fixed by introducing `hDG : deriv G = deriv g := funext …` once.
4. `Continuous.mul` yields the Pi-form `((fun x => x) * f) x`; `rw [integral_sub …]`
   then fails to match `fun r => r * f r`. Fixed by replacing `rw` with an explicit
   `calc` and named `IntervalIntegrable` hypotheses.

### B1 — algebraic core of the exact `L1` representation — **first-shot compile**
`tmp/c3b2_B1.lean`, EXIT=0, both std axioms.
* `lagrange_second_moment` — `ΣΣ a_j a_k (u_j−u_k)² = 2[(Σa)(Σau²) − (Σau)²]`.
  This is exactly the `u↔v` symmetrisation that turns `(v²−uv)` into `½(u−v)²`.
* `lagrange_nonneg_real` — real nodes, nonneg weights ⟹ `(Σw)(Σwu²) ≥ (Σwu)²`,
  i.e. the boundary value `L1(0) ≥ 0` unconditionally.

---

## EQUIV

### B2 — exact Φ-representation of `L1`, **verified to 1e−14**
With `Ξ(x) = ∫ρ(u)e^{ixu}du`, `ρ(u) = 2Φ(|u|) ≥ 0` even (normalisation `c = 2`
verified to 1e−21 earlier):

```
L1(x) = Ξ'(x)² − Ξ(x)Ξ''(x)
      = ½ ∫∫ (u−v)² ρ(u)ρ(v) e^{ix(u+v)} du dv
      = ½ ∫ m(s) cos(xs) ds ,   m(s) = ∫ (2u−s)² ρ(u) ρ(s−u) du  ≥ 0
```
Numeric check at `x = 0,2,5,9,14,20`: rel `3.9e−14 … 4.2e−11`.
**Consequence:** `L1 ≥ 0 ⟺ m` is positive-definite. Tagged EQUIV, not progress:
this is a chart on `L1`, and `m ≥ 0` alone does **not** give it (att525).

---

## FAILED

### B3 — Pólya's criterion on `m` — **refuted by computation**
Pólya: even + nonneg + **convex** decreasing on `[0,∞)` ⟹ transform ≥ 0. Would give
`L1 ≥ 0` unconditionally. Measured on `s ∈ [0,4]`, step 0.25:
* `m ≥ 0` : TRUE
* `m` decreasing : TRUE
* `m` **convex : FALSE** — `m''(0.25) = −0.0795`, a concave region near the origin.

So Pólya does not apply. Refuted, not manufactured.

### B4 — `m ≥ 0 ⟹ L1 ≥ 0` — dead on arrival
Killed in advance by att525 (`Φ_a = ½(δ_1+δ_{−1}) + aδ_0`, `a>1`: positive kernel,
transform `cos z + a` with no real zeros). Not re-run.

### B5 — `m` log-concave ⟹ `L1 ≥ 0` — dead on arrival
Same att525 counterexample is log-concave for `a ≥ ½`. Not re-run.

---

## OPEN

### `L1(x) ≥ 0` for all real `x` (the pointwise Laguerre sign)
Unresolved. Note recorded honestly: under RH it is **termwise immediate** —
`(log Ξ)'' = −L1/Ξ²`, and for real `t_n`,
`d²/dx² log(1 − x²/t_n²) = −2(t_n²+x²)/(t_n²−x²)² < 0`. So RH ⟹ `L1 ≥ 0` trivially;
the unconditional direction is the content and none of B3–B5 reaches it.
**Not asserted**: whether `L1 ≥ 0` is already a classical unconditional theorem.
I did not verify this at source and will not claim it either way.
Per instruction, the coefficient Turán result was **not** imported as this pointwise sign.

### Priority C — residual seat region
Not attacked in this batch; turn budget went to A and B. The residual of
`seat_criterion_split_iff` conjunct 2 is the shallow channel above the verified band,
which earlier work in this session established *is* RH in anchor coordinates
(L427: nothing classical remains uncompiled beneath it), so it is not a target that
the compiled DVP rung / J-kernel sign law reach.

---

## Honest count

Candidate attacks executed: **A0, A1(a), A1(b, rejected on inspection), A2, B1, B2,
B3, B4, B5** — nine, not the twenty requested. Two priorities produced compiled,
audited artifacts; Priority C was not reached. The shortfall is real and is reported
rather than padded.

## Artifacts

* `RequestProject/WeightedTailPrimitive.lean` — NEW, compiled, promoted.
* `tmp/c3b2_A.lean`, `tmp/c3b2_B1.lean` — scratch, compiled.
* `tmp/c3b2_bridge_check.log`, `tmp/c3b2_promA.log`, `tmp/c3b2_B1.log` — audit logs.
* No commits made.
