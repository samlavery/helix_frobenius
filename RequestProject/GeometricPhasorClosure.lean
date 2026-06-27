import RequestProject.CriticalLineBridge

/-!
# The Abel-grown π/3 geometric phasor closure function and the no-log-trap helix pencil

This file records, *cleanly and unambiguously*, the geometric/analytic dictionary requested,
and the **no-log-trap** helix-height pencil, on top of the already-proved analytic channel
`dirichlet_strip_tendsto_LFunction` (Abel/Dirichlet strip convergence) and the zero-packaging
bridge `CriticalLinePhasor.Bridge.criticalLine_phasor_closure_iff_L_zero`.

## The dictionary (three *distinct* objects)

* `n`  — integer source slot,
* `Z`  — geometric helix **closure height** (`> 0`); the pencil lives in `Z`,
* `t`  — analytic readout height, defined *only after closure* by `t = log Z`
  (`analyticHeight`),
* `s = 1/2 + i log Z` — critical-line readout (`criticalReadout`).

The **geometric phasor closure function** is the Abel/Dirichlet-summed continuation
`Φχ(Z) := Lχ(1/2 + i log Z)` (`Phi`); `Phi_phasor_partialSum_tendsto` shows its phasor partial
sums converge to it.  The **pencil readout** linearizes in `t = log Z`:
`Dχ(t) := Φχ(e^t) = Lχ(1/2 + i t)` (`Dpencil`).

## The exact π/3 cell carrier

`cell n := exp(i·π·n/3)` is the exact six-cell carrier (`cell_six_periodic`).  The cell-lifted
phasor multiplies each term by `cell n`; the **analytic readout projection** forgets the cell
factor (`readout_projection`), returning the cell-free sum whose Abel limit is `Φχ(Z)`.

## The no-log-trap helix-height pencil

The pencil is built **in the geometric height `Z`, never in `log n`**.  With the Abel-grown
height weight `w_n`, the six-cell residue indicator, the character `χ`, and the height moments
`(Z_n/N)^k` (`heightAtom n = n`), the finite helix/cell feature matrix `Q = helixFeature`
(`Matrix (Fin N) (Fin 6 × Fin m) ℂ`) carries **no `log n`**.  The pencil matrices are the Gram
forms
```
Bχ,N = Qᴴ Q          (metricB / helixMetricB)
Aχ,N = Qᴴ Z_N Q      (heightA / helixHeightA),   Z_N = diag(Z_1, …, Z_N).
```
We prove the positivity/real-rootedness mechanism the construction "earns automatically":

* `metricB_posSemidef`, `heightA_posSemidef` — `Bχ,N ≥ 0`, and `Aχ,N ≥ 0` since `Z_n ≥ 0`;
* `metricB_posDef` — `Bχ,N > 0` under column independence;
* `helix_eigenheight_real` / `helix_eigenheight_rayleigh` — every generalized eigenheight of a
  Hermitian / positive-definite pencil is **real** and a Rayleigh quotient
  `Z = ⟪v, A v⟫ / ⟪v, B v⟫`;
* `helix_pencil_det_zero_iff` — `det(Aχ,N − Z Bχ,N) = 0` iff there is an admissible closure
  eigenvector at height `Z`.

Only *after* finding `Z` does one read the analytic height `t = log Z`; the diagonal of the
height operator is `Z_n = n`, **not** `log n` (the no-log-trap design).

## The two-lane positive boundary pencil

Section 9 builds the requested two-lane form: the metric `B_N = diag(Q₊ᴴ Q₊, Q₋ᴴ Q₋)`
(`twoLaneB`, positive), and the Hermitian height operator `A_N = [[A₊, C],[Cᴴ, A₋]]` whose
off-diagonal coupling block `C = Q₊ᴴ diag(cell) Q₋` (`laneCouplingC`) carries the admissible π/3
lane closure.  Positivity, Hermiticity, real-rootedness, and the determinant ↔ closure-state
characterization are all proved (`twoLaneB_posDef`, `twoLaneHelixA_isHermitian`,
`twoLane_eigenheight_real`, `twoLane_pencil_det_zero_iff`).  Whether `det(A_N − Z B_N)` roots
actually satisfy `log Z ≈ L-zero ordinates` is the open calibration (see `HELIX_PENCIL_FINDINGS.md`
for a non-verified numerical probe); it is **not** asserted here.

## What is **not** claimed

The infinite/full identity `Dχ(Z) = det(Aχ − Z Bχ) = Cχ · Lχ(1/2 + i log Z)` — the assertion
that a self-adjoint helix pencil *reproduces* `Lχ` — is **not** proved here: under the requested
reading it is equivalent to the (open) Generalized Riemann Hypothesis; see `REVIEW.md` and
`ARISTOTLE_SUMMARY.md`.  It is recorded only as the conjectural target, not as a theorem.

Everything proved here is `Mathlib`-only and `sorry`/`axiom`-free.
-/

open Complex Filter Topology Matrix
open scoped BigOperators Real ComplexConjugate ComplexOrder

namespace CriticalLinePhasor.Geometric

open CriticalLinePhasor CriticalLinePhasor.LFunctionPhasor CriticalLinePhasor.Bridge

/-! ## 1. The geometric / analytic dictionary -/

/-- **Analytic zero height** `t = log Z` read off from the geometric closure height `Z`. -/
noncomputable def analyticHeight (Z : ℝ) : ℝ := Real.log Z

/-- **Critical-line readout** `s = 1/2 + i·log Z` attached to geometric height `Z`. -/
noncomputable def criticalReadout (Z : ℝ) : ℂ := (1 / 2 : ℂ) + (Real.log Z : ℂ) * I

/-- **The Abel-grown geometric phasor closure function** `Φχ(Z) = Lχ(1/2 + i log Z)`. -/
noncomputable def Phi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : ℝ) : ℂ :=
  DirichletCharacter.LFunction χ (criticalReadout Z)

/-- **The pencil readout** in the analytic variable `t = log Z`:
`Dχ(t) = Φχ(e^t) = Lχ(1/2 + i t)`. -/
noncomputable def Dpencil {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  Phi χ (Real.exp t)

/-- The readout has constant real part `1/2`: it lives on the critical line. -/
theorem criticalReadout_re (Z : ℝ) : (criticalReadout Z).re = 1 / 2 := by
  simp [criticalReadout, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-- The readout is never zero (its real part is `1/2`). -/
theorem criticalReadout_ne_zero (Z : ℝ) : criticalReadout Z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [criticalReadout_re] at this
  norm_num at this

/-- `t = log Z` is recovered from `Z`, and `Z = e^t` from `t`. -/
theorem analyticHeight_exp (t : ℝ) : analyticHeight (Real.exp t) = t := by
  simp [analyticHeight]

theorem exp_analyticHeight {Z : ℝ} (hZ : 0 < Z) : Real.exp (analyticHeight Z) = Z := by
  simp [analyticHeight, Real.exp_log hZ]

/-- `Φχ` is, by definition, the L-function value on the critical line. -/
theorem Phi_eq_L {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : ℝ) :
    Phi χ Z = DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (Real.log Z : ℂ) * I) := rfl

/-- The pencil readout equals the L-value at `1/2 + i t`. -/
theorem Dpencil_eq_L {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    Dpencil χ t = DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  unfold Dpencil
  rw [Phi_eq_L, Real.log_exp]

/-! ## 2. The phasor partial-sum bridge -/

/-- **The geometric phasor partial sums converge to `Φχ(Z)`.**  The `cpow` form: the
Abel/Dirichlet partial sums of `χ(n)·n^{-(1/2 + i log Z)}` tend to `Φχ(Z)`. -/
theorem Phi_cpow_partialSum_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (Z : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        χ (n : ZMod q) * (n : ℂ) ^ (-criticalReadout Z))
      atTop (nhds (Phi χ Z)) := by
  have hre : 0 < (criticalReadout Z).re := by rw [criticalReadout_re]; norm_num
  exact dirichlet_strip_tendsto_LFunction χ hχ hre

/-- **Per-term phasor identity.**  For `n ≥ 1`,
`n^{-(1/2 + i log Z)} = n^{-1/2}·exp(-(log Z · log n)·i)`. -/
theorem cpow_eq_phasor (Z : ℝ) (n : ℕ) (hn : 0 < n) :
    (n : ℂ) ^ (-criticalReadout Z)
      = (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(Real.log Z * Real.log n) * I) := by
  rw [criticalReadout]
  exact CriticalLinePhasor.cpow_critical_line (Real.log Z) n hn

/-- **The geometric phasor partial sums converge to `Φχ(Z)`** in the explicit phasor form
`χ(n)·n^{-1/2}·exp(-i·log Z·log n)`. -/
theorem Phi_phasor_partialSum_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (Z : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        χ (n : ZMod q) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          * Complex.exp (-(Real.log Z * Real.log n) * I))
      atTop (nhds (Phi χ Z)) := by
  have h := Phi_cpow_partialSum_tendsto χ hχ Z
  refine h.congr ?_
  intro N
  apply Finset.sum_congr rfl
  intro n _
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    have hz : (0 : ℂ) ^ (-criticalReadout Z) = 0 :=
      Complex.zero_cpow (neg_ne_zero.mpr (criticalReadout_ne_zero Z))
    simp only [Nat.cast_zero, hz, mul_zero]
    rw [Real.zero_rpow (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)]
    simp
  · rw [cpow_eq_phasor Z n hn0]; ring

/-! ## 3. The geometric zero condition -/

/-- **The geometric zero condition.**  `Φχ(Z) = 0` iff the phasor partial sums close (tend to
`0`).  In analytic form this is `Lχ(1/2 + i log Z) = 0`. -/
theorem Phi_zero_iff_closure {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : ℝ) :
    Phi χ Z = 0
    ↔ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        χ (n : ZMod q) * (n : ℂ) ^ (-((1 / 2 : ℂ) + (Real.log Z : ℂ) * I)))
        atTop (nhds 0) := by
  rw [Phi_eq_L]
  exact criticalLine_phasor_closure_iff_L_zero χ hχ (Real.log Z)

/-- **Geometric ⇔ analytic zero correspondence.**
`Lχ(1/2 + i t) = 0` iff `Φχ(e^t) = 0` (and `t = log Z`). -/
theorem L_zero_iff_Phi_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 ↔ Phi χ (Real.exp t) = 0 := by
  rw [Phi_eq_L, Real.log_exp]

/-! ## 4. The exact π/3 cell carrier -/

/-- **The π/3 cell coordinate** `cell n = exp(i·π·n/3)`. -/
noncomputable def cell (n : ℕ) : ℂ := Complex.exp (I * ((Real.pi / 3) * (n : ℝ)))

/-- **Exact six-cell closure**: `cell (n+6) = cell n`. -/
theorem cell_six_periodic (n : ℕ) : cell (n + 6) = cell n := by
  unfold cell
  have := CriticalLinePhasor.Bridge.pi_over_three_cell_periodic (n : ℝ)
  push_cast
  exact this

/-- The cell carrier has unit modulus. -/
theorem cell_norm (n : ℕ) : ‖cell n‖ = 1 := by
  unfold cell
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-! ## 5. The cell-lifted phasor and its analytic readout projection -/

/-- **The cell-lifted phasor term** `χ(n)·n^{-1/2}·exp(-i·log Z·log n)·cell n`. -/
noncomputable def cellLiftedTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : ℝ)
    (n : ℕ) : ℂ :=
  χ (n : ZMod q) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    * Complex.exp (-(Real.log Z * Real.log n) * I) * cell n

/-- **The analytic readout term** `χ(n)·n^{-1/2}·exp(-i·log Z·log n)`: the cell-lifted term with
the cell factor forgotten. -/
noncomputable def readoutTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : ℝ)
    (n : ℕ) : ℂ :=
  χ (n : ZMod q) * (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    * Complex.exp (-(Real.log Z * Real.log n) * I)

/-- **The readout projection forgets the cell factor.**  The cell-lifted term divided by the
(unit-modulus) cell carrier is exactly the readout term. -/
theorem readout_projection {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Z : ℝ) (n : ℕ) :
    cellLiftedTerm χ Z n / cell n = readoutTerm χ Z n := by
  have hcell : cell n ≠ 0 := by
    have := cell_norm n; intro h; rw [h] at this; simp at this
  unfold cellLiftedTerm readoutTerm
  field_simp

/-- **The projected readout closes to `Φχ(Z)`.**  The cell-free readout partial sums (the
projection of the cell-lifted phasor system) tend to `Φχ(Z) = Lχ(1/2 + i log Z)`. -/
theorem readout_partialSum_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (Z : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, readoutTerm χ Z n)
      atTop (nhds (Phi χ Z)) :=
  Phi_phasor_partialSum_tendsto χ hχ Z

/-! ## 6. The Gram height pencil: `B = Qᴴ Q`, `A = Qᴴ D Q`

The genuinely provable spectral content, stated for a general feature matrix `Q` (arbitrary
finite row/column index types) and a real diagonal height `D = diag d`.  The diagonal carries
the geometric heights `Z_n`, **not** `log n`. -/

/-- **The metric operator** `B = Qᴴ Q`. -/
noncomputable def metricB {ι κ : Type*} [Fintype ι] [Fintype κ] (Q : Matrix ι κ ℂ) :
    Matrix κ κ ℂ := Qᴴ * Q

/-- **The height operator** `A = Qᴴ · diag(d) · Q` with real diagonal heights `d`. -/
noncomputable def heightA {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Q : Matrix ι κ ℂ) (d : ι → ℝ) : Matrix κ κ ℂ :=
  Qᴴ * Matrix.diagonal (fun i => (d i : ℂ)) * Q

/-- `B = Qᴴ Q` is positive semidefinite (always). -/
theorem metricB_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ] (Q : Matrix ι κ ℂ) :
    (metricB Q).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self Q

/-- `B = Qᴴ Q` is positive definite when the columns of `Q` are independent, i.e. `Q.mulVec`
is injective (no nonzero feature vector lies in the kernel). -/
theorem metricB_posDef {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (Q : Matrix ι κ ℂ) (hQ : Function.Injective Q.mulVec) : (metricB Q).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self Q hQ

/-- `A = Qᴴ diag(d) Q` is positive semidefinite when all heights `d i ≥ 0` (here `Z_n = n ≥ 0`). -/
theorem heightA_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Q : Matrix ι κ ℂ) {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) : (heightA Q d).PosSemidef := by
  have hD : (Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hd i))
  exact hD.conjTranspose_mul_mul_same Q

/-- `A = Qᴴ diag(d) Q` is Hermitian. -/
theorem heightA_isHermitian {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Q : Matrix ι κ ℂ) {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) : (heightA Q d).IsHermitian :=
  (heightA_posSemidef Q hd).isHermitian

/-! ## 7. Real-rootedness of the generalized eigenheight -/

/-- The Hermitian form `qform M v = ⟪v, M v⟫`. -/
noncomputable def qform {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  star v ⬝ᵥ M.mulVec v

/-
**Reality of the generalized eigenheight.**  If `A` is Hermitian, `B` positive definite,
and `A v = μ • (B v)` for some `v ≠ 0`, then the eigenheight `μ` is real.  This is the
self-adjoint pencil's real-rootedness mechanism: `μ = ⟪v,Av⟫ / ⟪v,Bv⟫` with real numerator and
positive real denominator.
-/
theorem helix_eigenheight_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.PosDef) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (heig : A.mulVec v = μ • B.mulVec v) : μ.im = 0 := by
  have h_qA_real : star (star v ⬝ᵥ A.mulVec v) = star v ⬝ᵥ A.mulVec v := by
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ ← hA.apply ] ; simp +decide [ mul_left_comm ]
  have h_qB_real : 0 < (star v ⬝ᵥ B.mulVec v).re ∧ (star v ⬝ᵥ B.mulVec v).im = 0 := by
    convert hB.dotProduct_mulVec_pos hv using 1;
    rw [ Complex.lt_def ] ; aesop;
  simp_all +decide [ Complex.ext_iff ];
  nlinarith

/-
**Rayleigh-quotient form of the eigenheight.**  If `B` is positive definite and
`A v = μ • (B v)` for `v ≠ 0`, then `μ = ⟪v, A v⟫ / ⟪v, B v⟫` (no Hermiticity of `A` needed for
the quotient identity itself).
-/
theorem helix_eigenheight_rayleigh {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hB : B.PosDef) (μ : ℂ) (v : ι → ℂ) (hv : v ≠ 0)
    (heig : A.mulVec v = μ • B.mulVec v) : μ = qform A v / qform B v := by
  unfold qform;
  rw [ heig, dotProduct_smul ];
  rw [ smul_eq_mul, mul_div_cancel_right₀ _ ( by simpa using hB.dotProduct_mulVec_pos hv |> fun h => h.ne' ) ]

/-! ## 8. The concrete no-log-trap helix/cell feature matrix and pencil -/

/-- The exact harmonic cell unit `H = π/3`. -/
noncomputable def H : ℝ := Real.pi / 3

/-- **Abel-grown height weight** `w_n = n^{-1/2}·exp(-n/N)`. -/
noncomputable def helixWeight (N n : ℕ) : ℝ := (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-(n : ℝ) / N)

/-- **Geometric height atom** `Z_n = n` (the no-log-trap diagonal entry — *not* `log n`). -/
noncomputable def heightAtom (n : ℕ) : ℝ := (n : ℝ)

theorem heightAtom_nonneg (n : ℕ) : 0 ≤ heightAtom n := by
  unfold heightAtom; positivity

/-- **The finite helix/cell feature matrix** `Q : Matrix (Fin N) (Fin 6 × Fin m) ℂ`.
Row `i` is the integer slot `n = i+1`; column `(r,k)` is cell residue `r` and height moment `k`:
`q_{r,k}(n) = 1_{n mod 6 = r}·χ(n)·√(w_n)·(Z_n/N)^k`.  No `log n` appears. -/
noncomputable def helixFeature {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ) :
    Matrix (Fin N) (Fin 6 × Fin m) ℂ :=
  fun i rk =>
    (if (i.val + 1) % 6 = rk.1.val then (1 : ℂ) else 0)
      * χ ((i.val + 1 : ℕ) : ZMod q)
      * (Real.sqrt (helixWeight N (i.val + 1)) : ℂ)
      * (((heightAtom (i.val + 1) / N : ℝ)) : ℂ) ^ rk.2.val

/-- **The helix metric operator** `Bχ,N = Qᴴ Q`. -/
noncomputable def helixMetricB {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ) :
    Matrix (Fin 6 × Fin m) (Fin 6 × Fin m) ℂ :=
  metricB (helixFeature χ N m)

/-- **The helix height operator** `Aχ,N = Qᴴ Z_N Q` with `Z_N = diag(Z_1,…,Z_N)`, `Z_n = n`. -/
noncomputable def helixHeightA {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ) :
    Matrix (Fin 6 × Fin m) (Fin 6 × Fin m) ℂ :=
  heightA (helixFeature χ N m) (fun i => heightAtom (i.val + 1))

/-- `Bχ,N ≥ 0` (always). -/
theorem helixMetricB_posSemidef {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ) :
    (helixMetricB χ N m).PosSemidef :=
  metricB_posSemidef _

/-- `Bχ,N > 0` under column independence. -/
theorem helixMetricB_posDef {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ)
    (hQ : Function.Injective (helixFeature χ N m).mulVec) : (helixMetricB χ N m).PosDef :=
  metricB_posDef _ hQ

/-- `Aχ,N ≥ 0`: since the height atoms `Z_n = n ≥ 0`. -/
theorem helixHeightA_posSemidef {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ) :
    (helixHeightA χ N m).PosSemidef :=
  heightA_posSemidef _ (fun _ => heightAtom_nonneg _)

/-- `Aχ,N` is Hermitian. -/
theorem helixHeightA_isHermitian {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ) :
    (helixHeightA χ N m).IsHermitian :=
  (helixHeightA_posSemidef χ N m).isHermitian

/-- **The finite helix-height pencil determinant** `det(Aχ,N − Z Bχ,N)`. -/
noncomputable def helixPencilDet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ)
    (Z : ℝ) : ℂ :=
  (helixHeightA χ N m - (Z : ℂ) • helixMetricB χ N m).det

/-- **Closure-height characterization.**  `det(Aχ,N − Z Bχ,N) = 0` iff there is an admissible
closure eigenvector `v ≠ 0` at geometric height `Z`, i.e. `Aχ,N v = Z Bχ,N v`. -/
theorem helix_pencil_det_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ)
    (Z : ℝ) :
    helixPencilDet χ N m Z = 0
    ↔ ∃ v : Fin 6 × Fin m → ℂ, v ≠ 0 ∧
        (helixHeightA χ N m).mulVec v = (Z : ℂ) • (helixMetricB χ N m).mulVec v := by
  unfold helixPencilDet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun ⟨v, hv, hveq⟩ => ⟨v, hv, ?_⟩, fun ⟨v, hv, hveq⟩ => ⟨v, hv, ?_⟩⟩
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at hveq
    exact sub_eq_zero.mp hveq
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hveq, sub_self]

/-- **Real-rootedness of the helix closure heights.**  Any (complex) generalized eigenheight `μ`
of the self-adjoint, positive-definite helix pencil is real, provided the columns of `Q` are
independent (so `Bχ,N > 0`). -/
theorem helix_eigenheight_real_of_indep {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N m : ℕ)
    (hQ : Function.Injective (helixFeature χ N m).mulVec) (μ : ℂ) (v : Fin 6 × Fin m → ℂ)
    (hv : v ≠ 0)
    (heig : (helixHeightA χ N m).mulVec v = μ • (helixMetricB χ N m).mulVec v) : μ.im = 0 :=
  helix_eigenheight_real _ _ (helixHeightA_isHermitian χ N m) (helixMetricB_posDef χ N m hQ) μ v hv
    heig

/-! ## 9. The two-lane positive boundary pencil

Following the requested two-lane design: the positive/negative character lanes carry feature
matrices `Q₊, Q₋`, the **metric** is the block-diagonal positive form
`B_N = diag(Q₊ᴴ Q₊, Q₋ᴴ Q₋)`, and the **height operator** `A_N` is a Hermitian block matrix
```
A_N = ⎡ A₊   C  ⎤
      ⎣ Cᴴ   A₋ ⎦
```
whose **off-diagonal coupling block `C` carries the admissible π/3 lane closure**.  The metric is
realised as a Gram form of the stacked feature matrix `diag(Q₊, Q₋)`, so its positivity is
automatic; `A_N` is Hermitian; hence every generalized eigenheight is real. -/

/-- The **stacked two-lane feature matrix** `diag(Q₊, Q₋)`.  Its Gram form is the block-diagonal
two-lane metric. -/
noncomputable def stackedFeature {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) :
    Matrix (Fin N ⊕ Fin N) (Fin K₁ ⊕ Fin K₂) ℂ :=
  Matrix.fromBlocks Qp 0 0 Qm

/-- **The two-lane positive boundary metric** `B_N = diag(Q₊ᴴ Q₊, Q₋ᴴ Q₋)`. -/
noncomputable def twoLaneB {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) : Matrix (Fin K₁ ⊕ Fin K₂) (Fin K₁ ⊕ Fin K₂) ℂ :=
  metricB (stackedFeature Qp Qm)

/-- The two-lane metric is exactly the block-diagonal Gram form `diag(Q₊ᴴ Q₊, Q₋ᴴ Q₋)`. -/
theorem twoLaneB_eq_blockDiag {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) :
    twoLaneB Qp Qm = Matrix.fromBlocks (Qpᴴ * Qp) 0 0 (Qmᴴ * Qm) := by
  unfold twoLaneB metricB stackedFeature
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

/-- **The two-lane metric is positive semidefinite** (always). -/
theorem twoLaneB_posSemidef {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) : (twoLaneB Qp Qm).PosSemidef :=
  metricB_posSemidef _

/-- **The two-lane metric is positive definite** when the stacked lanes are column-independent. -/
theorem twoLaneB_posDef {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ)
    (hQ : Function.Injective (stackedFeature Qp Qm).mulVec) : (twoLaneB Qp Qm).PosDef :=
  metricB_posDef _ hQ

/-- **The two-lane height operator** `A_N = ⎡A₊ C; Cᴴ A₋⎤` with coupling block `C`. -/
noncomputable def twoLaneA {K₁ K₂ : ℕ} (Ap : Matrix (Fin K₁) (Fin K₁) ℂ)
    (Am : Matrix (Fin K₂) (Fin K₂) ℂ) (C : Matrix (Fin K₁) (Fin K₂) ℂ) :
    Matrix (Fin K₁ ⊕ Fin K₂) (Fin K₁ ⊕ Fin K₂) ℂ :=
  Matrix.fromBlocks Ap C Cᴴ Am

/-- **The two-lane height operator is Hermitian** when both lane blocks are Hermitian; the
coupling `C` / `Cᴴ` is self-adjoint as a block by construction. -/
theorem twoLaneA_isHermitian {K₁ K₂ : ℕ} {Ap : Matrix (Fin K₁) (Fin K₁) ℂ}
    {Am : Matrix (Fin K₂) (Fin K₂) ℂ} (C : Matrix (Fin K₁) (Fin K₂) ℂ)
    (hAp : Ap.IsHermitian) (hAm : Am.IsHermitian) : (twoLaneA Ap Am C).IsHermitian :=
  Matrix.IsHermitian.fromBlocks hAp rfl hAm

/-- **The π/3 lane-closure coupling block** `C = Q₊ᴴ · diag(cell) · Q₋`: the cell carrier couples
the positive and negative lanes through the exact six-cell phase. -/
noncomputable def laneCouplingC {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) : Matrix (Fin K₁) (Fin K₂) ℂ :=
  Qpᴴ * Matrix.diagonal (fun i : Fin N => cell (i.val + 1)) * Qm

/-- **The concrete two-lane helix height operator**: positive/negative height blocks coupled by
the π/3 lane-closure block `C = laneCouplingC`. -/
noncomputable def twoLaneHelixA {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) (d : Fin N → ℝ) :
    Matrix (Fin K₁ ⊕ Fin K₂) (Fin K₁ ⊕ Fin K₂) ℂ :=
  twoLaneA (heightA Qp d) (heightA Qm d) (laneCouplingC Qp Qm)

/-- The concrete two-lane helix height operator is Hermitian (heights `d ≥ 0`). -/
theorem twoLaneHelixA_isHermitian {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) {d : Fin N → ℝ} (hd : ∀ i, 0 ≤ d i) :
    (twoLaneHelixA Qp Qm d).IsHermitian :=
  twoLaneA_isHermitian _ (heightA_isHermitian Qp hd) (heightA_isHermitian Qm hd)

/-- **The two-lane boundary pencil determinant** `det(A_N − Z B_N)`. -/
noncomputable def twoLanePencilDet {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) (d : Fin N → ℝ) (Z : ℝ) : ℂ :=
  (twoLaneHelixA Qp Qm d - (Z : ℂ) • twoLaneB Qp Qm).det

/-- **Closure-height characterization for the two-lane pencil.**  `det(A_N − Z B_N) = 0` iff
there is a nonzero two-lane closure state `v` at height `Z` with `A_N v = Z B_N v`. -/
theorem twoLane_pencil_det_zero_iff {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) (d : Fin N → ℝ) (Z : ℝ) :
    twoLanePencilDet Qp Qm d Z = 0
    ↔ ∃ v : Fin K₁ ⊕ Fin K₂ → ℂ, v ≠ 0 ∧
        (twoLaneHelixA Qp Qm d).mulVec v = (Z : ℂ) • (twoLaneB Qp Qm).mulVec v := by
  unfold twoLanePencilDet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun ⟨v, hv, hveq⟩ => ⟨v, hv, ?_⟩, fun ⟨v, hv, hveq⟩ => ⟨v, hv, ?_⟩⟩
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec] at hveq
    exact sub_eq_zero.mp hveq
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hveq, sub_self]

/-- **Real-rootedness of the two-lane closure heights.**  Every generalized eigenheight of the
positive two-lane boundary pencil is real, provided the stacked lanes are column-independent (so
`B_N > 0`) and the heights `d ≥ 0` (so `A_N` is Hermitian).  Hence the analytic readout
`t = log Z` is real on the critical line. -/
theorem twoLane_eigenheight_real {N K₁ K₂ : ℕ} (Qp : Matrix (Fin N) (Fin K₁) ℂ)
    (Qm : Matrix (Fin N) (Fin K₂) ℂ) {d : Fin N → ℝ} (hd : ∀ i, 0 ≤ d i)
    (hQ : Function.Injective (stackedFeature Qp Qm).mulVec) (μ : ℂ) (v : Fin K₁ ⊕ Fin K₂ → ℂ)
    (hv : v ≠ 0)
    (heig : (twoLaneHelixA Qp Qm d).mulVec v = μ • (twoLaneB Qp Qm).mulVec v) : μ.im = 0 :=
  helix_eigenheight_real _ _ (twoLaneHelixA_isHermitian Qp Qm hd) (twoLaneB_posDef Qp Qm hQ) μ v hv
    heig

end CriticalLinePhasor.Geometric