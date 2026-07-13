import RequestProject.CarrierTowerSeparation

/-!
# The Jordan drift tower: drift is value-blind, jet-visible, and never silent

**The harmonization reading of extension data** (companion paper; instrument
`tmp/drift_observability.py`).  A pure epicycle stack -- commuting clocks at distinct
frequencies -- produces only rotation; *drift* is the first-order shear between layers, the
Jordan/extension part that semisimplification kills.  The measured law (drift dimensions
0--3, GL(2)/`ℚ` census): the value ladder is silent below the drift dimension and first
fires at exactly that harmonic, with the response amplitude the height-pairing volume.
This file proves the three structural halves of that law on the finite Jordan-2 model,
unconditionally:

* **the value channel is drift-blind** (`jordan_localFactor_driftBlind`,
  `drift_in_value_radical`): the local factor `det(1 - X·A)` and every trace power of the
  Jordan block `[[λ, δ], [0, λ]]` are independent of the drift `δ` -- "killed by
  semisimplification" as a theorem, so every pure drift lies in the `radical` of the value
  tower;
* **the jet channel reads drift, in the Gross--Zagier shape**
  (`jordan_pow`, `jetResponse_eq_weighted_moment`): the shear slot of the `d`-th power is
  exactly `d·λ^{d-1}·δ` -- the first-order response is the derivative-weighted moment of
  the drift amplitudes;
* **drift exhaustion** (`jetTower_radical_trivial`, `jetTower_exhaustive`): over finitely
  many *distinct* clock frequencies, a drift state silent at every jet level is zero --
  the jet tower is jointly faithful on drift, by the same Vandermonde separation as the
  semisimple theorem.  No silent drift, unconditionally, in the model.

**Scope, priced exactly.**  This closes the model half.  The arithmetic instance replaces
the abstract jet response by the N\'eron--Tate / Beilinson--Bloch height pairing on cycle
extension data; the identification is Gross--Zagier at grade one (theorem) and the
nondegeneracy of that pairing above grade one is the named open input -- the reduction of
exhaustion to gradewise nondegeneracy is already formalized
(`grade_visible_of_nondegenerate` in `HodgeLedgerFiltration`).  Nothing here assumes or
proves Beilinson--Bloch or the Hodge conjecture.  No `sorry`, no `axiom`.
-/

open scoped BigOperators
open Matrix

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The Jordan-2 drift block**: clock frequency `λ` with first-order shear `δ` -- the
minimal state a pure epicycle stack cannot produce. -/
def jordanBlock (lam del : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![lam, del; 0, lam]

/-- **Powers of the drift block**: the diagonal carries the pure rotation `λ^d`; the shear
slot carries exactly `d·λ^{d-1}·δ` -- the first-order (jet) response of the `d`-th tower
level to the drift. -/
theorem jordan_pow (lam del : ℂ) (d : ℕ) :
    (jordanBlock lam del) ^ d
      = !![lam ^ d, (d : ℂ) * lam ^ (d - 1) * del; 0, lam ^ d] := by
  induction d with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      have hpow : (n : ℂ) * (lam ^ (n - 1) * lam) = (n : ℂ) * lam ^ n := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · have h1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
          rw [← pow_succ, h1]
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [jordanBlock, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
      · simp only [jordanBlock, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.of_apply, Nat.add_sub_cancel]
        push_cast
        linear_combination del * hpow
      · simp [jordanBlock, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [jordanBlock, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- **The value channel is drift-blind (local factor)**: `det(1 - X·A)` of the drift block
is `(1 - Xλ)²`, independent of `δ` -- the local factor sees only the semisimplification. -/
theorem jordan_localFactor_driftBlind (lam del X : ℂ) :
    Matrix.det (1 - X • jordanBlock lam del) = (1 - X * lam) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [jordanBlock, Matrix.one_fin_two]
  ring

/-- **The value channel is drift-blind (trace tower)**: every trace power of the drift
block equals that of its semisimplification. -/
theorem jordan_trace_pow_driftBlind (lam del : ℂ) (d : ℕ) :
    Matrix.trace ((jordanBlock lam del) ^ d)
      = Matrix.trace ((jordanBlock lam 0) ^ d) := by
  simp only [jordan_pow]
  simp [Matrix.trace_fin_two]

/-- **Every pure drift lies in the radical of the value tower**: the difference readout of
the trace tower against the semisimplification vanishes at every level, for every drift --
"killed by semisimplification," in the house `radical`. -/
theorem drift_in_value_radical (lam : ℂ) (del : ℂ) :
    del ∈ radical (fun d (del' : ℂ) =>
      Matrix.trace ((jordanBlock lam del') ^ d)
        - Matrix.trace ((jordanBlock lam 0) ^ d)) := by
  rw [mem_radical]
  intro d
  rw [jordan_trace_pow_driftBlind]
  exact sub_self _

/-- **The jet response of a drift bank**: the shear slot of the `d`-th power, summed over
the sites -- what the derivative channel reads. -/
def jetResponse {m : ℕ} (lam del : Fin m → ℂ) (d : ℕ) : ℂ :=
  ∑ i, ((jordanBlock (lam i) (del i)) ^ d) 0 1

/-- **The Gross--Zagier shape**: the jet response is the derivative-weighted moment of the
drift amplitudes, `Σ_i d·λ_i^{d-1}·δ_i`. -/
theorem jetResponse_eq_weighted_moment {m : ℕ} (lam del : Fin m → ℂ) (d : ℕ) :
    jetResponse lam del d = ∑ i, (d : ℂ) * (lam i) ^ (d - 1) * del i := by
  unfold jetResponse
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [jordan_pow]
  simp

/-- **Drift exhaustion (the model Beilinson--Bloch analogue), unconditional**: over
distinct clock frequencies, a drift state silent at every jet level `d ≥ 1` is zero.  By
Vandermonde, exactly as the semisimple theorem. -/
theorem jetTower_radical_trivial {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) :
    ∀ del : Fin m → ℂ,
      del ∈ radical (fun d (del' : Fin m → ℂ) => jetResponse lam del' (d + 1)) →
      del = 0 := by
  intro del hdel
  apply momentTower_detects lam del hdistinct
  intro d
  have h := hdel d
  simp only [jetResponse_eq_weighted_moment] at h
  have hd1 : ((d : ℂ) + 1) ≠ 0 := by
    have h0 : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    push_cast at h0
    exact h0
  have hsum : ((d : ℂ) + 1) * ∑ i, del i * (lam i) ^ d
      = ∑ i, ((d + 1 : ℕ) : ℂ) * (lam i) ^ (d + 1 - 1) * del i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast [Nat.add_sub_cancel]
    ring
  have h2 : ((d : ℂ) + 1) * ∑ i, del i * (lam i) ^ d = 0 := by
    rw [hsum]
    exact h
  exact (mul_eq_zero.mp h2).resolve_left hd1

/-- **No silent drift**: the jet tower is `Exhaustive` on the drift bank -- every nonzero
drift fires at some finite jet level. -/
theorem jetTower_exhaustive {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) :
    Exhaustive (fun d (del : Fin m → ℂ) => jetResponse lam del (d + 1)) :=
  exhaustive_of_radical_trivial (jetTower_radical_trivial lam hdistinct)

/-! ## The drift pairing is positive definite (the model anisotropy theorem)

Beilinson--Bloch nondegeneracy above grade one asks whether the height pairing on drift
(extension) data can be isotropic.  On the model, the answer is a theorem: the jet-response
energy is positive definite, because a finite window of jet levels already separates drift
(Vandermonde).  The **retention reduction** below then converts the arithmetic instance into a
ledger statement: a pairing that factors through a definite carrier energy along an injective
ledger map is anisotropic -- so the open arithmetic content is exactly *ledger retention on
cycle drift* (no two distinct drifts share a full ledger), the same statement the
ledger-failure and observability instruments hunt. -/

/-- **Finite-window Vandermonde separation**: the first `m` moments already detect the
amplitude state -- vanishing for `d < m` forces `c = 0` (the `m x m` Vandermonde is
invertible; same proof as `momentTower_detects`, window form). -/
theorem momentTower_detects_window {m : ℕ} (lam : Fin m → ℂ) (c : Fin m → ℂ)
    (hdistinct : Function.Injective lam)
    (hmom : ∀ d < m, ∑ i, c i * (lam i) ^ d = 0) : c = 0 := by
  classical
  set M : Matrix (Fin m) (Fin m) ℂ := (Matrix.vandermonde lam)ᵀ with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_transpose, Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
    exact sub_ne_zero.mpr (hdistinct.ne (Finset.mem_Ioi.mp hj).ne')
  have hmv : M *ᵥ c = 0 := by
    funext d
    have hval : (M *ᵥ c) d = ∑ i, (lam i) ^ (d : ℕ) * c i := by
      simp only [hM, Matrix.mulVec, Matrix.transpose_apply, Matrix.vandermonde_apply]
      rfl
    rw [hval, Pi.zero_apply, ← hmom (d : ℕ) d.isLt]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  by_contra hc
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc, hmv⟩)

/-- A vanishing jet response at level `d+1` forces the `d`-th moment of the drift to vanish
(divide out the nonzero derivative weight `d+1`). -/
theorem moment_zero_of_jetResponse_zero {m : ℕ} (lam del : Fin m → ℂ) (d : ℕ)
    (h : jetResponse lam del (d + 1) = 0) : ∑ i, del i * (lam i) ^ d = 0 := by
  simp only [jetResponse_eq_weighted_moment] at h
  have hd1 : ((d : ℂ) + 1) ≠ 0 := by
    have h0 : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    push_cast at h0
    exact h0
  have hsum : ((d : ℂ) + 1) * ∑ i, del i * (lam i) ^ d
      = ∑ i, ((d + 1 : ℕ) : ℂ) * (lam i) ^ (d + 1 - 1) * del i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast [Nat.add_sub_cancel]
    ring
  have h2 : ((d : ℂ) + 1) * ∑ i, del i * (lam i) ^ d = 0 := by
    rw [hsum]; exact h
  exact (mul_eq_zero.mp h2).resolve_left hd1

/-- **The model anisotropy theorem**: the jet-response energy over the first `m` levels is
positive definite on drift -- a nonzero drift state has strictly positive energy,
unconditionally.  This is the model form of "the Beilinson--Bloch pairing is anisotropic on
extension data": in the model it is a Vandermonde fact, not a conjecture. -/
theorem driftPairing_posDef {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) {del : Fin m → ℂ} (hdel : del ≠ 0) :
    0 < ∑ d ∈ Finset.range m, ‖jetResponse lam del (d + 1)‖ ^ 2 := by
  have hnn : ∀ d ∈ Finset.range m, (0 : ℝ) ≤ ‖jetResponse lam del (d + 1)‖ ^ 2 :=
    fun d _ => sq_nonneg _
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0.symm
  apply hdel
  apply momentTower_detects_window lam del hdistinct
  intro d hd
  have hsq := hzero d (Finset.mem_range.mpr hd)
  have hJ : jetResponse lam del (d + 1) = 0 := by
    have hn : ‖jetResponse lam del (d + 1)‖ = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp hsq
    exact norm_eq_zero.mp hn
  exact moment_zero_of_jetResponse_zero lam del d hJ

/-- **The retention reduction** (the arithmetic-frontier isolator): a quadratic energy that
factors through a *definite* carrier energy along an injective ledger map is anisotropic.
Consequently the open content of Beilinson--Bloch nondegeneracy above grade one is exactly
**ledger retention on cycle drift** -- that the arithmetic ledger embedding never collides two
distinct drift states -- the same statement the ledger-failure and drift-observability
instruments test.  Nothing here proves that retention; it converts the height question into
the retention question, at the standard footprint. -/
theorem anisotropic_of_definite_factor {Z W : Type*} [Zero Z] [Zero W]
    (f : Z → W) (E : W → ℝ)
    (hE : ∀ w, w ≠ 0 → 0 < E w)
    (hf0 : f 0 = 0) (hinj : Function.Injective f)
    {z : Z} (hz : z ≠ 0) : 0 < E (f z) := by
  apply hE
  intro h
  exact hz (hinj (h.trans hf0.symm))

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.jordan_localFactor_driftBlind
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.drift_in_value_radical
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.jetResponse_eq_weighted_moment
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.jetTower_exhaustive
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.driftPairing_posDef
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.anisotropic_of_definite_factor
