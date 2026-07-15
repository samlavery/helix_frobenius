import RequestProject.HodgeDial
import RequestProject.CarrierTowerSeparation
import RequestProject.ForcibleClosure

/-!
# The path to the carrier Hodge-terminus, assembled from compiled bricks

The companion paper defines a four-step path to the terminus.  This file assembles the three
structural steps out of machinery the codebase **already proves**, isolating each unproven
classical input as a single named hypothesis — exactly the discipline of
`symr_functoriality_cancellation` (which carries `PerronTauberian`) and `HodgeDial`
(which carries `Recognition`).  Nothing here is re-derived and nothing assumes its own
conclusion; the value, as with the GRH spine, is that the *architecture* is kernel-fixed.

* **Step 1 — finite generation.**  `FiniteSeparation T D` (silence through a finite depth `D`
  forces the class to zero) glues to `Exhaustive` (`pathStep1_exhaustive_of_finiteSeparation`).
  On the semisimple model this is a **theorem**: the moment tower separates at depth `m` by the
  Vandermonde determinant (`pathStep1_finiteSeparation_model`, the bounded form of
  `momentTower_detects`).  The general finite depth is the classical import
  (SL(2)-orbit theorem of Schmid + Saito admissibility of the polarized variation), never
  re-proved here.

* **Step 2 — necessary exact closure.**  `pathStep2_exactClosure` re-exports
  `ForcibleClosure.residual_forcible` in the terminus reading: an algebraic class, by
  admissibility, supplies two `ℝ`-independent closure directions at the common height
  (`hIndep`, the named GGK import), and then its multi-rail residual closes **exactly**
  (residue-free).  This is the "each harmonic compatible / vanishing passes through the common
  height" constraint.  Paired with the no-orphan quantization of `MassMeter.mass_meter`
  (freeze mass `∈ ℕ`), the closure is a finite, checkable condition.

* **Step 3 — retention, all grades.**  Falls out of Steps 1–2 plus the existing detection
  bricks.  The semisimple half is unconditional: `pathStep3_retention_of_finiteSeparation`
  composes Step 1 into `Retention` via `retention_of_exhaustive`.  The transcendental grades go
  through `grade_visible_of_nondegenerate` (`pathStep3_detectable_of_gradewise`): the Step-2
  exact closure furnishes the pairing's anisotropy, Beilinson–Bloch furnishes the regulator's
  faithfulness (the named import at grades `≥ 2`).

* **Terminus.**  `terminus_of_finiteSeparation_recognition` composes Step 1/3 with `Recognition`
  into `SourceExhaustion` through `hodge_of_retention_recognition`.  On the model
  (`model_terminus_of_recognition`) Step 1 is discharged, so the terminus needs recognition
  alone — the same reduction as `model_sourceExhaustion_of_recognition`, now routed through the
  named path steps.

This asserts no Hodge conjecture, no Beilinson–Bloch, no SL(2)-orbit finiteness; each is a named
hypothesis.  No `sorry`, no `axiom`.
-/

open scoped BigOperators
open Matrix

namespace CriticalLinePhasor.HodgeLedgerFiltration

variable {Z V : Type*} [Zero Z] [Zero V]

/-! ## Step 1 — finite generation -/

/-- **Finite separation** (Step-1 conclusion): a *finite* truncation depth `D` is faithful —
a class silent on every grade below `D` is zero.  "Finitely many grades decide every class."
The general finite `D` is the SL(2)-orbit / Saito-admissibility classical import; on the model
it is a theorem at `D = m` (below). -/
def FiniteSeparation (T : ℕ → Z → V) (D : ℕ) : Prop :=
  ∀ z : Z, (∀ d, d < D → T d z = 0) → z = 0

/-- **Step 1, the glue**: finite separation gives no-silent-layer.  Every nonzero class fires at
some grade (indeed within `[0, D)`), so the tower is `Exhaustive`. -/
theorem pathStep1_exhaustive_of_finiteSeparation {T : ℕ → Z → V} {D : ℕ}
    (hsep : FiniteSeparation T D) : Exhaustive T :=
  fun z hz => not_mem_radical_iff_detectable.mp
    (fun hmem => hz (hsep z (fun d _ => hmem d)))

/-- **Step 1, discharged on the semisimple model** (bounded Vandermonde).  The moment tower over
`m` distinct clock frequencies separates already at depth `m`: a state whose first `m` moments
all vanish is zero.  This is `momentTower_detects` with the sharp finite bound — the model is
finitely generated at depth equal to the number of frequencies. -/
theorem pathStep1_finiteSeparation_model {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) :
    FiniteSeparation (fun (d : ℕ) (c : Fin m → ℂ) => ∑ i, c i * (lam i) ^ d) m := by
  classical
  intro c hc
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
    rw [hval, Pi.zero_apply, ← hc (d : ℕ) d.isLt]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  by_contra hcne
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hcne, hmv⟩)

/-! ## Step 2 — necessary exact closure -/

/-- **Step 2, the necessary constraint**: an algebraic class closes exactly.  By admissibility
(the named import `hIndep`: the readout-preserving warp supplies two `ℝ`-independent directions
in the residual plane at the common height), *every* multi-rail residual `D` is forcible to zero
— residue-free closure, the "each harmonic compatible, vanishing at the common height"
constraint.  This is `ForcibleClosure.residual_forcible` in the terminus reading. -/
theorem pathStep2_exactClosure {u v : ℂ} (hIndep : LinearIndependent ℝ ![u, v]) (D : ℂ) :
    ∃ s t : ℝ, D + (s • u + t • v) = 0 :=
  ForcibleClosure.residual_forcible hIndep D

/-! ## Step 3 — retention, all grades -/

/-- **Step 3, semisimple half (unconditional given Step 1)**: finite separation gives retention.
The moment/semisimple layer retains with no further input. -/
theorem pathStep3_retention_of_finiteSeparation {D : HodgeDial Z} {Dep : ℕ}
    (hsep : FiniteSeparation D.T Dep) : Retention D :=
  retention_of_exhaustive (pathStep1_exhaustive_of_finiteSeparation hsep)

omit [Zero Z] in
/-- **Step 3, transcendental grades (via Step 2)**: at a grade `d` whose readout factors through
an *anisotropic* pairing `B` of a faithful regulator `reg`, a class of nonzero regulator fires at
`d`.  The Step-2 exact closure furnishes the anisotropy `hanis` (residue-free landing);
Beilinson–Bloch furnishes the regulator faithfulness `hreg` (the named import at grades `≥ 2`).
This is `grade_visible_of_nondegenerate` in the retention reading. -/
theorem pathStep3_detectable_of_gradewise {T : ℕ → Z → V} {d : ℕ} {W : Type*} [Zero W]
    (reg : Z → W) (B : W → W → V) (hfac : ∀ z, T d z = B (reg z) (reg z))
    (hanis : ∀ w : W, w ≠ 0 → B w w ≠ 0) {z : Z} (hreg : reg z ≠ 0) :
    Detectable T z :=
  ⟨d, grade_visible_of_nondegenerate reg B hfac hanis hreg⟩

/-! ## Terminus -/

/-- **The terminus, assembled**: finite separation (Step 1 ⇒ retention, Step 3) and recognition
give source exhaustion.  Every classical input is a named hypothesis; the composition is the
kernel-fixed architecture. -/
theorem terminus_of_finiteSeparation_recognition {D : HodgeDial Z} {Dep : ℕ}
    (hsep : FiniteSeparation D.T Dep) (hrec : Recognition D) : SourceExhaustion D :=
  hodge_of_retention_recognition (pathStep3_retention_of_finiteSeparation hsep) hrec

/-- **On the model, the terminus needs recognition alone** — Step 1 is discharged by the bounded
Vandermonde separation.  Same content as `model_sourceExhaustion_of_recognition`, now routed
through the named path steps. -/
theorem model_terminus_of_recognition {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) (Alg : (Fin m → ℂ) → Prop)
    (hrec : Recognition (modelDial lam Alg)) :
    SourceExhaustion (modelDial lam Alg) :=
  terminus_of_finiteSeparation_recognition
    (pathStep1_finiteSeparation_model lam hdistinct) hrec

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.pathStep1_finiteSeparation_model
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.pathStep2_exactClosure
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.terminus_of_finiteSeparation_recognition
