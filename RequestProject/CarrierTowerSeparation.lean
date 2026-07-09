import Mathlib
import RequestProject.HodgeLedgerFiltration

/-!
# Carrier tower separation: the moment / symmetric-power tower is jointly faithful on the
  semisimple carrier state (unconditional)

The paper's *recursive symmetric-power tower* reads the Satake weight multiset of the carrier state by
its symmetric-power / moment coordinates.  This file proves, **unconditionally**, the strongest form of
the no-silent-layer statement that the structural (non-arithmetic) route actually supports:

  the moment tower `T_d(c) = Σ_i c_i λ_i^d` over finitely many **distinct** clock frequencies `λ_i`
  is a *jointly faithful* coordinate system on the amplitude state `c` — a Vandermonde/Newton fact —
  so the carrier radical of the moment tower is **trivial** (`R = 0`), i.e. every nonzero semisimple
  carrier state fires at some finite tower level.

This is the "finite structural source → faithful carrier state → complete retained record → tower
decomposition" route carried out where it genuinely closes: on the **finite duality-stable weight
fiber** (the *semisimple* carrier state).  It does **not** reach the extension / cycle classes of the
Hodge section: those are killed by semisimplification (the localPoly / L-factors depend only on the
weight multiset), so they lie in the radical of the *value* tower and are detected only by the leading
L-derivative (height / regulator), whose nonvanishing is the Beilinson–Bloch nondegeneracy conjecture.
That is the manuscript STOP; here we prove the positive semisimple half unconditionally.

No `sorry`, no `axiom`.
-/

open scoped BigOperators
open Matrix

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **Abstract skeleton (the preferred target).** If the whole tower, viewed as the single map
`z ↦ (d ↦ T d z)`, is injective and preserves `0`, the carrier radical is trivial. -/
theorem radical_trivial_of_tower_injective {Z V : Type*} [Zero V] [Zero Z] {T : ℕ → Z → V}
    (hT0 : ∀ d, T d 0 = 0)
    (hinj : Function.Injective (fun z : Z => fun d => T d z)) :
    ∀ z, z ∈ radical T → z = 0 := by
  intro z hz
  apply hinj
  funext d
  show T d z = T d 0
  rw [hz d, hT0 d]

/-- **Moment separation (Vandermonde).** For finitely many **distinct** clock frequencies `λ`, if
every moment `Σ_i c_i λ_i^d` vanishes then the amplitude vector `c` is zero. This is the concrete
joint-faithfulness of the symmetric-power / moment tower on a semisimple state. -/
theorem momentTower_detects {m : ℕ} (lam : Fin m → ℂ) (c : Fin m → ℂ)
    (hdistinct : Function.Injective lam)
    (hmom : ∀ d : ℕ, ∑ i, c i * (lam i) ^ d = 0) : c = 0 := by
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
    rw [hval, Pi.zero_apply, ← hmom (d : ℕ)]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  by_contra hc
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc, hmv⟩)

/-- The moment tower `T_d(c) = Σ_i c_i λ_i^d` for distinct frequencies has **trivial radical**. -/
theorem momentTower_radical_trivial {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) :
    ∀ c : Fin m → ℂ,
      c ∈ radical (fun (d : ℕ) (c : Fin m → ℂ) => ∑ i, c i * (lam i) ^ d) → c = 0 :=
  fun c hc => momentTower_detects lam c hdistinct (fun d => hc d)

/-- **No-silent-layer on the semisimple carrier state (unconditional).** Every nonzero amplitude state
fires at some finite moment level: the moment tower is `Exhaustive`. -/
theorem momentTower_exhaustive {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) :
    Exhaustive (fun (d : ℕ) (c : Fin m → ℂ) => ∑ i, c i * (lam i) ^ d) :=
  exhaustive_of_radical_trivial (momentTower_radical_trivial lam hdistinct)

end CriticalLinePhasor.HodgeLedgerFiltration
