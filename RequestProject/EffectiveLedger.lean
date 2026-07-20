import RequestProject.ArchitectureExactness

/-!
# The effective ledger: finite detection, sharp depth, and the radical computed

Three sharpenings of the retention corpus, each unconditional:

* **Detection closes at the bank size** (`momentTower_detects_within`,
  `firstVisibleDepth_lt`): a nonzero state on `m` distinct clocks fires within the first `m`
  moment readings — the infinite tower quantifier was never needed; the `m × m` Vandermonde
  block already separates.  Detection is finite-time with an explicit bound.

* **The bound is sharp** (`exists_maximally_hidden`): every bank of `m ≥ 1` distinct clocks
  carries a nonzero state silent through the first `m - 1` readings — a *maximally hidden
  state* — so the bank-size bound cannot be improved.  (Rank–nullity: the first `m - 1`
  moment functionals cannot separate `m` amplitudes.)

* **The carrier radical, computed exactly on arithmetic data**
  (`radical_coordinateTower_eq_torsion`): for the depth-one bundle of an elliptic curve the
  radical of the height-coordinate tower *is* the torsion subgroup — the paper's "identify
  `R`" question has its first exact arithmetic answer: `R = tors`, from the two cited
  classical inputs alone.  No `sorry`, no `axiom`.
-/

open scoped BigOperators
open Matrix

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-! ## Detection closes at the bank size -/

/-- **Effective Vandermonde separation**: the first `m` moments alone already detect — the
infinite tower was never needed. -/
theorem momentTower_detects_within {m : ℕ} (lam : Fin m → ℂ) (c : Fin m → ℂ)
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

/-- **The first-visible depth is bounded**: if silence through the first `m` levels forces the
class to be trivial for the purpose at hand, a detectable class is first visible strictly
below `m`. -/
theorem firstVisibleDepth_lt {Z V : Type*} [Zero V] {T : ℕ → Z → V} {z : Z}
    (h : Detectable T z) {m : ℕ} (hsep : ¬ ∀ d < m, T d z = 0) :
    firstVisibleDepth h < m := by
  by_contra hge
  push Not at hge
  exact hsep fun d hd =>
    (firstVisibleDepth_isFirstVisible h).1 d (lt_of_lt_of_le hd hge)

/-- **Detection closes at the bank size**: a nonzero state on `m` distinct clocks is first
visible strictly below level `m`. -/
theorem momentTower_firstVisible_lt {m : ℕ} (lam : Fin m → ℂ)
    (hdistinct : Function.Injective lam) {c : Fin m → ℂ} (hc : c ≠ 0)
    (h : Detectable (fun d c => ∑ i, c i * (lam i) ^ d) c) :
    firstVisibleDepth h < m :=
  firstVisibleDepth_lt h fun hsil =>
    hc (momentTower_detects_within lam c hdistinct hsil)

/-! ## The bound is sharp: the maximally hidden state -/

/-- **Every bank hides a maximally deep state**: for `m ≥ 1` there is a nonzero state silent
through the first `m - 1` moment readings.  The bank-size detection bound is exact. -/
theorem exists_maximally_hidden {m : ℕ} (hm : 1 ≤ m) (lam : Fin m → ℂ) :
    ∃ c : Fin m → ℂ, c ≠ 0 ∧ ∀ d < m - 1, ∑ i, c i * (lam i) ^ d = 0 := by
  classical
  set f : (Fin m → ℂ) →ₗ[ℂ] (Fin (m - 1) → ℂ) :=
    { toFun := fun c => fun d => ∑ i, c i * (lam i) ^ (d : ℕ)
      map_add' := by
        intro a b
        funext d
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        funext d
        simp [Finset.mul_sum, mul_assoc] } with hf
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_pi, Fintype.card_fin] at hle
    omega
  obtain ⟨c, hcmem, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨c, hc0, fun d hd => ?_⟩
  have hzero : ∑ i, c i * (lam i) ^ d = 0 :=
    congrFun (LinearMap.mem_ker.mp hcmem) ⟨d, hd⟩
  exact hzero

/-! ## The carrier radical, computed exactly on the arithmetic rung -/

/-- **The carrier radical of the depth-one height tower is the torsion subgroup.**  The paper's
central retention question — *identify `R = ⋂ ker T_d`* — has its first exact arithmetic
answer: for the point group of an elliptic curve under the cited Mordell–Weil/Néron–Tate
bundle, `R = tors`, on the nose.  Torsion is invisible to the height channel
(`pairing_torsion_right`) and nothing else is (`faithful_mod_torsion`). -/
theorem radical_coordinateTower_eq_torsion {P : Type*} [AddCommGroup P]
    (D : DepthOneHeightData P) :
    radical D.coordinateTower = {p : P | IsOfFinAddOrder p} := by
  ext p
  constructor
  · intro hp
    refine D.faithful_mod_torsion fun i => ?_
    have h := hp i.val
    simp only [DepthOneHeightData.coordinateTower, i.isLt, dif_pos, Fin.eta] at h
    exact_mod_cast h
  · intro ht d
    show D.coordinateTower d p = 0
    by_cases hd : d < D.rank
    · simp only [DepthOneHeightData.coordinateTower, dif_pos hd]
      rw [D.pairing_symm, D.pairing_torsion_right ht, Complex.ofReal_zero]
    · simp only [DepthOneHeightData.coordinateTower, dif_neg hd]

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.momentTower_detects_within
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.momentTower_firstVisible_lt
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.exists_maximally_hidden
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.radical_coordinateTower_eq_torsion
