import RequestProject.WeilDuality

/-!
# The duality package at every conductor: Dirichlet L-functions

The paper's pillar IV noted "Dirichlet-L instantiation via Mathlib's `completedLFunction`
is routine pending work."  This file makes that true.  For every primitive Dirichlet
character `χ` mod `N` the Weil-package duality transfers from `ζ`:

* `vanishing_dual_pair_dirichlet` — the pairing on the vanishing set: `Λ(1−ρ, χ) = 0 ⟺
  Λ(ρ, χ⁻¹) = 0` (helix ↔ antihelix across the DUAL character — for complex `χ` the
  strand pair genuinely swaps the character, as the two-strand ontology says).
* `jets_mul_iff` — the workhorse: a smooth factor nonvanishing at the point neither
  creates nor destroys jet-tower depth (Leibniz + strong induction).
* `dual_dimension_symmetry_dirichlet` — duality is a perfect pairing at every conductor:
  the jet towers of `Λ(·, χ)` at `1−ρ` and of `Λ(·, χ⁻¹)` at `ρ` die together to every
  depth `k`: `d_χ(1−ρ) = d_{χ⁻¹}(ρ)` for the census dimension.
* `dual_pair_det_one` needs no instantiation: it is chart algebra, character-free
  (`WeilDuality.dual_pair_det_one` already covers every conductor).
* `rootNumber_ne_zero_of_gaussSum` — nonvanishing of the FE constant reduced to the
  Gauss sum's (classical for primitive `χ`; Mathlib's `rootNumber` docstring records
  `|W(χ)| = 1`).  The duality theorems take `hW : rootNumber χ ≠ 0` explicitly so the
  arithmetic input stays visible.

No `sorry`, no `axiom` beyond the standard three.
-/

open Complex DirichletCharacter

namespace CriticalLinePhasor.DirichletDuality

variable {N : ℕ} [NeZero N]

/-- The FE prefactor `N^{s−1/2}` never vanishes. -/
theorem fe_prefactor_ne_zero (s : ℂ) : ((N : ℂ) ^ (s - 1 / 2)) ≠ 0 := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [Complex.cpow_def_of_ne_zero hN]
  exact Complex.exp_ne_zero _

/-- The root number is nonzero as soon as the Gauss sum is (it is the Gauss sum divided
by the nonzero `I^a` and `N^{1/2}`). -/
theorem rootNumber_ne_zero_of_gaussSum {χ : DirichletCharacter ℂ N}
    (h : gaussSum χ (ZMod.stdAddChar) ≠ 0) : rootNumber χ ≠ 0 := by
  classical
  unfold rootNumber
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h2 : ((N : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hN]
    exact Complex.exp_ne_zero _
  have h3 : (Complex.I) ^ (if χ.Even then 0 else 1) ≠ 0 :=
    pow_ne_zero _ Complex.I_ne_zero
  exact div_ne_zero (div_ne_zero h h3) h2

/-- **The duality pairing at every conductor**: for primitive `χ` with nonvanishing root
number, `Λ(·, χ)` vanishes at `1 − ρ` iff `Λ(·, χ⁻¹)` vanishes at `ρ`. -/
theorem vanishing_dual_pair_dirichlet {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ)
    (hW : rootNumber χ ≠ 0) (ρ : ℂ) :
    completedLFunction χ (1 - ρ) = 0 ↔ completedLFunction χ⁻¹ ρ = 0 := by
  rw [IsPrimitive.completedLFunction_one_sub hχ]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 (fe_prefactor_ne_zero ρ)
      · exact absurd h4 hW
    · exact h2
  · intro h
    rw [h, mul_zero]

/-- **Jet towers are blind to nonvanishing smooth factors** (Leibniz + strong
induction): if `f ρ ≠ 0`, the jets of `f·g` and of `g` at `ρ` vanish together to every
depth `k`. -/
theorem jets_mul_iff {f g : ℂ → ℂ} {ρ : ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (hf0 : f ρ ≠ 0) (k : ℕ) :
    (∀ j ≤ k, iteratedDeriv j (f * g) ρ = 0) ↔ (∀ j ≤ k, iteratedDeriv j g ρ = 0) := by
  constructor
  · intro h j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
        intro hjk
        have hfg := h j hjk
        rw [iteratedDeriv_mul (hf.contDiff.contDiffAt) (hg.contDiff.contDiffAt)] at hfg
        have hz : ∀ i ∈ Finset.range (j + 1), i ≠ 0 →
            (j.choose i : ℂ) * iteratedDeriv i f ρ * iteratedDeriv (j - i) g ρ = 0 := by
          intro i hi hne
          have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hipos : 0 < i := Nat.pos_of_ne_zero hne
          have hlt : j - i < j := Nat.sub_lt (lt_of_lt_of_le hipos hij) hipos
          rw [ih (j - i) hlt (le_trans (Nat.sub_le j i) hjk)]
          ring
        rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos j)) hz] at hfg
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
          Nat.sub_zero] at hfg
        exact (mul_eq_zero.mp hfg).resolve_left hf0
  · intro h j hjk
    rw [iteratedDeriv_mul (hf.contDiff.contDiffAt) (hg.contDiff.contDiffAt)]
    apply Finset.sum_eq_zero
    intro i _
    rw [h (j - i) (le_trans (Nat.sub_le j i) hjk)]
    ring

/-- **Duality is a perfect pairing at every conductor**: for primitive nontrivial `χ`
with nonvanishing root number, the jet towers of `Λ(·, χ)` at `1−ρ` and of `Λ(·, χ⁻¹)`
at `ρ` die together to every depth — the census dimension transfers across the pairing,
`d_χ(1−ρ) = d_{χ⁻¹}(ρ)`. -/
theorem dual_dimension_symmetry_dirichlet {χ : DirichletCharacter ℂ N}
    (hχ : IsPrimitive χ) (hχ1 : χ ≠ 1) (hW : rootNumber χ ≠ 0) (k : ℕ) (ρ : ℂ) :
    (∀ j ≤ k, iteratedDeriv j (completedLFunction χ) (1 - ρ) = 0)
      ↔ (∀ j ≤ k, iteratedDeriv j (completedLFunction χ⁻¹) ρ = 0) := by
  have hrefl : ∀ j : ℕ, iteratedDeriv j (fun z => completedLFunction χ (1 - z)) ρ
      = (-1 : ℂ) ^ j • iteratedDeriv j (completedLFunction χ) (1 - ρ) := fun j =>
    congrFun (iteratedDeriv_comp_const_sub (n := j) (f := completedLFunction χ) (s := 1)) ρ
  have hne : ∀ j : ℕ, ((-1 : ℂ) ^ j) ≠ 0 := fun j => pow_ne_zero _ (by norm_num)
  have hFE : (fun z => completedLFunction χ (1 - z))
      = (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * rootNumber χ) * completedLFunction χ⁻¹ := by
    funext z
    rw [Pi.mul_apply, IsPrimitive.completedLFunction_one_sub hχ]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hf : Differentiable ℂ (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * rootNumber χ) := by
    have hcp : (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2))
        = fun z => Complex.exp (Complex.log N * (z - 1 / 2)) := by
      funext z
      rw [Complex.cpow_def_of_ne_zero hN]
    apply Differentiable.mul_const
    rw [hcp]
    exact Complex.differentiable_exp.comp ((differentiable_id.sub_const _).const_mul _)
  have hg : Differentiable ℂ (completedLFunction χ⁻¹) :=
    differentiable_completedLFunction (by simpa [inv_eq_one] using hχ1)
  have hf0 : (fun z : ℂ => (N : ℂ) ^ (z - 1 / 2) * rootNumber χ) ρ ≠ 0 :=
    mul_ne_zero (fe_prefactor_ne_zero ρ) hW
  constructor
  · intro h
    refine (jets_mul_iff hf hg hf0 k).mp (fun j hj => ?_)
    rw [← hFE, hrefl j, h j hj, smul_zero]
  · intro h j hj
    have h2 := (jets_mul_iff hf hg hf0 k).mpr h j hj
    rw [← hFE, hrefl j] at h2
    exact (smul_eq_zero.mp h2).resolve_left (hne j)

end CriticalLinePhasor.DirichletDuality
