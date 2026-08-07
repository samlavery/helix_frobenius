import RequestProject.Sym2CoefficientIdentification
import RequestProject.GlobalHelixCPSDualPair

/-!
# The local join: the CPS bank's Euler coefficient is the `Sym²` coefficient

The corpus computes the `Sym²` local data twice, from opposite directions:

* the **CPS bank** side takes `radialLocalEulerCoeff w k`, the complete-homogeneous sum
  `∑_{l₀+l₁+l₂ = k} w₀^{l₀} w₁^{l₁} w₂^{l₂}` over the rank-3 clock weights
  `symClockWeight 2 α · = (α², 1, α⁻²)`;
* the **Hecke-wire** side takes `Sym2Identification.sym2Coeff α k`, the same complete
  homogeneous written on the triangle `a + c ≤ k` with `b = k − a − c` implicit.

They are the same sum in two indexings, and this file proves it.  The content is the
bijection `l ↦ (l₀, l₂)` between the antidiagonal `finsuppAntidiag univ k` and the triangle
— injective because `l₁ = k − l₀ − l₂` is forced by the antidiagonal condition, surjective
by reading that formula backwards.

* `symClock_prod_eq_zpow` — the rank-3 clock product collapses to one power,
  `∏ᵢ (symClockWeight 2 α i)^{lᵢ} = α^{2(l₀ − l₂)}` (the middle weight is `1`);
* `mk3` — the inverse map, the finitely-supported `(a, k−a−c, c)`;
* `radialLocalEulerCoeff_symClock_eq_sym2Coeff` — **the join**.

This is the identification that lets the `Sym²` readout of `HeckeMultiplicativityWire`
(`sym2_readout`, `sym2_readout_gammaC`) be read as the prescribed CPS bank's completed
readout: both sides' local factors are now literally the same function.

No `axiom`, no `sorry`.
-/

open Finset

namespace CriticalLinePhasor.Sym2Join

open CriticalLinePhasor.GlobalHelix CriticalLinePhasor.Sym2Identification

/-- **The rank-3 clock product collapses.**  At the `Sym²` clock weights
`(α², 1, α⁻²)` the monomial `∏ᵢ wᵢ^{lᵢ}` is a single power, `α^{2(l₀ − l₂)}`: the middle
channel is trivial and the outer two are reciprocal. -/
theorem symClock_prod_eq_zpow (α : ℂ) (hα : α ≠ 0) (l : Fin 3 →₀ ℕ) :
    (∏ i : Fin 3, symClockWeight 2 α (i : ℕ) ^ l i)
      = α ^ (2 * ((l 0 : ℤ) - (l 2 : ℤ))) := by
  rw [Fin.prod_univ_three]
  unfold symClockWeight
  norm_num
  rw [zpow_mul, zpow_sub₀ (zpow_ne_zero 2 hα)]
  norm_cast

/-- The inverse of the bijection: the finitely-supported triple `(a, b, c)` on `Fin 3`. -/
noncomputable def mk3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a, b, c]

@[simp] theorem mk3_zero (a b c : ℕ) : mk3 a b c 0 = a := rfl
@[simp] theorem mk3_one (a b c : ℕ) : mk3 a b c 1 = b := rfl
@[simp] theorem mk3_two (a b c : ℕ) : mk3 a b c 2 = c := rfl

/-- **The local join**: the CPS bank's local Euler coefficient at the rank-3 `Sym²` clock
weights is the Hecke-wire's `Sym²` coefficient, for every `k`.

Both are the complete homogeneous symmetric function `h_k(α², 1, α⁻²)`; the proof is the
reindexing `l ↦ (l₀, l₂)` from the antidiagonal to the triangle, with `l₁ = k − l₀ − l₂`
recovering the inverse. -/
theorem radialLocalEulerCoeff_symClock_eq_sym2Coeff (α : ℂ) (hα : α ≠ 0) (k : ℕ) :
    radialLocalEulerCoeff (fun i : Fin 3 => symClockWeight 2 α (i : ℕ)) k
      = sym2Coeff α k := by
  unfold radialLocalEulerCoeff sym2Coeff
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun l => (⟨l 0, l 2⟩ : Σ _ : ℕ, ℕ))
    (fun p => mk3 p.1 (k - p.1 - p.2) p.2) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have h : l 0 + l 1 + l 2 = k := by simpa [Fin.sum_univ_three] using hl.1
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    simp only [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    simp only [Fin.sum_univ_three, mk3_zero, mk3_one, mk3_two]
    omega
  · intro l hl
    simp only [Finset.mem_finsuppAntidiag] at hl
    have h : l 0 + l 1 + l 2 = k := by simpa [Fin.sum_univ_three] using hl.1
    ext i
    fin_cases i
    · simp
    · simp; omega
    · simp
  · intro p _
    rfl
  · intro l _
    exact symClock_prod_eq_zpow α hα l

end CriticalLinePhasor.Sym2Join

#print axioms CriticalLinePhasor.Sym2Join.symClock_prod_eq_zpow
#print axioms CriticalLinePhasor.Sym2Join.radialLocalEulerCoeff_symClock_eq_sym2Coeff
