import Mathlib

/-!
# What symmetry of the native generator does to zero-eigenvectors (ledger 1221)

The area-measure dilation generator has the power function `x^{−ρ}` as a (generalized) eigenvector with
eigenvalue `i(ρ − ½)` (`AreaDilation.dilGen_power`). Suppose some inner-product space carries a SYMMETRIC
operator `T` with an eigenvector `v_ρ` for `i(ρ − ½)` for each zero `ρ`: the exhaustive Hilbert–Pólya
realization. Then:

* `inner_eq_zero_unless_reflect`: `⟪v_ρ, v_ρ'⟫ ≠ 0` forces `ρ' = 1 − conj ρ`. The reflection pairing comes out
  of symmetry; it is not put in through the functional equation.
* `re_eq_half_of_symmetric`: a nonzero eigenvector forces `Re ρ = ½`.

The second is the Hilbert–Pólya step. The open part is constructing such a `T` and `v_ρ` for EVERY
nontrivial zero without assuming where the zeros are.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SymPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Symmetry pairs each zero only with its reflection.** -/
theorem inner_eq_zero_unless_reflect (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) {ρ ρ' : ℂ} {v v' : E}
    (hv : T v = (I * (ρ - 1 / 2)) • v) (hv' : T v' = (I * (ρ' - 1 / 2)) • v')
    (hne : ρ' ≠ 1 - (starRingEnd ℂ) ρ) : inner ℂ v v' = 0 := by
  have h := hT v v'
  rw [hv, hv', inner_smul_left, inner_smul_right] at h
  have hfac : ((starRingEnd ℂ) (I * (ρ - 1 / 2)) - I * (ρ' - 1 / 2)) * inner ℂ v v' = 0 := by
    rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exfalso
    apply hne
    have h1 : (starRingEnd ℂ) (I * (ρ - 1 / 2)) = -I * ((starRingEnd ℂ) ρ - 1 / 2) := by
      simp [map_sub, map_mul, Complex.conj_I, map_ofNat]
    rw [h1] at h0
    have h2 : -I * ((starRingEnd ℂ) ρ - 1 / 2) - I * (ρ' - 1 / 2) =
        -I * ((starRingEnd ℂ) ρ + ρ' - 1) := by ring
    rw [h2, mul_eq_zero] at h0
    rcases h0 with h3 | h3
    · exact absurd h3 (by simp [Complex.I_ne_zero])
    · linear_combination h3
  · exact h0

/-- **The Hilbert–Pólya step**: a nonzero eigenvector of a symmetric operator for `i(ρ − ½)` has
`Re ρ = ½`. -/
theorem re_eq_half_of_symmetric (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) {ρ : ℂ} {v : E} (hv0 : v ≠ 0)
    (hv : T v = (I * (ρ - 1 / 2)) • v) : ρ.re = 1 / 2 := by
  by_contra hre
  have hne : ρ ≠ 1 - (starRingEnd ℂ) ρ := by
    intro h
    apply hre
    have := congrArg Complex.re h
    simp at this
    linarith
  have h0 := inner_eq_zero_unless_reflect T hT hv hv hne
  exact hv0 (inner_self_eq_zero.mp h0)

end CriticalLinePhasor.SymPair

end

#print axioms CriticalLinePhasor.SymPair.inner_eq_zero_unless_reflect
#print axioms CriticalLinePhasor.SymPair.re_eq_half_of_symmetric
