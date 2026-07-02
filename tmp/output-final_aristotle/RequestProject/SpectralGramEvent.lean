import RequestProject.SelfAdjointGeneratorReadout

/-!
# L-zero ⇒ spectral Gram event

This file records the requested implication

> a zero of the (spectral) `L`-function produces a **spectral Gram event**: a rank-drop of the
> harmonic cell Gram matrix `GramH χ Z μ lam` at a real source-height `Z` whose represented point is
> the zero,

phrased in exactly the requested form
```
DirichletCharacter.LFunction χ ρ = 0 → ∃ Z : ℝ, ρ = reprPoint χ Z ∧ (GramH χ Z μ lam).det = 0 .
```

`reprPoint χ Z = 1/2 + i·log Z` is the represented critical-line point of the source height `Z`
(`HarmonicCell.reprPoint`), and `GramH χ Z μ lam` is the Hermitian positive-semidefinite harmonic
cell Gram matrix (`HarmonicCell.GramH`); its rank-drop `det = 0` is the spectral Gram event.

**Unconditionality / honest scope.**  A real height's represented point always has `Re = 1/2`, so a
zero `ρ` can equal `reprPoint χ Z` for a real `Z` **only** when `Re ρ = 1/2`.  The implication is
therefore stated for zeros **on the critical line** (`hcrit : ρ.re = 1/2`); on that line it is a
genuine, fully **unconditional** theorem.  Dropping `hcrit` would assert that *every* zero is so
represented — i.e. that every zero lies on the critical line — which is GRH, and is deliberately
**not** assumed or proved here (consistent with the rest of the project).  The diagonal calibration
is required admissible (`hlam : lam ≠ μ`).

No `axiom`, no `sorry`.
-/

open Complex Filter Topology Matrix
open scoped BigOperators Real

namespace CriticalLinePhasor.HarmonicCell

open CriticalLinePhasor

variable {q : ℕ} [NeZero q]

/--
**L-zero ⇒ spectral Gram event.**

If the Dirichlet `L`-function vanishes at a critical-line point `ρ` (`Re ρ = 1/2`), then there is a
real source-height `Z` whose represented point is exactly `ρ` (`ρ = reprPoint χ Z`) and at which the
harmonic cell Gram matrix rank-drops (`(GramH χ Z μ lam).det = 0`) — the spectral Gram event.

The witness is `Z = exp (Im ρ) > 0`, so `reprPoint χ Z = 1/2 + i·Im ρ = ρ`, and the rank-drop is the
forward direction of `gramH_rank_drop_iff_L_zero`.
-/
theorem L_zero_imp_spectral_gram_event (χ : DirichletCharacter ℂ q) (ρ : ℂ) (μ lam : ℂ)
    (hlam : lam ≠ μ) (hcrit : ρ.re = 1 / 2)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ Z : ℝ, ρ = reprPoint χ Z ∧ (GramH χ Z μ lam).det = 0 := by
  refine ⟨Real.exp ρ.im, ?_, ?_⟩
  · have hlog : Real.log (Real.exp ρ.im) = ρ.im := Real.log_exp ρ.im
    rw [reprPoint, tauChi, hlog]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcrit]
    · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  · have hLrepr : DirichletCharacter.LFunction χ (reprPoint χ (Real.exp ρ.im)) = 0 := by
      have hlog : Real.log (Real.exp ρ.im) = ρ.im := Real.log_exp ρ.im
      have hpt : reprPoint χ (Real.exp ρ.im) = ρ := by
        rw [reprPoint, tauChi, hlog]
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcrit]
        · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [hpt]; exact hρ
    exact (gramH_rank_drop_iff_L_zero χ _ μ lam hlam).mpr hLrepr

/--
**Spectral form (via `Lspec`).**  The same event for the spectral `L`-function `Lspec χ`, which is
definitionally the analytic Dirichlet `L`-function (`SpectralFiber.Lspec`): a critical-line zero of
the spectral `L`-function produces a harmonic cell Gram rank-drop at the represented source height.
-/
theorem Lspec_zero_imp_spectral_gram_event (χ : DirichletCharacter ℂ q) (ρ : ℂ) (μ lam : ℂ)
    (hlam : lam ≠ μ) (hcrit : ρ.re = 1 / 2)
    (hρ : SpectralFiber.Lspec χ ρ = 0) :
    ∃ Z : ℝ, ρ = reprPoint χ Z ∧ (GramH χ Z μ lam).det = 0 :=
  L_zero_imp_spectral_gram_event χ ρ μ lam hlam hcrit hρ

end CriticalLinePhasor.HarmonicCell
