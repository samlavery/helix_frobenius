import RequestProject.HarmonicPencilCell

/-!
# The channel-agnostic focal residual: no independent residual mode

`HarmonicPencilCell.lean` proves the pencil/Gram **rank-drop ⇔ signed-channel zero** for an
arbitrary channel pair (`harmonicGram_rank_drop_iff_channel_zero`), and `FocalResidualVanishes.lean`
completes the residual-vanishing for the Dirichlet model (`normalized_cell_focal_residual_exact`,
`focal_residual_zero_iff_scalar_zero`).  This file lifts the **residual-exactness** step to the same
channel-agnostic generality, so the full `(E4)` chain

```
P = M  →  lane dependence  →  Gram rank-drop  →  closed singular direction
       →  residual = (nonzero unit)·(signed channel)  →  no independent residual mode
```

is formalized for **any** admissible channel pair — in particular for the P/M channels of a general
finite duality-stable (`FiniteWeightFiber.fiber_det_one`) fiber, not only the Dirichlet
instantiation.  The exact analytic completion of the symmetric-power/twist family is then the
numerical verification through `Sym^13`; the algebraic residue-free core is what is proved here.

* `harmonic_residual_exact` — the normalized focal residual `det H / A = (λ − μ)·B` is an **exact
  nonzero multiple** of the signed channel `B`: no independent constant mode, slaved to the readout.
* `harmonic_residual_zero_iff_channel_zero` — the residual vanishes iff `B = 0`.
* `harmonic_residual_no_independent_mode` — the packaged `(E4)` statement: the Gram rank-drop and the
  residual-vanishing are the *same* event, and the residual carries no coefficient independent of `B`.

No `axiom`, no `sorry`.
-/

open Complex Matrix
open scoped BigOperators

namespace CriticalLinePhasor.HarmonicCell

/-- **The normalized focal residual is an exact nonzero multiple of the signed channel.**
For any channels `A, B` with `A ≠ 0` and admissible calibration `λ ≠ μ`, the normalized residual
`det H(A,B,μ,λ) / A` equals `(λ − μ)·B`, the nonzero unit `(λ − μ)` times the signed channel `B`.
The residual therefore carries **no independent constant mode**: it is slaved to the readout `B`
and vanishes exactly with it.  This is the channel-agnostic form of
`normalized_cell_focal_residual_exact`. -/
theorem harmonic_residual_exact (A B μ lam : ℂ) (hA : A ≠ 0) (hlam : lam ≠ μ) :
    (harmonicPencil A B μ lam).det / A = (lam - μ) * B ∧ (lam - μ) ≠ 0 := by
  refine ⟨?_, sub_ne_zero.mpr hlam⟩
  rw [harmonicPencil_det, mul_right_comm, mul_div_assoc, div_self hA, mul_one]

/-- **Residual vanishes ⇔ signed channel closes** — the same event the Gram rank-drop detects
(`harmonicGram_rank_drop_iff_channel_zero`). -/
theorem harmonic_residual_zero_iff_channel_zero (A B μ lam : ℂ) (hA : A ≠ 0) (hlam : lam ≠ μ) :
    (harmonicPencil A B μ lam).det / A = 0 ↔ B = 0 := by
  obtain ⟨hexact, hV⟩ := harmonic_residual_exact A B μ lam hA hlam
  rw [hexact, mul_eq_zero, or_iff_right hV]

/-- **Packaged `(E4)` chain, channel-agnostic.**  Under admissibility (`A ≠ 0`, `λ ≠ μ`): the Gram
matrix `Hᴴ·H` drops rank iff the normalized residual `det H / A` vanishes, and that residual is
`(λ − μ)·B` — an exact nonzero multiple of the signed channel, hence no independent zero-frequency
coefficient.  Because it reads only `(A, B, μ, λ)` it applies verbatim to the P/M channels of a
general det-one fiber, not merely the Dirichlet instantiation. -/
theorem harmonic_residual_no_independent_mode (A B μ lam : ℂ) (hA : A ≠ 0) (hlam : lam ≠ μ) :
    (((harmonicPencil A B μ lam)ᴴ * harmonicPencil A B μ lam).det = 0
        ↔ (harmonicPencil A B μ lam).det / A = 0)
      ∧ (harmonicPencil A B μ lam).det / A = (lam - μ) * B := by
  refine ⟨?_, (harmonic_residual_exact A B μ lam hA hlam).1⟩
  rw [harmonicGram_rank_drop_iff_channel_zero A B μ lam hA hlam,
    harmonic_residual_zero_iff_channel_zero A B μ lam hA hlam]

end CriticalLinePhasor.HarmonicCell
