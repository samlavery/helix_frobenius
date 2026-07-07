import Mathlib

/-!
# Forcible cell closure: the controllability core

`tmp/forcible_closure.py` validates numerically that a cuspidal fiber's per-cell residual
`D_C = ∑_{n ∈ C} a_n · ω(n)` can be driven to machine zero by a *readout-preserving* warp with a
few coherent generators (the winding `Ω(n)`, the distinct-prime count `ω(n)`, the vertical shift
`log n`):
* `Sym⁵ Δ` (open, r ≥ 5): `|D_C| → 4.0e-15`, warp params `|x| < 1.5`;
* `Sym¹³ Δ` (open):        `|D_C| → 3.6e-15`, warp params `|x| < 1.2`;
* cells independent (one cell's forcing warp leaves another cell's residual at `O(√cell)`).

So per-crossing cell closure is *forcible* by a small legitimate warp family. The **algebraic
core** of why this succeeds is a controllability statement: two independent warp
correction-directions span the residual plane `ℂ` (as an `ℝ`-space), hence *any* residual is
forcible to zero by real warp weights. The data-dependent input — that the warp genuinely
supplies two `ℝ`-independent directions at each cell — is exactly what the numerics certify; the
linear-algebra consequence is what is machine-checked here.

Scope: this does not by itself prove niceness for the general cuspidal fiber; it formalizes the
per-crossing *solvability* (controllability) that the forcible-closure mechanism rests on.
-/

namespace CriticalLinePhasor.ForcibleClosure

/-- **Controllability core of forcible cell closure.** If two warp correction-directions
`u v : ℂ` are `ℝ`-linearly independent — the two-generator warp supplying two independent
directions in the residual plane, the condition the numerics certify at each cell (nonzero real
Jacobian determinant) — then *every* cell residual `D` is forcible to zero: there are real warp
weights `s t` with `D + (s • u + t • v) = 0`. (`ℂ` is two-dimensional over `ℝ`, so two
independent directions span it; the readout-preserving warp supplies `u, v` at each crossing.) -/
theorem residual_forcible {u v : ℂ} (h : LinearIndependent ℝ ![u, v]) (D : ℂ) :
    ∃ s t : ℝ, D + (s • u + t • v) = 0 := by
  have htop : Submodule.span ℝ (Set.range ![u, v]) = ⊤ :=
    h.span_eq_top_of_card_eq_finrank (by simp [Complex.finrank_real_complex])
  have hmem : (-D) ∈ Submodule.span ℝ (Set.range ![u, v]) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨c 0, c 1, ?_⟩
  rw [Fin.sum_univ_two] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  rw [hc]; abel

end CriticalLinePhasor.ForcibleClosure
