import RequestProject.HodgeDial

/-!
# Family-level transcendental retention: the Ceresa classes of the
# Laga–Shnidman family

The review's hardest realization obligation is the transcendental
retained coordinate: a FAMILY-level no-silent-class theorem at a layer
where the readout is a transcendental height, not a rational amplitude.
This file supplies the first such bundle, at the exact strength available.

The family is Laga–Shnidman's bielliptic Picard curves: their theorem
identifies the Beilinson–Bloch height of the Ceresa class `κ(C_t)` with a
POSITIVE multiple of the Néron–Tate height of an explicit point `Q_t` on
`y² = x³ + 1`, vanishing precisely at torsion.  The bundle carries exactly
two cited monuments — the proportionality (Laga–Shnidman) and the
Néron–Tate laws (nonnegativity, kernel-exactly-torsion) — and proves,
family-level (every member `t` at once, not per-instance):

* `no_silent_ceresa`: every non-torsion Ceresa class of the family fires
  at the depth-three readout — retention at the first transcendental
  layer, in the anisotropic-pairing shape;
* `silent_iff_torsion`: the silence locus is EXACTLY the torsion locus —
  the isotropy boundary the instruments measured (`t = 0, ±3`) is forced,
  not observed.

Honest register: a `FaithfulRealization` term is deliberately NOT
constructed here — the model's rationality field cannot hold for a
transcendental-valued readout, and that misfit is precisely the open
obligation the review names.  What IS proven: the retention half at
family level, from the two cited inputs and nothing else.  Scope: does
not assume or prove RH/GRH, the Hodge conjecture, or Beilinson–Bloch
nondegeneracy beyond the cited family theorem.
-/

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- The Laga–Shnidman family bundle: the Ceresa classes over the family
base, the explicit Abel–Jacobi points, and the two cited monuments. -/
structure CeresaFamilyData (T : Type*) where
  /-- the torsion locus of the family (measured: `t = 0, ±3`). -/
  IsTorsion : T → Prop
  /-- the Néron–Tate height of the explicit point `Q_t`. -/
  ntHeight : T → ℝ
  /-- the Beilinson–Bloch height of the Ceresa class `κ(C_t)`. -/
  bbHeight : T → ℝ
  /-- the proportionality factor of the family. -/
  factor : T → ℝ
  /-- **Laga–Shnidman (cited):** the Ceresa height is the factor times the
  Néron–Tate height, with the factor positive on the family. -/
  ls_identity : ∀ t, bbHeight t = factor t * ntHeight t
  ls_factor_pos : ∀ t, 0 < factor t
  /-- **Néron–Tate (cited):** nonnegativity and kernel-exactly-torsion. -/
  nt_nonneg : ∀ t, 0 ≤ ntHeight t
  nt_zero_iff : ∀ t, ntHeight t = 0 ↔ IsTorsion t

namespace CeresaFamilyData

variable {T : Type*} (D : CeresaFamilyData T)

/-- The Ceresa height is nonnegative across the family. -/
theorem bb_nonneg (t : T) : 0 ≤ D.bbHeight t := by
  rw [D.ls_identity t]
  exact mul_nonneg (le_of_lt (D.ls_factor_pos t)) (D.nt_nonneg t)

/-- **Family-level transcendental retention**: every non-torsion member's
Ceresa class fires at the depth-three readout — no silent class, all `t`
at once. -/
theorem no_silent_ceresa (t : T) (h : ¬ D.IsTorsion t) :
    D.bbHeight t ≠ 0 := by
  intro h0
  rw [D.ls_identity t] at h0
  rcases mul_eq_zero.mp h0 with hf | hn
  · exact absurd hf (ne_of_gt (D.ls_factor_pos t))
  · exact h ((D.nt_zero_iff t).mp hn)

/-- **The silence locus is exactly torsion**: the isotropy boundary is
forced by the two monuments, not observed. -/
theorem silent_iff_torsion (t : T) :
    D.bbHeight t = 0 ↔ D.IsTorsion t := by
  constructor
  · intro h0
    by_contra h
    exact no_silent_ceresa D t h h0
  · intro h
    rw [D.ls_identity t]
    rw [(D.nt_zero_iff t).mpr h]
    ring

/-- The depth-three firing is strictly positive off torsion — the
anisotropic-pairing shape of retention at the transcendental layer. -/
theorem fires_positively (t : T) (h : ¬ D.IsTorsion t) :
    0 < D.bbHeight t :=
  lt_of_le_of_ne (D.bb_nonneg t) (Ne.symm (D.no_silent_ceresa t h))

end CeresaFamilyData

end CriticalLinePhasor.HodgeLedgerFiltration
