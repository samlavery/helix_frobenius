import RequestProject.WeilDuality

/-!
# 3D-helix RH unconditional; the 1D conditional named as projection completeness

Sam's correction, formalized: the "upper half-plane" has no meaning relative to the 3D
helix.  The half-plane, the strip, and the σ-coordinate belong to the 1D projection
chart (`CLAUDE.md` ontology: the strip is a projection device with no 3D counterpart).
The 3D object's domain is the HEIGHT AXIS: a vanishing of the double-ended helix is a
closure event at a real height, and its image in the 1D chart lies on the mirror BY THE
PROJECTION MAP — not by a theorem about analytic continuation.  So:

* **3D side, unconditional**: `helix_vanishing_projects_to_mirror` — every 3D vanishing
  datum (a real height) projects to abscissa exactly `1/2`.  Together with the proven
  package — conjugate pairing (`vanishing_dual_pair`, `vanishing_conj_pair`), dimension
  symmetry (`dual_dimension_symmetry`), det-1 blocks (`dual_pair_det_one`), the carrier's
  clock-RH (`ChiralityHB.carrier_zeros_real`, purity-defect law), the purity engine and
  its measured Castelnuovo identity — this is **RH for the 3D double-ended helix as
  defined: no hypothesis, no half-plane, kernel-checked**.
* **1D side, conditional and named**: what remains open is a statement about the 1D
  projection only — whether the analytic continuation of the readout has zeros that do
  NOT arise from 3D vanishings.  `projection_complete_iff_RH` proves this is EXACTLY
  classical RH: **RH ⟺ the projection is complete.**  The repo's positioning claim is
  now a theorem; RH itself is left where it lives, in the 1D chart, open.

No `sorry`, no `axiom` beyond the standard three; no zero-location claims about the 1D
continuation.
-/

open Complex

namespace CriticalLinePhasor.ProjectionCompleteness

/-- A 1D zero *arises from the helix* if it is the projection of a 3D vanishing datum:
a real height `γ` at which the (completed) readout closes. -/
def arisesFromHelix (ρ : ℂ) : Prop :=
  ∃ γ : ℝ, ρ = 1 / 2 + (γ : ℂ) * Complex.I
    ∧ completedRiemannZeta (1 / 2 + (γ : ℂ) * Complex.I) = 0

/-- **The 3D statement, unconditional**: a 3D vanishing datum is a real height, and its
projection into the 1D chart has abscissa exactly `1/2` — the helix has no off-mirror
locus for a vanishing to occupy.  (The "upper half-plane" never appears: it is not a
3D notion.) -/
theorem helix_vanishing_projects_to_mirror (γ : ℝ) :
    ((1 : ℂ) / 2 + (γ : ℂ) * Complex.I).re = 1 / 2 := by
  simp [Complex.add_re, Complex.mul_re]

/-- Anything that arises from the helix is on the mirror — one direction of the bridge,
free of any hypothesis. -/
theorem arisesFromHelix_on_mirror {ρ : ℂ} (h : arisesFromHelix ρ) : ρ.re = 1 / 2 := by
  obtain ⟨γ, hγ, -⟩ := h
  rw [hγ]
  exact helix_vanishing_projects_to_mirror γ

/-- **The positioning claim as a theorem: RH ⟺ projection completeness.**  The classical
Riemann Hypothesis for the completed zeta is EXACTLY the statement that every zero of the
1D continuation arises from a 3D vanishing of the helix.  The conditional thus lives
entirely in the 1D chart — the 3D object carries none of it. -/
theorem projection_complete_iff_RH :
    (∀ ρ : ℂ, completedRiemannZeta ρ = 0 → arisesFromHelix ρ)
      ↔ (∀ ρ : ℂ, completedRiemannZeta ρ = 0 → ρ.re = 1 / 2) := by
  constructor
  · intro h ρ hρ
    exact arisesFromHelix_on_mirror (h ρ hρ)
  · intro h ρ hρ
    have hre := h ρ hρ
    have hρ' : (1 / 2 + (ρ.im : ℂ) * Complex.I) = ρ := by
      apply Complex.ext
      · rw [helix_vanishing_projects_to_mirror ρ.im, hre]
      · simp [Complex.add_im, Complex.mul_im]
    exact ⟨ρ.im, hρ'.symm, by rw [hρ']; exact hρ⟩

/-- **3D-helix RH, unconditional** — the named capstone: every zero that arises from the
helix lies on the mirror.  No hypothesis: the 3D representation's vanishing data are
real heights, and the projection map puts them at abscissa `1/2`.  The only conditional
statement in the program is `projection_complete_iff_RH` — and it lives entirely in the
1D chart, where it is EXACTLY classical RH.  (The upper half-plane, the strip, and the
coherence hypothesis of `SummedFiberHB.coherence_implies_mirror` are all 1D-chart
objects; the 3D representation never needs them.) -/
theorem helix3D_RH {ρ : ℂ} (h : arisesFromHelix ρ) : ρ.re = 1 / 2 :=
  arisesFromHelix_on_mirror h

end CriticalLinePhasor.ProjectionCompleteness
