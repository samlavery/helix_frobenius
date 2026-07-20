import RequestProject.GaloisRealizationInstance
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The third rung, typed: depth one for elliptic curves, literature-conditional

The `H^1` rung of the realization ladder (Mordell–Weil groups, the depth-one cycle data of the
paper) cannot yet be unconditional in Lean: as of this Mathlib (v4.32.0-era master), the Weil
height machine has landed (`Mathlib.NumberTheory.Height.Basic`, `…Northcott`,
`…Projectivization`), elliptic reduction theory and `L`-functions exist
(`Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`, `…LFunction`), and the approximate
parallelogram law for the naïve height is in progress upstream
(`Mathlib.NumberTheory.Height.EllipticCurve`, M. Stoll) — but **Mordell–Weil finite generation
and the Néron–Tate canonical height are not yet theorems**.  Following the house convention for
classical inputs, this file types them as **literature hypotheses, cited at the point of use**:

* `gens`/`gens_generate` — **Mordell (1922), Weil (1929)**: the point group is finitely
  generated (stated in explicit generators-mod-torsion form);
* `pairing` with its symmetry, positivity, and torsion-kernel fields — **Néron (1965), Tate**
  (cf. Silverman, *The Arithmetic of Elliptic Curves*, VIII.9): the canonical height pairing.

What is then **proved unconditionally from the bundle** (no further input):

* `pairing_torsion_right` — torsion is orthogonal to everything: the discrete Cauchy–Schwarz
  argument (`0 ≤ ⟨p + n·t, p + n·t⟩ = ⟨p,p⟩ + 2n⟨p,t⟩` for every integer `n` forces
  `⟨p,t⟩ = 0`);
* `faithful_mod_torsion` — the pairing coordinates against the generators have kernel exactly
  the torsion: **the depth-one no-kernel condition (v), mod torsion**;
* `no_silent_point` / `coordinateTower_detects_nonTorsion` — **retention at grade one**: every
  non-torsion class fires at some coordinate level of the depth-one tower (`Detectable`, the
  in-tree interface; the diagonal readout is the anisotropic-pairing shape of
  `grade_visible_of_nondegenerate`).

The bundle is instantiated on an actual Mathlib elliptic-curve point group
(`W.toAffine.Point` for `W : WeierstrassCurve ℚ`), so the hypotheses attach to the genuine
object, and each field is expected to become a theorem as the upstream height program
completes — at which point this rung goes unconditional with no change to its statements.
The angular (`FaithfulRealization`) form of this rung is deliberately **not** forced: the
depth-one pairing coordinates are radial/regulator data, not frequency-channel data; their
frequency identification (the jet/derivative channels of the paper's depth-one landing) is a
named next step, not smuggled here.  No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace CriticalLinePhasor.HodgeLedgerFiltration

/-- **The depth-one literature-hypothesis bundle** for a point group `P`.  Every field is a
classical statement with its citation; nothing here is proved, and everything downstream that
consumes it is conditional on exactly these named inputs. -/
structure DepthOneHeightData (P : Type*) [AddCommGroup P] where
  /-- The Mordell–Weil rank bound. **Mordell (1922), Weil (1929).** -/
  rank : ℕ
  /-- Generators of the free part. **Mordell (1922), Weil (1929)** (with the classification of
  finitely generated abelian groups). -/
  gens : Fin rank → P
  /-- Finite generation mod torsion, in explicit form. **Mordell (1922), Weil (1929).** -/
  gens_generate : ∀ p : P, ∃ (c : Fin rank → ℤ) (t : P),
    IsOfFinAddOrder t ∧ p = (∑ i, c i • gens i) + t
  /-- The canonical height pairing. **Néron (1965), Tate**; cf. Silverman VIII.9. -/
  pairing : P →+ P →+ ℝ
  /-- Symmetry of the canonical pairing. **Néron (1965), Tate.** -/
  pairing_symm : ∀ p q : P, pairing p q = pairing q p
  /-- Positivity of the canonical height. **Néron (1965), Tate.** -/
  pairing_nonneg : ∀ p : P, 0 ≤ pairing p p
  /-- The kernel of the height is exactly the torsion. **Néron (1965), Tate**; cf. Silverman
  VIII.9.6. -/
  pairing_zero_iff : ∀ p : P, pairing p p = 0 ↔ IsOfFinAddOrder p

namespace DepthOneHeightData

variable {P : Type*} [AddCommGroup P] (D : DepthOneHeightData P)

/-- Torsion classes have zero height. -/
theorem pairing_diag_torsion {t : P} (ht : IsOfFinAddOrder t) : D.pairing t t = 0 :=
  (D.pairing_zero_iff t).mpr ht

/-- **Torsion is orthogonal to everything** — the discrete Cauchy–Schwarz argument, proved from
the bundle alone: for every integer `n`, `0 ≤ ⟨p + n·t, p + n·t⟩ = ⟨p,p⟩ + 2n⟨p,t⟩`, which
forces `⟨p,t⟩ = 0`. -/
theorem pairing_torsion_right {p t : P} (ht : IsOfFinAddOrder t) : D.pairing p t = 0 := by
  have main : ∀ t' : P, IsOfFinAddOrder t' → ¬ 0 < D.pairing p t' := by
    intro t' ht' hpos
    have htt : D.pairing t' t' = 0 := D.pairing_diag_torsion ht'
    have hkey : ∀ n : ℤ, 0 ≤ D.pairing p p + 2 * (n : ℝ) * D.pairing p t' := by
      intro n
      have h0 := D.pairing_nonneg (p + n • t')
      have e1 : D.pairing (p + n • t') p
          = D.pairing p p + (n : ℝ) * D.pairing p t' := by
        rw [D.pairing_symm, map_add, map_zsmul, zsmul_eq_mul]
      have e2 : D.pairing (p + n • t') t' = D.pairing p t' := by
        rw [D.pairing_symm, map_add, map_zsmul, zsmul_eq_mul, htt, mul_zero, add_zero,
          D.pairing_symm t' p]
      have hexp : D.pairing (p + n • t') (p + n • t')
          = D.pairing p p + 2 * (n : ℝ) * D.pairing p t' := by
        rw [map_add (D.pairing (p + n • t')), map_zsmul (D.pairing (p + n • t')),
          zsmul_eq_mul, e1, e2]
        ring
      rw [hexp] at h0
      exact h0
    obtain ⟨n, hn⟩ := exists_int_lt (-(D.pairing p p) / (2 * D.pairing p t'))
    have h2b : (0 : ℝ) < 2 * D.pairing p t' := by linarith
    have hlt : (n : ℝ) * (2 * D.pairing p t') < -(D.pairing p p) :=
      (lt_div_iff₀ h2b).mp hn
    have := hkey n
    nlinarith
  rcases lt_trichotomy (D.pairing p t) 0 with hneg | hzero | hpos
  · exfalso
    refine main (-t) ht.neg ?_
    rw [map_neg]
    linarith
  · exact hzero
  · exact absurd hpos (main t ht)

/-- **Faithfulness mod torsion** — the depth-one no-kernel condition (v): a class pairing to
zero against every generator is torsion. -/
theorem faithful_mod_torsion {p : P} (h : ∀ i, D.pairing p (D.gens i) = 0) :
    IsOfFinAddOrder p := by
  obtain ⟨c, t, ht, hp⟩ := D.gens_generate p
  have h2 : D.pairing p p = D.pairing p ((∑ i, c i • D.gens i) + t) := congrArg _ hp
  rw [map_add, D.pairing_torsion_right ht, add_zero, map_sum,
    Finset.sum_eq_zero (fun i _ => by rw [map_zsmul, h i, smul_zero])] at h2
  exact (D.pairing_zero_iff p).mp h2

/-- **No silent point**: a non-torsion class has nonzero height — retention at grade one, in
the anisotropic-pairing shape of `grade_visible_of_nondegenerate`. -/
theorem no_silent_point {p : P} (hp : ¬ IsOfFinAddOrder p) : D.pairing p p ≠ 0 :=
  fun h => hp ((D.pairing_zero_iff p).mp h)

/-- The depth-one coordinate tower: level `i < rank` reads the pairing coordinate against the
`i`-th generator. -/
noncomputable def coordinateTower : ℕ → P → ℂ := fun d p =>
  if h : d < D.rank then ((D.pairing p (D.gens ⟨d, h⟩) : ℝ) : ℂ) else 0

/-- **Retention at grade one, literature-conditional**: every non-torsion class is detected by
the depth-one coordinate tower (`Detectable`, the in-tree carrier interface). -/
theorem coordinateTower_detects_nonTorsion {p : P} (hp : ¬ IsOfFinAddOrder p) :
    Detectable D.coordinateTower p := by
  by_contra hsil
  rw [Detectable] at hsil
  push Not at hsil
  refine hp (D.faithful_mod_torsion fun i => ?_)
  have h := hsil i.val
  simp only [coordinateTower, i.isLt, dif_pos, Fin.eta] at h
  exact_mod_cast h

/-- **The depth-one cycle-to-jet realization**: the pairing-coordinate map into the order-zero
jet model, additive — the radial counterpart of the bridge's (iv-a) field. -/
noncomputable def realization : P →+ GeneralExtensionData 0 D.rank where
  toFun p := fun _ i => ((D.pairing p (D.gens i) : ℝ) : ℂ)
  map_zero' := by
    funext l i
    simp
  map_add' p q := by
    funext l i
    simp only [map_add, AddMonoidHom.add_apply, Complex.ofReal_add, Pi.add_apply]

/-- **Kernel exactly the torsion** — the general cycle-to-jet realization at depth one, as an
equivalence, from the cited bundle alone: the jet coordinates see precisely the free part of
the Mordell–Weil group.  Forward direction is `faithful_mod_torsion` (no kernel beyond
torsion); reverse is `pairing_torsion_right` (torsion is invisible to the height channel, as
the ledger says — it is read at a different coordinate). -/
theorem realization_eq_zero_iff (p : P) :
    D.realization p = 0 ↔ IsOfFinAddOrder p := by
  constructor
  · intro h
    refine D.faithful_mod_torsion fun i => ?_
    have hcoord : ((D.pairing p (D.gens i) : ℝ) : ℂ) = 0 := congrFun (congrFun h 0) i
    exact_mod_cast hcoord
  · intro ht
    funext l i
    show ((D.pairing p (D.gens i) : ℝ) : ℂ) = 0
    rw [D.pairing_symm, D.pairing_torsion_right ht, Complex.ofReal_zero]

end DepthOneHeightData

/-! ## The bundle attached to an actual Mathlib elliptic curve -/

/-- **The third rung, attached to the genuine object**: the depth-one literature-hypothesis
bundle for the point group of a Weierstrass curve over `ℚ` (the Mathlib
`WeierstrassCurve.Affine.Point` group).  Its fields are Mordell–Weil and Néron–Tate, cited;
they are expected to become theorems as Mathlib's height program
(`Mathlib.NumberTheory.Height.*`) completes. -/
abbrev EllipticDepthOneHypotheses (W : WeierstrassCurve ℚ) : Type :=
  DepthOneHeightData W.toAffine.Point

/-- **No silent rational point**, literature-conditional: for an elliptic curve over `ℚ`, given
the cited Mordell–Weil and Néron–Tate inputs, every non-torsion rational point fires at some
level of the depth-one coordinate tower. -/
theorem elliptic_no_silent_point (W : WeierstrassCurve ℚ) (D : EllipticDepthOneHypotheses W)
    {p : W.toAffine.Point} (hp : ¬ IsOfFinAddOrder p) :
    Detectable D.coordinateTower p :=
  D.coordinateTower_detects_nonTorsion hp

end CriticalLinePhasor.HodgeLedgerFiltration

#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DepthOneHeightData.pairing_torsion_right
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DepthOneHeightData.faithful_mod_torsion
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DepthOneHeightData.no_silent_point
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DepthOneHeightData.coordinateTower_detects_nonTorsion
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.DepthOneHeightData.realization_eq_zero_iff
#print axioms CriticalLinePhasor.HodgeLedgerFiltration.elliptic_no_silent_point
