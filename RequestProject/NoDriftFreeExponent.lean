import RequestProject.LimitFocalEvent
import RequestProject.FocalLineGate

/-!
# No Drift with a free exponent (ledger 1180)

Every compiled No Drift theorem compares an exponent `σ` with a reference: a literal `½`
(`HelixDefs.no_radial_drift_iff_half`), `carrierAbscissa` evaluated at a chart point whose real part
is `carrierAbscissa` (`ThreeDFocalEvent.carrierPointAtHeight_noRadialDrift`), or the base of a pole
coordinate defined as `½ + rate` (`HelixSource`). Here every reference is replaced by a free
exponent.

* `noDrift_iff_eq_ref`: for `n > 1`, `n^(σ − τ) = 1 ↔ σ = τ`. Drift only compares two exponents.
* `NativeNoDrift σ`: the fiber amplitude `n^{−σ}` against the carrier's own radius settles at a
  positive value. `nativeNoDrift_iff_scaleBalanced`: this IS `CarrierScaleBalanced σ` (the same
  predicate). `nativeNoDrift_iff_half`: the area law gives its value.
* `cancellationForcesBalance_iff` (χ ≠ 1): "every limit focal cancellation of the χ fiber has
  native no drift at its amplitude exponent" is equivalent to "every zero of `L(χ, ·)` with
  `Re ρ > 0` has `Re ρ = ½`". Proof: `ofLZero` and `char_event_is_zero` (events ⟷ zeros) and the
  area law; no `carrierAbscissa` (scan below).
* The η routing: `LimitFocalEventNS.not_cancellationForcesBalance_eta` (ledger 1156): for the η fiber
  the statement is false (its dyadic-factor cancellations at exponent 1).

**Scope (cleanup, ledger 1237).** `cancellationForcesBalance_iff` is a CHARACTERIZATION: it says what
its left side is equivalent to and does NOT prove its left side. It is not a compiled
"cancellation → balance" theorem. `CancellationForcesBalance` quantifies over the weak asymptotic type
`LimitFocalEvent`, which admits factor-induced limit zeros; it is not a statement about physical focal
events (`FocalEventProjection.FocalEvent`). The η failure comes only from the dyadic-factor witness.
`NativeNoDrift` and `nativeNoDrift_iff_half` are the native Area Law / no-drift provenance of the
balanced exponent.
-/

open Filter Topology

namespace CriticalLinePhasor.NoDriftFree

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.LimitFocalEventNS

/-- **Drift only compares two exponents.** -/
theorem noDrift_iff_eq_ref {n : ℝ} (hn : 1 < n) (σ τ : ℝ) : n ^ (σ - τ) = 1 ↔ σ = τ := by
  constructor
  · intro h
    have hn0 : 0 < n := by linarith
    have hlog : Real.log n ≠ 0 := (Real.log_pos hn).ne'
    have h2 := congrArg Real.log h
    rw [Real.log_rpow hn0, Real.log_one] at h2
    have := (mul_eq_zero.mp h2).resolve_right hlog
    linarith
  · intro h
    rw [h, sub_self, Real.rpow_zero]

/-- The site-scale product: the fiber amplitude `n^{−σ}` against the carrier's radius at site `n`. -/
noncomputable def siteScale (σ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-σ) * Geometry.carrierRadius 1 3 n

/-- **Native no drift at exponent `σ`**: the site-scale product settles at a positive value. -/
def NativeNoDrift (σ : ℝ) : Prop := ∃ L : ℝ, 0 < L ∧ Tendsto (siteScale σ) atTop (𝓝 L)

/-- **Native no drift is the area-law specification itself.** -/
theorem nativeNoDrift_iff_scaleBalanced (σ : ℝ) : NativeNoDrift σ ↔ CarrierScaleBalanced σ :=
  Iff.rfl

/-- The area law gives its value. -/
theorem nativeNoDrift_iff_half (σ : ℝ) : NativeNoDrift σ ↔ σ = 1 / 2 :=
  carrierScaleBalanced_iff σ

/-- **For a character fiber, "cancellation forces native no drift" is the statement that every zero
with `Re ρ > 0` has `Re ρ = ½`.** A characterization of its left side, not a proof of it; the left
side quantifies over the weak asymptotic type `LimitFocalEvent`. -/
theorem cancellationForcesBalance_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    CancellationForcesBalance (fun n : ℕ => χ (n : ZMod q)) ↔
      ∀ ρ : ℂ, 0 < ρ.re → DirichletCharacter.LFunction χ ρ = 0 → ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ hz
    exact (carrierScaleBalanced_iff _).1 (h (LimitFocalEvent.ofLZero χ hχ ρ hρ hz) rfl)
  · intro h e hw
    have hz := char_event_is_zero χ hχ e hw
    have hre : ((e.σ : ℂ) + (e.y : ℂ) * Complex.I).re = e.σ := by simp
    have h2 := h _ (by rw [hre]; exact e.σ_pos) hz
    rw [hre] at h2
    exact (carrierScaleBalanced_iff _).2 h2

end CriticalLinePhasor.NoDriftFree

#scan_abscissa CriticalLinePhasor.NoDriftFree.noDrift_iff_eq_ref
  CriticalLinePhasor.NoDriftFree.nativeNoDrift_iff_scaleBalanced
  CriticalLinePhasor.NoDriftFree.nativeNoDrift_iff_half
  CriticalLinePhasor.NoDriftFree.cancellationForcesBalance_iff
  CriticalLinePhasor.LimitFocalEventNS.not_cancellationForcesBalance_eta
  CriticalLinePhasor.ThreeDFocal.carrierPointAtHeight_noRadialDrift

#print axioms CriticalLinePhasor.NoDriftFree.noDrift_iff_eq_ref
#print axioms CriticalLinePhasor.NoDriftFree.nativeNoDrift_iff_scaleBalanced
#print axioms CriticalLinePhasor.NoDriftFree.nativeNoDrift_iff_half
#print axioms CriticalLinePhasor.NoDriftFree.cancellationForcesBalance_iff
