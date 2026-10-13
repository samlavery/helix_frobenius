import RequestProject.LimitFocalEvent
import RequestProject.GlobalHelixIntertwiner

/-!
# The type bridge from the limit focal event to the Klein fold (ledger 1159)

The Klein fold (tmp/att1100, promoted here) acts on 3D states: J = `globalHelixInvolution`
`(r, φ, h) ↦ (r, −φ, −h)` (radius kept, so no scaling between the feet), the native transport
`T k α τ : (r, φ, h) ↦ (k·r, φ + α, h + τ)`, and the closed word `J·T·J·T`, which returns phase and
height and multiplies the radius by `k²` (`kleinWord_apply`). The step of att1101 (magnitude × √2) is
NOT used; the step here is built from the native carrier radius.

* (i) `RoutedLimitEvent`: a limit focal event whose law has every coefficient of absolute value 0 or 1
  (characters and η: `ofLZero_routed`, `etaFactorRouted`).
* (ii) `eventStep e m = mag3(phasor at m) · carrierRadius 1 3 m` (`eventStep_eq`: `= m^{−σ}·R_m`).
* (iii) The fold on that step. `KleinDescendsAt e m` (the word has trivial holonomy at site `m`), with
  `kleinDescendsAt_iff` (⟺ `eventStep e m = 1`). `KleinDescendsAsymptotically e` (the step settles to a
  positive constant, i.e. no radial drift around the loop; a constant is a normalization of `T`), with
  `kleinDescendsAsymptotically_iff` (⟺ `CarrierScaleBalanced σ`).
* Both properties on one object: `RoutedLimitEvent.isFocal`. The η-factor control
  `etaFactor_focal_not_descends` is focal and does not descend.
* The proposition the repository can now state, named and not assumed: `AnalyticZerosDescend χ`, and
  `analyticZerosDescend_iff` (⟺ every zero's exponent is balanced).

No value of the balance exponent, no `endPairFace`, FE, `1 − s`, or scaling between the feet.

**Scope (cleanup, ledger 1237).** Throughout this file "focal" refers to the weak asymptotic type
`LimitFocalEvent` (limit vanishing of `lawFiber`), not to physical focal cancellation
(`FocalEventProjection.FocalEvent`). `etaFactorRouted` / `etaFactor_focal_not_descends` use the η dyadic-factor
witness, a factor-induced limit zero and not a physical focal event. `AnalyticZerosDescend` is a coverage
statement over the weak type, starting from analytic zeros (`ofLZero_routed`). It is not the remaining theorem.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.KleinEventBridge

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.EisensteinWheelBank
open CriticalLinePhasor.FiberDetectorChain CriticalLinePhasor.LimitFocalEventNS
open CriticalLinePhasor.GlobalHelix

/-! ## The Klein fold (promoted from tmp/att1100) -/

/-- The native transport: scale the radius by `k`, turn the phase by `α`, shift the signed height by
`τ`. -/
def T (k α τ : ℝ) (f : ConeProjection.Fiber) : ConeProjection.Fiber :=
  (k * f.1, f.2.1 + α, f.2.2 + τ)

/-- **The closed word `J·T·J·T`** returns phase and height and multiplies the radius by `k²`. -/
theorem kleinWord_apply (k α τ : ℝ) (f : ConeProjection.Fiber) :
    globalHelixInvolution (T k α τ (globalHelixInvolution (T k α τ f))) = (k ^ 2 * f.1, f.2.1, f.2.2) := by
  rcases f with ⟨r, φ, h⟩
  simp [T, globalHelixInvolution, ConeProjection.radial, ConeProjection.phase, ConeProjection.height]
  ring

/-! ## (i) The routed limit focal event -/

/-- A limit focal event whose routing law has every coefficient of absolute value 0 or 1. -/
structure RoutedLimitEvent where
  e : LimitFocalEvent
  routed : ∀ n, 0 < n → ‖e.w n‖ = 0 ∨ ‖e.w n‖ = 1

/-- Focal cancellation of the routed event (its grown fiber cancels in the limit). "Focal" in the weak
asymptotic sense only; not physical bank-level cancellation at the native head. -/
theorem RoutedLimitEvent.isFocal (ev : RoutedLimitEvent) :
    Tendsto (fun Z => lawFiber ev.e.w Z ((ev.e.σ : ℂ) + (ev.e.y : ℂ) * Complex.I)) atTop (𝓝 0) :=
  ev.e.cancel

theorem character_routed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ (n : ZMod q)‖ = 0 ∨ ‖χ (n : ZMod q)‖ = 1 := by
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨u, hu⟩ := hu
    right
    rw [← hu, DirichletCharacter.unit_norm_eq_one]
  · left
    rw [MulChar.map_nonunit _ hu, norm_zero]

/-- Every zero of `L(χ, ·)` with `Re > 0` gives a routed limit focal event. -/
def ofLZero_routed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : 0 < ρ.re) (hz : DirichletCharacter.LFunction χ ρ = 0) : RoutedLimitEvent where
  e := LimitFocalEvent.ofLZero χ hχ ρ hρ hz
  routed := fun n _ => character_routed χ n

/-- The η-factor event of ledger 1156, routed. -/
def etaFactorRouted : RoutedLimitEvent where
  e := etaFactorEvent
  routed := fun n hn => routing_coeff_norm Routing.eta n hn

/-! ## (ii) The event's step -/

/-- **The event's step at site `m`**: the 3D magnitude of its phasor there times the native carrier
radius there. -/
def eventStep (ev : RoutedLimitEvent) (m : ℕ) : ℝ :=
  Phasor3D.mag3 (Phasor3D.phasor3D ev.e.w ev.e.σ ev.e.y m) * Geometry.carrierRadius 1 3 m

theorem eventStep_eq (ev : RoutedLimitEvent) {m : ℕ} (hm : 0 < m) :
    eventStep ev m = (m : ℝ) ^ (-ev.e.σ) * Geometry.carrierRadius 1 3 m := by
  rw [eventStep, mag3_phasor3D_of_norm ev.e.w ev.e.σ ev.e.y m hm (ev.routed m hm)]

theorem eventStep_nonneg (ev : RoutedLimitEvent) (m : ℕ) : 0 ≤ eventStep ev m :=
  mul_nonneg (by unfold Phasor3D.mag3; positivity) (Geometry.carrierRadius_nonneg 1 3 m)

/-! ## (iii) The fold on the event's step -/

/-- **Exact descent at site `m`**: the Klein word built from the event's step there has trivial holonomy. -/
def KleinDescendsAt (ev : RoutedLimitEvent) (m : ℕ) : Prop :=
  ∀ (α τ : ℝ) (f : ConeProjection.Fiber),
    globalHelixInvolution (T (eventStep ev m) α τ (globalHelixInvolution (T (eventStep ev m) α τ f))) = f

theorem kleinDescendsAt_iff (ev : RoutedLimitEvent) (m : ℕ) :
    KleinDescendsAt ev m ↔ eventStep ev m = 1 := by
  have hk := eventStep_nonneg ev m
  constructor
  · intro h
    have h1 := congrArg Prod.fst (h 0 0 (1, 0, 0))
    rw [kleinWord_apply] at h1
    simp only [mul_one] at h1
    nlinarith
  · intro h1 α τ f
    rw [kleinWord_apply, h1]
    rcases f with ⟨r, φ, h⟩
    simp

/-- **Asymptotic descent**: around the loop the event's step settles to a positive constant (no radial
drift). A constant limit is a normalization of the transport; drift to `0` or `∞` is the obstruction. -/
def KleinDescendsAsymptotically (ev : RoutedLimitEvent) : Prop :=
  ∃ L : ℝ, 0 < L ∧ Tendsto (eventStep ev) atTop (𝓝 L)

/-- **The fold's asymptotic descent of the event is the carrier balance of its exponent.** -/
theorem kleinDescendsAsymptotically_iff (ev : RoutedLimitEvent) :
    KleinDescendsAsymptotically ev ↔ CarrierScaleBalanced ev.e.σ := by
  have heq : ∀ᶠ m : ℕ in atTop,
      eventStep ev m = (m : ℝ) ^ (-ev.e.σ) * Geometry.carrierRadius 1 3 m := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact eventStep_eq ev hm
  constructor
  · rintro ⟨L, hL, hT⟩
    exact ⟨L, hL, hT.congr' heq⟩
  · rintro ⟨L, hL, hT⟩
    exact ⟨L, hL, hT.congr' (heq.mono fun _ h => h.symm)⟩

/-! ## Both properties on one object: the control -/

/-- **The η-factor event is focal and does not descend.** "Focal" in the weak asymptotic sense; the
η-factor event is factor-induced, not a physical focal event. -/
theorem etaFactor_focal_not_descends :
    Tendsto (fun Z => lawFiber etaFactorRouted.e.w Z
        ((etaFactorRouted.e.σ : ℂ) + (etaFactorRouted.e.y : ℂ) * Complex.I)) atTop (𝓝 0) ∧
      ¬ KleinDescendsAsymptotically etaFactorRouted := by
  refine ⟨etaFactorRouted.isFocal, fun h => not_balanced_one ?_⟩
  exact (kleinDescendsAsymptotically_iff etaFactorRouted).mp h

/-! ## The proposition the repository can now state (named, not assumed) -/

/-- **Every analytic zero's focal event descends through the Klein fold.** A coverage statement over the
weak asymptotic type, starting from analytic zeros; not the remaining theorem. -/
def AnalyticZerosDescend {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : Prop :=
  ∀ (ρ : ℂ) (hρ : 0 < ρ.re) (hz : DirichletCharacter.LFunction χ ρ = 0),
    KleinDescendsAsymptotically (ofLZero_routed χ hχ ρ hρ hz)

theorem ofLZero_routed_σ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : 0 < ρ.re) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    (ofLZero_routed χ hχ ρ hρ hz).e.σ = ρ.re :=
  rfl

theorem analyticZerosDescend_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    AnalyticZerosDescend χ hχ ↔
      ∀ ρ : ℂ, 0 < ρ.re → DirichletCharacter.LFunction χ ρ = 0 → CarrierScaleBalanced ρ.re := by
  constructor
  · intro h ρ hρ hz
    have h1 := (kleinDescendsAsymptotically_iff (ofLZero_routed χ hχ ρ hρ hz)).mp (h ρ hρ hz)
    rwa [ofLZero_routed_σ] at h1
  · intro h ρ hρ hz
    apply (kleinDescendsAsymptotically_iff (ofLZero_routed χ hχ ρ hρ hz)).mpr
    rw [ofLZero_routed_σ]
    exact h ρ hρ hz

end CriticalLinePhasor.KleinEventBridge

#print axioms CriticalLinePhasor.KleinEventBridge.kleinWord_apply
#print axioms CriticalLinePhasor.KleinEventBridge.eventStep_eq
#print axioms CriticalLinePhasor.KleinEventBridge.kleinDescendsAt_iff
#print axioms CriticalLinePhasor.KleinEventBridge.kleinDescendsAsymptotically_iff
#print axioms CriticalLinePhasor.KleinEventBridge.etaFactor_focal_not_descends
#print axioms CriticalLinePhasor.KleinEventBridge.analyticZerosDescend_iff
