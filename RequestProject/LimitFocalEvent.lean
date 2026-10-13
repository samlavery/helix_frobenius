import RequestProject.FocalEventProjection

/-!
# The limit focal event, the analytic zeros attached to it, and the drift test (ledger 1156)

The zero lives at the limit. A limit focal event is a routing law `w`, an amplitude exponent `σ > 0`
and an ordinate `y` at which the grown fiber cancels as the head climbs:
`lawFiber w Z (σ + iy) → 0`. No finite exact cancellation is used.

* `LimitFocalEvent`; `LimitFocalEvent.detector_tendsto`: the normalized detector converges as an operator
  to a pencil with zero signed channel, whose Gram is singular.
* Every analytic zero is attached. `ofLZero` takes a zero of `L(χ, ·)` with `Re > 0` (χ ≠ 1, via
  `limit_chain_char`); `ofZetaZero` takes a nontrivial ζ zero (η routing, via `limit_chain_eta`). The
  converse holds as well: `char_event_is_zero`.
* Projection: `LimitFocalEvent.height_eq` (the projected height is `e^y`), `readout_balanced` (readout
  `(balanceExponent, height)`), `readout_eq_of_y_eq` (the readout does not see `σ`).
* **The drift test.** `CancellationForcesBalance w`: every limit focal event with routing law `w` has
  `CarrierScaleBalanced σ`. FALSE for the η routing: `etaFactorEvent` is the limit focal event at
  `σ = 1`, `y = 2π/log 2`. There the η grown fiber's limit `(1 − 2^{1−s})·ζ(s)` vanishes through the
  dyadic factor (`etaFactorEvent_limit`), ζ itself does not vanish (`etaFactorEvent_not_zeta_zero`), and
  `σ = 1` is not balanced (`not_balanced_one`, from the sublinear growth of the carrier radius only).
  Hence `not_cancellationForcesBalance_eta`. Its readout coincides with that of a balanced event at the
  same ordinate (`etaFactorEvent_readout`).

No value of the balance exponent, no `Re ρ = ½`, no functional equation and no finite exact
cancellation is used.

**Scope (cleanup, ledger 1237).** `LimitFocalEvent` is a legitimate ASYMPTOTIC, observer-side object.
It is NOT synonymous with physical focal cancellation. Its only condition is the limit
`lawFiber w Z (σ + iy) → 0` with the head `Z` climbing at fixed `y`. It carries no exact cancellation
at the native head `physicalHead y`, no head–ordinate coupling, no exact positive-bank = negative-bank
equality, no J configuration or two-ended state, and no post-cancellation state `(M, Z)`. The rich
physical event is `FocalEventProjection.FocalEvent`; no map connects the two types. The type admits
factor-induced limit zeros: `etaFactorEvent` is the η conductor's dyadic multiplier `1 − 2^{1−s}`
vanishing while `ζ ≠ 0` (`EtaFactorAudit.eta_event_dichotomy`). It is legitimate for this weak type
and is not a physical focal event. `ofLZero` / `ofZetaZero` build the asymptotic object from an
analytic zero (readout → limit object); they do not manufacture a physical event.
`CancellationForcesBalance` quantifies over this weak type, so `not_cancellationForcesBalance_eta`
refutes only that overbroad predicate and says nothing about physical focal events.
-/

open Complex Filter Topology
open scoped Matrix

noncomputable section

namespace CriticalLinePhasor.LimitFocalEventNS

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.EisensteinWheelBank
open CriticalLinePhasor.HarmonicCell CriticalLinePhasor.FiberDetectorChain
open CriticalLinePhasor.FocalEventProjection

/-! ## 1. The limit focal event -/

/-- **A limit focal event**: the grown fiber of routing law `w` at amplitude exponent `σ` and
ordinate `y` cancels in the limit of the climbing head. Asymptotic and observer-side; not the
physical focal event `FocalEventProjection.FocalEvent` (see the module header's scope note). -/
structure LimitFocalEvent where
  w : ℕ → ℂ
  σ : ℝ
  y : ℝ
  σ_pos : 0 < σ
  cancel : Tendsto (fun Z => lawFiber w Z ((σ : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0)

/-- The normalized detector converges as an operator to the pencil with zero signed channel. -/
theorem LimitFocalEvent.detector_tendsto (e : LimitFocalEvent) (μ lam : ℂ) :
    Tendsto (fun Z => harmonicPencil 1 (lawFiber e.w Z ((e.σ : ℂ) + (e.y : ℂ) * Complex.I)) μ lam)
      atTop (𝓝 (harmonicPencil 1 0 μ lam)) :=
  normalizedDetector_tendsto e.cancel μ lam

/-- The limit pencil is rank-deficient. -/
theorem limit_pencil_singular (μ lam : ℂ) :
    ((harmonicPencil 1 0 μ lam)ᴴ * harmonicPencil 1 0 μ lam).det = 0 := by
  rw [Matrix.det_mul, harmonicPencil_det]
  simp

/-! ## 2. Every analytic zero is a limit focal event -/

/-- A zero of `L(χ, ·)` with `Re > 0` is a limit focal event of the character's routing law. -/
def LimitFocalEvent.ofLZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : 0 < ρ.re) (hz : DirichletCharacter.LFunction χ ρ = 0) : LimitFocalEvent where
  w := fun n => χ (n : ZMod q)
  σ := ρ.re
  y := ρ.im
  σ_pos := hρ
  cancel := by
    rw [Complex.re_add_im]
    exact (limit_chain_char χ hχ hρ 0 1 one_ne_zero).1.mpr hz

/-- A nontrivial ζ zero is a limit focal event of the η routing law. -/
def LimitFocalEvent.ofZetaZero (ρ : ℂ) (hρ : ρ ∈ ZD.NontrivialZeros) : LimitFocalEvent where
  w := Routing.eta.coeff
  σ := ρ.re
  y := ρ.im
  σ_pos := hρ.1
  cancel := by
    rw [Complex.re_add_im]
    exact (limit_chain_eta hρ.1 hρ.2.1 0 1 one_ne_zero).1.mpr hρ.2.2

/-- Conversely, a limit focal event of a character's routing law is a zero of `L(χ, ·)`. -/
theorem char_event_is_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (e : LimitFocalEvent) (hw : e.w = fun n : ℕ => χ (n : ZMod q)) :
    DirichletCharacter.LFunction χ ((e.σ : ℂ) + (e.y : ℂ) * Complex.I) = 0 := by
  have hre : 0 < ((e.σ : ℂ) + (e.y : ℂ) * Complex.I).re := by simpa using e.σ_pos
  have h := e.cancel
  rw [hw] at h
  exact (limit_chain_char χ hχ hre 0 1 one_ne_zero).1.mp h

/-! ## 3. Projection of the limit event -/

/-- The projected height of the limit event: its carrier point at ordinate `y`, radius and angle
dropped. -/
def LimitFocalEvent.height (e : LimitFocalEvent) : ℝ :=
  toHeight (toUnitCylinder (carrierState3D 1 3 e.y).point)

/-- The geometric readout of the limit event. -/
def LimitFocalEvent.readout (e : LimitFocalEvent) : ℝ × ℝ := (balanceExponent, e.height)

theorem LimitFocalEvent.height_eq (e : LimitFocalEvent) : e.height = Real.exp e.y := by
  rw [LimitFocalEvent.height, toHeight_toUnitCylinder]
  exact (carrierState3D 1 3 e.y).physicalHeight_eq_exp one_ne_zero

theorem LimitFocalEvent.readout_balanced (e : LimitFocalEvent) :
    CarrierScaleBalanced e.readout.1 ∧ ∀ σ : ℝ, CarrierScaleBalanced σ → σ = e.readout.1 :=
  ⟨carrierAbscissa_scaleBalanced, fun _ hσ =>
    exists_unique_carrierScaleBalanced.unique hσ carrierAbscissa_scaleBalanced⟩

/-- The readout does not see the amplitude exponent. -/
theorem LimitFocalEvent.readout_eq_of_y_eq {e e' : LimitFocalEvent} (h : e.y = e'.y) :
    e.readout = e'.readout := by
  unfold LimitFocalEvent.readout LimitFocalEvent.height
  rw [h]

/-- An attached L-zero reads out at its own ordinate's height. -/
theorem ofLZero_readout {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : 0 < ρ.re) (hz : DirichletCharacter.LFunction χ ρ = 0) :
    (LimitFocalEvent.ofLZero χ hχ ρ hρ hz).readout = (balanceExponent, Real.exp ρ.im) := by
  rw [LimitFocalEvent.readout, LimitFocalEvent.height_eq]
  rfl

/-! ## 4. The drift test -/

/-- **The proposition under test**: every limit focal event with routing law `w` is balanced.
Quantifies over the weak asymptotic type, factor-induced limit zeros included. It is not a
statement about physical focal events. -/
def CancellationForcesBalance (w : ℕ → ℂ) : Prop :=
  ∀ e : LimitFocalEvent, e.w = w → CarrierScaleBalanced e.σ

/-- **Exponent `1` is not balanced.** The site radius grows sublinearly (`R_n²/n` converges), so
`n^{−1}·R_n → 0`. -/
theorem not_balanced_one : ¬ CarrierScaleBalanced 1 := by
  rintro ⟨L, hL, hT⟩
  have hsq := Geometry.carrierRadius_sq_div_tendsto 1 3 (by norm_num)
  have hprod := hsq.mul tendsto_one_div_atTop_nhds_zero_nat
  rw [mul_zero] at hprod
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hprod
  rw [Real.sqrt_zero] at hsqrt
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ)) * Geometry.carrierRadius 1 3 n) atTop
      (𝓝 0) := by
    refine hsqrt.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hR := Geometry.carrierRadius_nonneg 1 3 n
    simp only [Function.comp_apply]
    rw [Real.rpow_neg_one, show Geometry.carrierRadius 1 3 n ^ 2 / (n : ℝ) * (1 / (n : ℝ)) =
      ((n : ℝ)⁻¹ * Geometry.carrierRadius 1 3 n) ^ 2 by field_simp]
    exact Real.sqrt_sq (mul_nonneg (inv_nonneg.mpr hnpos.le) hR)
  exact hL.ne' (tendsto_nhds_unique hT h0)

/-- The ordinate of the first dyadic cancellation of the η routing. -/
def dyadicOrdinate : ℝ := 2 * Real.pi / Real.log 2

theorem dyadicOrdinate_ne_zero : dyadicOrdinate ≠ 0 := by
  unfold dyadicOrdinate
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  positivity

/-- The η routing's dyadic factor vanishes at `1 + i·2π/log 2`. -/
theorem dyadic_factor_zero :
    (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - (((1 : ℝ) : ℂ) + (dyadicOrdinate : ℂ) * Complex.I)) = 0 := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos one_lt_two).ne'
  have hexp : (1 : ℂ) - (((1 : ℝ) : ℂ) + (dyadicOrdinate : ℂ) * Complex.I) =
      -((dyadicOrdinate : ℂ) * Complex.I) := by push_cast; ring
  rw [hexp, Complex.cpow_def_of_ne_zero two_ne_zero]
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hlog]
  have h2pi : (Real.log 2 : ℂ) * -((dyadicOrdinate : ℂ) * Complex.I) =
      -(2 * (Real.pi : ℂ) * Complex.I) := by
    unfold dyadicOrdinate
    push_cast
    field_simp
  rw [h2pi, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, sub_self]

/-- **The η grown fiber cancels in the limit at `σ = 1`, `y = 2π/log 2`.** -/
theorem etaFactorEvent_limit :
    Tendsto (fun Z => lawFiber Routing.eta.coeff Z
      (((1 : ℝ) : ℂ) + (dyadicOrdinate : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hre : 0 < ((((1 : ℝ) : ℂ) + (dyadicOrdinate : ℂ) * Complex.I)).re := by simp
  have hne : (((1 : ℝ) : ℂ) + (dyadicOrdinate : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact dyadicOrdinate_ne_zero this
  have h := lawFiber_eta_tendsto hre hne
  rwa [dyadic_factor_zero, zero_mul] at h

/-- **The counterexample event**: the η routing's dyadic limit cancellation. Factor-induced: the
conductor's fold multiplier `1 − 2^{1−s}` vanishes while the fiber's content does not cancel
(`etaFactorEvent_not_zeta_zero`). Legitimate for the weak asymptotic type; NOT a physical focal event,
and not to be used as a counterexample to claims about physical focal events. -/
def etaFactorEvent : LimitFocalEvent where
  w := Routing.eta.coeff
  σ := 1
  y := dyadicOrdinate
  σ_pos := one_pos
  cancel := etaFactorEvent_limit

/-- It is not an analytic ζ zero: ζ does not vanish at `1 + i·2π/log 2`. -/
theorem etaFactorEvent_not_zeta_zero :
    riemannZeta ((etaFactorEvent.σ : ℂ) + (etaFactorEvent.y : ℂ) * Complex.I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by simp [etaFactorEvent])

/-- **The proposition fails for the η routing.** Through the factor-induced witness only; it refutes
the overbroad predicate over the weak type, not any claim about physical focal events. -/
theorem not_cancellationForcesBalance_eta : ¬ CancellationForcesBalance Routing.eta.coeff :=
  fun h => not_balanced_one (h etaFactorEvent rfl)

/-- Its readout is that of every event at the same ordinate: the projection places this unbalanced
cancellation at the balance exponent. The readout's first coordinate is the constant `balanceExponent`
for every event, so this readout carries no information about the event's own exponent. -/
theorem etaFactorEvent_readout :
    etaFactorEvent.readout = (balanceExponent, Real.exp dyadicOrdinate) := by
  rw [LimitFocalEvent.readout, LimitFocalEvent.height_eq]
  rfl

end CriticalLinePhasor.LimitFocalEventNS

#print axioms CriticalLinePhasor.LimitFocalEventNS.LimitFocalEvent.detector_tendsto
#print axioms CriticalLinePhasor.LimitFocalEventNS.LimitFocalEvent.ofLZero
#print axioms CriticalLinePhasor.LimitFocalEventNS.LimitFocalEvent.ofZetaZero
#print axioms CriticalLinePhasor.LimitFocalEventNS.char_event_is_zero
#print axioms CriticalLinePhasor.LimitFocalEventNS.ofLZero_readout
#print axioms CriticalLinePhasor.LimitFocalEventNS.not_balanced_one
#print axioms CriticalLinePhasor.LimitFocalEventNS.etaFactorEvent_limit
#print axioms CriticalLinePhasor.LimitFocalEventNS.etaFactorEvent_not_zeta_zero
#print axioms CriticalLinePhasor.LimitFocalEventNS.not_cancellationForcesBalance_eta
#print axioms CriticalLinePhasor.LimitFocalEventNS.etaFactorEvent_readout
