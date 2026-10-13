import RequestProject.KleinEventBridge

/-!
# The cancellation is the gate (ledger 1161)

There is one physical fiber, the carrier's: its amplitude exponent is the carrier's balance exponent.
An event is an ordinate `y` at which that fiber cancels as the head climbs. That cancellation is the
gate; no other fiber, and no transverse parameter of an analytic zero, enters the geometry.

* The carrier's exponent without its value: `balanceExponent_pos` (from the radius growing without
  bound), `balanceExponent_ne_one` (from the radius growing sublinearly).
* `Gate w y`: the carrier's fiber of routing law `w` cancels in the limit at ordinate `y`.
  `gateEvent` is the corresponding limit focal event (exponent = the balance exponent).
* Verification only: `charGate_iff` (the gate ⟺ `L(χ, ·)` vanishes at `balanceExponent + iy` ⟺ the
  limit detector drops rank), `etaGate_iff` (the η gate ⟺ `ζ` vanishes there; the dyadic factor never
  vanishes on the carrier's fiber, `carrier_eta_no_dyadic`).
* `gateEvent_readout_faithful`: for gate events the projected readout is faithful. Its transverse
  component is the event's own exponent, and read back it gives the parameter of the vanishing it verifies.
* The control: `etaFactor_not_gate_event` (the η-factor event's fiber is not the carrier's), and no
  dyadic cancellation passes the η gate (`etaGate_iff`).
* Named and not assumed: `EveryZeroPassesGate χ` (every analytic zero is the parameter of a gate
  event), with `everyZeroPassesGate_iff`.

The balance exponent's value is used nowhere.
-/

open Complex Filter Topology
open scoped Matrix

noncomputable section

namespace CriticalLinePhasor.CarrierGate

open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.HarmonicCell
open CriticalLinePhasor.EisensteinWheelBank CriticalLinePhasor.FiberDetectorChain
open CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.LimitFocalEventNS

/-! ## The carrier's exponent, without its value -/

theorem balanceExponent_balanced : CarrierScaleBalanced balanceExponent :=
  carrierAbscissa_scaleBalanced

theorem balanceExponent_ne_one : balanceExponent ≠ 1 := fun h =>
  not_balanced_one (h ▸ balanceExponent_balanced)

/-- The balance exponent is positive: at a nonpositive exponent the fiber amplitude cannot hold back
a carrier radius that grows without bound. -/
theorem balanceExponent_pos : 0 < balanceExponent := by
  by_contra hle'
  have hle : balanceExponent ≤ 0 := not_lt.mp hle'
  obtain ⟨L, hL, hT⟩ := balanceExponent_balanced
  have hsq := Geometry.carrierRadius_sq_div_tendsto 1 3 (by norm_num)
  have hc : (3 : ℝ) * (Real.pi / 3) / Real.pi = 1 := by field_simp
  rw [hc] at hsq
  have h1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / 2 < Geometry.carrierRadius 1 3 n ^ 2 / n :=
    hsq.eventually (lt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-balanceExponent) * Geometry.carrierRadius 1 3 n < L + 1 :=
    hT.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := (h1.and (h2.and (eventually_ge_atTop 1))).exists_forall_of_atTop
  set n : ℕ := max N (⌈2 * (L + 1) ^ 2⌉₊ + 1) with hn
  obtain ⟨hA, hB, hC⟩ := hN n (le_max_left _ _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hC
  have hnpos : (0 : ℝ) < n := by linarith
  have hR := Geometry.carrierRadius_nonneg 1 3 n
  have hpow : 1 ≤ (n : ℝ) ^ (-balanceExponent) := Real.one_le_rpow hn1 (by linarith)
  have hRle : Geometry.carrierRadius 1 3 n < L + 1 := by nlinarith
  have hRsq : Geometry.carrierRadius 1 3 n ^ 2 < (L + 1) ^ 2 := by nlinarith
  have hlow : (n : ℝ) / 2 < Geometry.carrierRadius 1 3 n ^ 2 := by
    rw [lt_div_iff₀ hnpos] at hA
    linarith
  have hbig : 2 * (L + 1) ^ 2 < (n : ℝ) := by
    have h3 : (⌈2 * (L + 1) ^ 2⌉₊ + 1 : ℕ) ≤ n := le_max_right _ _
    have h4 : (2 * (L + 1) ^ 2 : ℝ) ≤ ⌈2 * (L + 1) ^ 2⌉₊ := Nat.le_ceil _
    have h5 : ((⌈2 * (L + 1) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h3
    push_cast at h5
    linarith
  linarith

/-! ## The gate -/

/-- **The gate**: the carrier's fiber of routing law `w` cancels in the limit at ordinate `y`. -/
def Gate (w : ℕ → ℂ) (y : ℝ) : Prop :=
  Tendsto (fun Z => lawFiber w Z ((balanceExponent : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0)

/-- The limit focal event of a gate passage. -/
def gateEvent (w : ℕ → ℂ) (y : ℝ) (h : Gate w y) : LimitFocalEvent where
  w := w
  σ := balanceExponent
  y := y
  σ_pos := balanceExponent_pos
  cancel := h

theorem carrierPoint_re_pos (y : ℝ) : 0 < ((balanceExponent : ℂ) + (y : ℂ) * Complex.I).re := by
  simpa using balanceExponent_pos

theorem carrierPoint_ne_one (y : ℝ) : ((balanceExponent : ℂ) + (y : ℂ) * Complex.I) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact balanceExponent_ne_one this

/-! ## Verification -/

/-- **The character gate** is the vanishing of `L(χ, ·)` at the carrier point, and the rank drop of
the limit detector there. -/
theorem charGate_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y : ℝ)
    (μ lam : ℂ) (hlam : lam ≠ μ) :
    (Gate (fun n : ℕ => χ (n : ZMod q)) y ↔
        DirichletCharacter.LFunction χ ((balanceExponent : ℂ) + (y : ℂ) * Complex.I) = 0) ∧
      (DirichletCharacter.LFunction χ ((balanceExponent : ℂ) + (y : ℂ) * Complex.I) = 0 ↔
        ((harmonicPencil 1 (DirichletCharacter.LFunction χ
            ((balanceExponent : ℂ) + (y : ℂ) * Complex.I)) μ lam)ᴴ *
          harmonicPencil 1 (DirichletCharacter.LFunction χ
            ((balanceExponent : ℂ) + (y : ℂ) * Complex.I)) μ lam).det = 0) := by
  have h := limit_chain_char χ hχ (carrierPoint_re_pos y) μ lam hlam
  exact ⟨h.1, h.2.1⟩

/-- **On the carrier's fiber the η routing's dyadic factor never vanishes.** -/
theorem carrier_eta_no_dyadic (y : ℝ) :
    (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - ((balanceExponent : ℂ) + (y : ℂ) * Complex.I)) ≠ 0 := by
  intro h
  have heq : (2 : ℂ) ^ ((1 : ℂ) - ((balanceExponent : ℂ) + (y : ℂ) * Complex.I)) = 1 :=
    (sub_eq_zero.mp h).symm
  have hnorm : ‖(2 : ℂ) ^ ((1 : ℂ) - ((balanceExponent : ℂ) + (y : ℂ) * Complex.I))‖ =
      (2 : ℝ) ^ (((1 : ℂ) - ((balanceExponent : ℂ) + (y : ℂ) * Complex.I)).re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    exact Complex.norm_cpow_eq_rpow_re_of_pos two_pos _
  rw [heq, norm_one] at hnorm
  have hre : ((1 : ℂ) - ((balanceExponent : ℂ) + (y : ℂ) * Complex.I)).re = 1 - balanceExponent := by
    simp
  rw [hre] at hnorm
  have h0 : (1 : ℝ) - balanceExponent = 0 := by
    have hl := congrArg Real.log hnorm
    rw [Real.log_one, Real.log_rpow two_pos] at hl
    rcases mul_eq_zero.mp hl.symm with h' | h'
    · exact h'
    · exact absurd h' (Real.log_pos one_lt_two).ne'
  exact balanceExponent_ne_one (by linarith)

/-- **The η gate** is the vanishing of `ζ` at the carrier point; no dyadic cancellation passes it. -/
theorem etaGate_iff (y : ℝ) :
    Gate Routing.eta.coeff y ↔ riemannZeta ((balanceExponent : ℂ) + (y : ℂ) * Complex.I) = 0 := by
  have h := lawFiber_eta_tendsto (carrierPoint_re_pos y) (carrierPoint_ne_one y)
  have hfac := carrier_eta_no_dyadic y
  constructor
  · intro h0
    exact (mul_eq_zero.mp (tendsto_nhds_unique h h0)).resolve_left hfac
  · intro hz
    unfold Gate
    rwa [hz, mul_zero] at h

/-! ## The readout of a gate event is faithful -/

theorem gateEvent_readout (w : ℕ → ℂ) (y : ℝ) (h : Gate w y) :
    (gateEvent w y h).readout = ((gateEvent w y h).σ, Real.exp y) := by
  rw [LimitFocalEvent.readout, LimitFocalEvent.height_eq]
  rfl

/-- **Faithful**: read back, the readout of a gate event is the parameter of the vanishing it
verifies. -/
theorem gateEvent_readout_faithful (w : ℕ → ℂ) (y : ℝ) (h : Gate w y) :
    (((gateEvent w y h).readout.1 : ℝ) : ℂ) + ((Real.log (gateEvent w y h).readout.2 : ℝ) : ℂ) *
        Complex.I = ((gateEvent w y h).σ : ℂ) + ((gateEvent w y h).y : ℂ) * Complex.I := by
  rw [gateEvent_readout, Real.log_exp]
  rfl

/-! ## The control -/

/-- The η-factor event's fiber is not the carrier's. (The η-factor event is a factor-induced limit zero of
the weak asymptotic type, not a physical focal event.) -/
theorem etaFactor_not_gate_event : etaFactorEvent.σ ≠ balanceExponent :=
  fun h => balanceExponent_ne_one h.symm

/-! ## Named, not assumed -/

/-- **Every analytic zero is the parameter of a gate event.** A coverage statement (cleanup, ledger 1237):
`Gate` is the drift-free routed fiber's limit closure, packaged as the weak asymptotic `LimitFocalEvent`.
It is not "the remaining theorem" and not a statement about the rich physical `FocalEvent`. -/
def EveryZeroPassesGate {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → DirichletCharacter.LFunction χ ρ = 0 →
    ∃ y : ℝ, Gate (fun n : ℕ => χ (n : ZMod q)) y ∧ (balanceExponent : ℂ) + (y : ℂ) * Complex.I = ρ

theorem everyZeroPassesGate_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    EveryZeroPassesGate χ ↔
      ∀ ρ : ℂ, 0 < ρ.re → DirichletCharacter.LFunction χ ρ = 0 → ρ.re = balanceExponent := by
  constructor
  · intro h ρ hρ hz
    obtain ⟨y, -, hy⟩ := h ρ hρ hz
    rw [← hy]
    simp
  · intro h ρ hρ hz
    refine ⟨ρ.im, ?_, ?_⟩
    · have hρeq : (balanceExponent : ℂ) + (ρ.im : ℂ) * Complex.I = ρ := by
        rw [← h ρ hρ hz, Complex.re_add_im]
      exact ((charGate_iff χ hχ ρ.im 0 1 one_ne_zero).1).mpr (by rw [hρeq]; exact hz)
    · rw [← h ρ hρ hz, Complex.re_add_im]

end CriticalLinePhasor.CarrierGate

#print axioms CriticalLinePhasor.CarrierGate.balanceExponent_pos
#print axioms CriticalLinePhasor.CarrierGate.charGate_iff
#print axioms CriticalLinePhasor.CarrierGate.carrier_eta_no_dyadic
#print axioms CriticalLinePhasor.CarrierGate.etaGate_iff
#print axioms CriticalLinePhasor.CarrierGate.gateEvent_readout_faithful
#print axioms CriticalLinePhasor.CarrierGate.etaFactor_not_gate_event
#print axioms CriticalLinePhasor.CarrierGate.everyZeroPassesGate_iff
