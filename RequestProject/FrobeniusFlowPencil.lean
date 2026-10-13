import RequestProject.FocalQuotientFrobenius

/-!
# The harmonic pencil along the Frobenius flow, through the rank drop (ledger 1176)

The per-site Frobenius flow `frob t` (ledger 1175) moves the event's configuration: its resultant is
`B(t) = frozenSum e (y + t)` (the window frozen at the event's head, the spins at chart height `y + t`)
and its mass stays `M`. Fed to the detector, the flow gives the pencil family `H(t) = H(M, B(t))`.

* `flowB e t` and `flowB_eq`; `flowB_zero`: `B(0) = 0`.
* `flowPencil e t` (the detector fed the flow's channels): `flowPencil_eq` (`= H(M, B(t))`, the mass is
  constant), `flowPencil_zero` (at `t = 0` it is the event's detector), `flowPencil_det`
  (`det H(t) = (λ − μ)·M·B(t)`), `flowPencil_singular_iff` (singular exactly where `B(t) = 0`).
* `flowB_hasDerivAt_zero`: the crossing velocity `B'(0) = −i · Σ_k log(k+1) · c_k`.
* `frob_J`: `frob t ∘ J = J ∘ frob (−t)`; `antihelix_flowB`: the anti-helix flow resultant is
  `conj (B(−t))`; `antihelix_flowB_hasDerivAt_zero`: its crossing velocity is `−conj B'(0)`.

The flow freezes the window at the event's head; it agrees with the event family `y ↦ headSum (y)`
at `t = 0` only (`frozenSum_event`). Its other zeros are cancellations of this frozen configuration,
not focal events of the grown fiber.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.FrobeniusFlow

open CriticalLinePhasor CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.CancellationEigenstatePair
open CriticalLinePhasor.FocalFeet CriticalLinePhasor.FocalFeet.PhasorConfig CriticalLinePhasor.FocalQuotient
open CriticalLinePhasor.UnconditionalFrobenius

/-- The flow resultant `B(t)`: the resultant of the event's configuration after `frob t`. -/
def flowB (e : FocalEvent) (t : ℝ) : ℂ := (frob t (eventConfig e)).resultant

theorem flowB_eq (e : FocalEvent) (t : ℝ) : flowB e t = frozenSum e (e.y + t) :=
  frob_eventConfig_resultant e t

theorem flowB_zero (e : FocalEvent) : flowB e 0 = 0 := by
  rw [flowB_eq, add_zero, frozenSum_event]
  exact e.cancel

/-! ## The pencil family -/

/-- The detector fed the flow's channels (unsigned mass, resultant). -/
def flowPencil (e : FocalEvent) (t : ℝ) (μ lam : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  HarmonicCell.harmonicPencil (((frob t (eventConfig e)).mass : ℝ) : ℂ) (flowB e t) μ lam

theorem flowPencil_eq (e : FocalEvent) (t : ℝ) (μ lam : ℂ) :
    flowPencil e t μ lam = HarmonicCell.harmonicPencil ((eigenMass e : ℝ) : ℂ) (flowB e t) μ lam := by
  unfold flowPencil
  rw [frob_mass, mass_eventConfig]

/-- At `t = 0` the pencil is the event's detector. -/
theorem flowPencil_zero (e : FocalEvent) (μ lam : ℂ) :
    flowPencil e 0 μ lam = detector e.w e.a e.y μ lam := by
  rw [flowPencil_eq, flowB_zero, detector_at_event]

/-- **`det H(t) = (λ − μ)·M·B(t)`.** -/
theorem flowPencil_det (e : FocalEvent) (t : ℝ) (μ lam : ℂ) :
    (flowPencil e t μ lam).det = (lam - μ) * ((eigenMass e : ℝ) : ℂ) * flowB e t := by
  rw [flowPencil_eq, HarmonicCell.harmonicPencil_det]

/-- **The pencil is singular exactly where the flow resultant vanishes.** -/
theorem flowPencil_singular_iff (e : FocalEvent) (t : ℝ) {μ lam : ℂ} (hlam : lam ≠ μ) :
    (flowPencil e t μ lam).det = 0 ↔ flowB e t = 0 := by
  rw [flowPencil_det]
  have hM : ((eigenMass e : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (eigenMass_pos e).ne'
  have hl : lam - μ ≠ 0 := sub_ne_zero.mpr hlam
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hl hM)
  · intro h
    rw [h, mul_zero]

/-! ## The crossing velocity -/

theorem mellinSpin_eq_wave (u : ℝ) (n : ℕ) :
    LFunctionPhasor.mellinSpin u n = spectralWave (-Real.log n) u := by
  unfold LFunctionPhasor.mellinSpin spectralWave
  congr 1
  push_cast
  ring

/-- The crossing velocity: `−i · Σ_k log(k+1) · c_k`. -/
def crossingVelocity (e : FocalEvent) : ℂ :=
  -I * ∑ k ∈ Finset.range ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊,
    (Real.log ((k : ℝ) + 1) : ℂ) * cancellingPhasor e.w e.a e.y k

/-- **`B'(0)` is the crossing velocity.** -/
theorem flowB_hasDerivAt_zero (e : FocalEvent) : HasDerivAt (flowB e) (crossingVelocity e) 0 := by
  have hfun : flowB e = fun t => ∑ k ∈ Finset.range ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊,
      amplitude e k * spectralWave (-Real.log ((k : ℝ) + 1)) (e.y + t) := by
    funext t
    rw [flowB_eq, frozenSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mellinSpin_eq_wave, Nat.cast_add, Nat.cast_one]
  rw [hfun]
  have hk : ∀ k ∈ Finset.range ⌈CarrierHeadFiniteFiber.physicalHead e.y⌉₊,
      HasDerivAt (fun t => amplitude e k * spectralWave (-Real.log ((k : ℝ) + 1)) (e.y + t))
        (amplitude e k * ((((-Real.log ((k : ℝ) + 1)) : ℝ) : ℂ) * I *
          spectralWave (-Real.log ((k : ℝ) + 1)) (e.y + 0))) 0 := fun k _ =>
    ((spectralWave_hasDerivAt _ (e.y + 0)).comp_const_add e.y 0).const_mul (amplitude e k)
  convert HasDerivAt.fun_sum hk using 1
  rw [crossingVelocity, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : cancellingPhasor e.w e.a e.y k =
      amplitude e k * spectralWave (-Real.log ((k : ℝ) + 1)) e.y := by
    unfold cancellingPhasor amplitude
    rw [mellinSpin_eq_wave, Nat.cast_add, Nat.cast_one]
    ring
  rw [hc, add_zero]
  push_cast
  ring

/-! ## The anti-helix foot along the flow -/

/-- **The flow and J**: `frob t (J c) = J (frob (−t) c)`. -/
theorem frob_J (t : ℝ) (c : PhasorConfig) :
    frob t (PhasorConfig.J c) = PhasorConfig.J (frob (-t) c) := by
  simp only [frob, PhasorConfig.J, PhasorConfig.mk.injEq, true_and, heq_eq_eq]
  funext k
  rw [map_mul, TwoEndedJState.conj_mellinSpin, neg_neg]

/-- The anti-helix flow resultant is `conj (B(−t))`. -/
theorem antihelix_flowB (e : FocalEvent) (t : ℝ) :
    (frob t (PhasorConfig.J (eventConfig e))).resultant = (starRingEnd ℂ) (flowB e (-t)) := by
  rw [frob_J, resultant_J]
  rfl

/-- **The anti-helix crosses at the same parameter with velocity `−conj B'(0)`.** -/
theorem antihelix_flowB_hasDerivAt_zero (e : FocalEvent) :
    HasDerivAt (fun t => (frob t (PhasorConfig.J (eventConfig e))).resultant)
      (-(starRingEnd ℂ) (crossingVelocity e)) 0 := by
  have h1 : HasDerivAt (flowB e) (crossingVelocity e) (Neg.neg (0 : ℝ)) := by
    rw [neg_zero]
    exact flowB_hasDerivAt_zero e
  have h3 := (h1.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))).star
  convert h3 using 1
  · funext t
    rw [antihelix_flowB]
    rfl
  · rw [star_smul, star_trivial, neg_one_smul, starRingEnd_apply]

end CriticalLinePhasor.FrobeniusFlow

#print axioms CriticalLinePhasor.FrobeniusFlow.flowB_zero
#print axioms CriticalLinePhasor.FrobeniusFlow.flowPencil_zero
#print axioms CriticalLinePhasor.FrobeniusFlow.flowPencil_det
#print axioms CriticalLinePhasor.FrobeniusFlow.flowPencil_singular_iff
#print axioms CriticalLinePhasor.FrobeniusFlow.flowB_hasDerivAt_zero
#print axioms CriticalLinePhasor.FrobeniusFlow.frob_J
#print axioms CriticalLinePhasor.FrobeniusFlow.antihelix_flowB
#print axioms CriticalLinePhasor.FrobeniusFlow.antihelix_flowB_hasDerivAt_zero
