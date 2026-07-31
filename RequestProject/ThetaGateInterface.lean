import RequestProject.SchwarzAxisReality

/-!
# The typed gate-1 interface: the transfer exponent as a checkable hypothesis

Gate 1 of the two-gate reduction is the **transfer exponent**: a primitive bound
`‖∑_{k<n} a k‖ ≤ C·n^θ` with `θ < κ/2` — sub-random-walk cancellation strong enough to
carry both transfer continuations past the weld axis.  Until now "given gate 1" was
prose; this file makes it a type.

* `TransferGate a κ` — the typed gate: constant, exponent, nonnegativity, the sub-axis
  condition `θ < κ/2`, and the primitive bound.  `TransferGate.dual` shows the unitary
  dual carries the *same* gate for free (`dual_primitive_norm`) — one gate per rung, not
  two.
* `transferStrip θ κ` — the common analyticity strip `θ < Re s < κ − θ` of the two
  completed readouts: open, preconnected (convex), symmetric about the weld axis, stable
  under both the reflection `s ↦ κ − s` and conjugation.  `TransferGate.axis_mem_strip`:
  the gate places the axis inside.
* `AxisReality.differentiableOn_conj_conj` — Schwarz reflection preserves analyticity on
  any conjugation-stable open set.
* `AxisReality.fe_of_axisReality_on` — the identity-theorem engine generalized from `ℂ`
  to any open preconnected reflection- and conjugation-stable set containing the axis
  center: axis reality propagates to the reflection identity on the whole set.  The
  entire version (`fe_of_axisReality`) is the case `S = univ`.
* `TransferGate.fe_of_standingWave` — **the capstone: gate 1 typed ⟹ the per-rung FE
  on the strip is ONE real condition.**  Given a gate for the rung's coefficients, a
  chart factor `γ` analytic on the strip and Schwarz-real (`conj (γ s̄) = γ s` — the
  Γ/conductor factors of a completed chart), and the standing wave for the completed
  readout `Λ = γ·F` on the axis, the full functional equation
  `Λ(κ−s) = ε·(γ·F^∨)(s)` holds on the strip, with the dual readout `F^∨` the literal
  conjugated-coefficient continuation.  Nothing else is consumed: the Schwarz pairing of
  the Dirichlet layer is `abelContinuation_conj` (free), the dual gate is free, and the
  identity theorem runs on the gate's own strip.
* `unitGate` — non-vacuity: the delta sequence carries a gate at every `κ > 0`.

Scope: this file types and consumes gate 1; it does not discharge it for any CPS rung —
the per-fiber transfer exponent at `r ≥ 5` remains the named frontier input.  The
polynomial CPS coefficient bounds give only the trivial exponent `A + 1`, which is not
sub-axis.
-/

open Finset Filter Complex Topology ComplexConjugate

namespace CriticalLinePhasor.AxisReality

/-- Schwarz reflection preserves analyticity on a conjugation-stable open set. -/
theorem differentiableOn_conj_conj {f : ℂ → ℂ} {S : Set ℂ}
    (hSo : IsOpen S) (hSc : ∀ s ∈ S, conj s ∈ S)
    (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun s => conj (f (conj s))) S := by
  intro z hz
  have hd : DifferentiableAt ℂ f (conj z) :=
    (hf _ (hSc z hz)).differentiableAt (hSo.mem_nhds (hSc z hz))
  have h := hd.conj_conj
  rw [Complex.conj_conj] at h
  exact h.differentiableWithinAt

/-- **The axis-reality engine on a set**: on any open preconnected set containing the
axis center and stable under the reflection `s ↦ k − s` and conjugation, axis reality of
`G` propagates by the identity theorem to the full reflection identity.  The entire
version `fe_of_axisReality` is the case `S = univ`. -/
theorem fe_of_axisReality_on {G : ℂ → ℂ} (k : ℝ) (ε : ℂ) {S : Set ℂ}
    (hSo : IsOpen S) (hSp : IsPreconnected S) (hmem : ((k : ℂ) / 2) ∈ S)
    (hSrefl : ∀ s ∈ S, (k : ℂ) - s ∈ S) (hSconj : ∀ s ∈ S, conj s ∈ S)
    (hG : DifferentiableOn ℂ G S)
    (haxis : ∀ t : ℝ, G ((k : ℂ) / 2 + (t : ℂ) * I)
      = ε * conj (G ((k : ℂ) / 2 + (t : ℂ) * I))) :
    ∀ s ∈ S, G ((k : ℂ) - s) = ε * conj (G (conj s)) := by
  have hf : DifferentiableOn ℂ (fun s : ℂ => G ((k : ℂ) - s)) S := by
    intro z hz
    have haff : DifferentiableAt ℂ (fun s : ℂ => (k : ℂ) - s) z :=
      (differentiableAt_const _).sub differentiableAt_id
    exact ((hG _ (hSrefl z hz)).differentiableAt
      (hSo.mem_nhds (hSrefl z hz))).comp z haff |>.differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun s : ℂ => ε * conj (G (conj s))) S :=
    (differentiableOn_conj_conj hSo hSconj hG).const_mul ε
  have haxis' : ∀ t : ℝ, G ((k : ℂ) - ((k : ℂ) / 2 + (t : ℂ) * I))
      = ε * conj (G (conj ((k : ℂ) / 2 + (t : ℂ) * I))) := by
    intro t
    have h1 : (k : ℂ) - ((k : ℂ) / 2 + (t : ℂ) * I)
        = (k : ℂ) / 2 + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    have h2 : conj ((k : ℂ) / 2 + (t : ℂ) * I)
        = (k : ℂ) / 2 + ((-t : ℝ) : ℂ) * I := by
      have hsplit : (k : ℂ) / 2 + (t : ℂ) * I = ((k / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
        push_cast; ring
      rw [hsplit, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [h1, h2]
    exact haxis (-t)
  have hfreq : ∃ᶠ z in 𝓝[≠] ((k : ℂ) / 2),
      G ((k : ℂ) - z) = ε * conj (G (conj z)) := by
    have hmemne : ∀ n : ℕ,
        ((k : ℂ) / 2 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) ≠ (k : ℂ) / 2 := by
      intro n h
      have h' : (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) * I = 0 := by
        have hsub := congrArg (fun z => z - (k : ℂ) / 2) h
        simpa using hsub
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact Complex.ofReal_ne_zero.mpr (by positivity) h''
      · exact Complex.I_ne_zero h''
    have hlim : Tendsto
        (fun n : ℕ => (k : ℂ) / 2 + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)
        atTop (𝓝[≠] ((k : ℂ) / 2)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
            (𝓝 ((0 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto _).comp h0
        have h2 := (h1.mul_const I).const_add ((k : ℂ) / 2)
        simpa using h2
      · exact Eventually.of_forall fun n => hmemne n
    exact hlim.frequently (Frequently.of_forall fun n => haxis' _)
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (hf.analyticOnNhd hSo) (hg.analyticOnNhd hSo) hSp hmem hfreq
  exact fun s hs => hEq hs

end CriticalLinePhasor.AxisReality

namespace CriticalLinePhasor.GateInterface

open TransferContinuation CriticalLinePhasor.AxisReality

/-! ## The common strip -/

/-- The common analyticity strip of the two completed readouts: `θ < Re s < κ − θ`. -/
def transferStrip (θ κ : ℝ) : Set ℂ := {s : ℂ | θ < s.re ∧ s.re < κ - θ}

theorem isOpen_transferStrip (θ κ : ℝ) : IsOpen (transferStrip θ κ) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem convex_transferStrip (θ κ : ℝ) : Convex ℝ (transferStrip θ κ) :=
  (convex_halfSpace_re_gt θ).inter (convex_halfSpace_re_lt (κ - θ))

theorem isPreconnected_transferStrip (θ κ : ℝ) :
    IsPreconnected (transferStrip θ κ) :=
  (convex_transferStrip θ κ).isPreconnected

/-- The strip is stable under the completed reflection `s ↦ κ − s`. -/
theorem transferStrip_refl_mem {θ κ : ℝ} {s : ℂ} (hs : s ∈ transferStrip θ κ) :
    (κ : ℂ) - s ∈ transferStrip θ κ := by
  obtain ⟨h1, h2⟩ := hs
  constructor <;> simp only [Complex.sub_re, Complex.ofReal_re] <;> linarith

/-- The strip is stable under conjugation. -/
theorem transferStrip_conj_mem {θ κ : ℝ} {s : ℂ} (hs : s ∈ transferStrip θ κ) :
    conj s ∈ transferStrip θ κ := by
  obtain ⟨h1, h2⟩ := hs
  constructor <;> simpa using ‹_›

/-- The strip sits inside the primal continuation half-plane. -/
theorem transferStrip_subset_halfPlane (θ κ : ℝ) :
    transferStrip θ κ ⊆ {s : ℂ | θ < s.re} := fun _ hs => hs.1

/-! ## The typed gate -/

/-- **Gate 1, typed**: the transfer exponent of a rung.  A constant and an exponent with
the primitive bound `‖∑_{k<n} a k‖ ≤ C·n^θ` and the sub-axis condition `θ < κ/2` — the
cancellation strength that carries both transfer continuations past the weld axis. -/
structure TransferGate (a : ℕ → ℂ) (κ : ℝ) where
  C : ℝ
  θ : ℝ
  θ_nonneg : 0 ≤ θ
  θ_lt : θ < κ / 2
  primitive_bound : ∀ n : ℕ, ‖∑ k ∈ range n, a k‖ ≤ C * (n : ℝ) ^ θ

namespace TransferGate

variable {a : ℕ → ℂ} {κ : ℝ}

/-- **The unitary dual carries the same gate for free** (`dual_primitive_norm`): one
gate per rung, not two. -/
def dual (gate : TransferGate a κ) : TransferGate (fun n => conj (a n)) κ where
  C := gate.C
  θ := gate.θ
  θ_nonneg := gate.θ_nonneg
  θ_lt := gate.θ_lt
  primitive_bound := fun n => dual_primitive_bound gate.primitive_bound n

/-- The gate places the weld axis inside the common strip. -/
theorem axis_mem_strip (gate : TransferGate a κ) (t : ℝ) :
    ((κ : ℂ) / 2 + (t : ℂ) * I) ∈ transferStrip gate.θ κ := by
  have hre : ((κ : ℂ) / 2 + (t : ℂ) * I).re = κ / 2 := by simp
  constructor <;> rw [hre] <;> [exact gate.θ_lt; linarith [gate.θ_lt]]

/-- The strip center is in the strip. -/
theorem center_mem_strip (gate : TransferGate a κ) :
    ((κ : ℂ) / 2) ∈ transferStrip gate.θ κ := by
  have h := gate.axis_mem_strip 0
  simpa using h

/-- The primal transfer continuation is analytic past the axis. -/
theorem primal_differentiableOn (gate : TransferGate a κ) :
    DifferentiableOn ℂ (abelContinuation a) {s : ℂ | gate.θ < s.re} :=
  abelContinuation_differentiableOn a gate.C gate.θ gate.θ_nonneg gate.primitive_bound

/-- The dual transfer continuation is analytic past the axis — through the same gate. -/
theorem dual_differentiableOn (gate : TransferGate a κ) :
    DifferentiableOn ℂ (abelContinuation fun n => conj (a n)) {s : ℂ | gate.θ < s.re} :=
  gate.dual.primal_differentiableOn

/-- The Schwarz pairing at the gate: the dual continuation is the reflection of the
primal, everywhere (restatement of `abelContinuation_conj`). -/
theorem schwarz_pairing (_gate : TransferGate a κ) (s : ℂ) :
    abelContinuation (fun n => conj (a n)) s = conj (abelContinuation a (conj s)) :=
  abelContinuation_conj a s

/-- **The capstone: gate 1 typed ⟹ the per-rung FE on the strip is ONE real
condition.**  Given the gate, a chart factor `γ` analytic on the strip and Schwarz-real
(the Γ/conductor factors of a completed chart), and the standing wave for the completed
readout `Λ = γ·F` on the weld axis, the full functional equation holds on the strip
against the literal conjugated-coefficient dual readout.  Consumed: the gate, the chart
symmetry, one real condition.  Nothing else. -/
theorem fe_of_standingWave (gate : TransferGate a κ)
    (γ : ℂ → ℂ) (hγ : DifferentiableOn ℂ γ (transferStrip gate.θ κ))
    (hγs : ∀ s : ℂ, conj (γ (conj s)) = γ s) (ε : ℂ)
    (haxis : ∀ t : ℝ,
      γ ((κ : ℂ) / 2 + (t : ℂ) * I) * abelContinuation a ((κ : ℂ) / 2 + (t : ℂ) * I)
        = ε * conj (γ ((κ : ℂ) / 2 + (t : ℂ) * I) *
            abelContinuation a ((κ : ℂ) / 2 + (t : ℂ) * I))) :
    ∀ s ∈ transferStrip gate.θ κ,
      γ ((κ : ℂ) - s) * abelContinuation a ((κ : ℂ) - s) =
        ε * (γ s * abelContinuation (fun n => conj (a n)) s) := by
  set G : ℂ → ℂ := fun s => γ s * abelContinuation a s with hG
  have hGdiff : DifferentiableOn ℂ G (transferStrip gate.θ κ) :=
    hγ.mul (gate.primal_differentiableOn.mono (transferStrip_subset_halfPlane _ _))
  have hFE := fe_of_axisReality_on κ ε (isOpen_transferStrip gate.θ κ)
    (isPreconnected_transferStrip gate.θ κ) gate.center_mem_strip
    (fun s hs => transferStrip_refl_mem hs) (fun s hs => transferStrip_conj_mem hs)
    hGdiff haxis
  intro s hs
  have h := hFE s hs
  calc γ ((κ : ℂ) - s) * abelContinuation a ((κ : ℂ) - s)
      = ε * conj (G (conj s)) := h
    _ = ε * (conj (γ (conj s)) * conj (abelContinuation a (conj s))) := by
        rw [hG]; simp [map_mul]
    _ = ε * (γ s * abelContinuation (fun n => conj (a n)) s) := by
        rw [hγs s, ← abelContinuation_conj a s]

end TransferGate

/-! ## Non-vacuity -/

/-- The delta sequence: `1, 0, 0, …`. -/
def deltaSeq : ℕ → ℂ := fun n => if n = 0 then 1 else 0

/-- **Non-vacuity**: the delta sequence carries a gate at weight `1` — exponent `0`,
constant `1`. -/
noncomputable def unitGate : TransferGate deltaSeq 1 where
  C := 1
  θ := 0
  θ_nonneg := le_refl 0
  θ_lt := by norm_num
  primitive_bound := by
    intro n
    rw [Real.rpow_zero, mul_one]
    unfold deltaSeq
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hsum : (∑ k ∈ range n, if k = 0 then (1 : ℂ) else 0) = 1 := by
        rw [Finset.sum_ite_eq' (range n) 0 (fun _ => (1 : ℂ))]
        simp [Finset.mem_range, h]
      rw [hsum]
      simp

end CriticalLinePhasor.GateInterface

#print axioms CriticalLinePhasor.AxisReality.differentiableOn_conj_conj
#print axioms CriticalLinePhasor.AxisReality.fe_of_axisReality_on
#print axioms CriticalLinePhasor.GateInterface.TransferGate.dual
#print axioms CriticalLinePhasor.GateInterface.TransferGate.primal_differentiableOn
#print axioms CriticalLinePhasor.GateInterface.TransferGate.schwarz_pairing
#print axioms CriticalLinePhasor.GateInterface.TransferGate.fe_of_standingWave
#print axioms CriticalLinePhasor.GateInterface.unitGate
