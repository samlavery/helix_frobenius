import RequestProject.QuadrupleFiber

/-!
# Even weight ⇔ DC channel: the parity law of the tensor clock

The grade-4 campaign's Lean brick (a).  A channel of the `g`-fold tensor of weight-1
`H¹`'s is a **sign vector** `ε ∈ {±1}^g`: each factor contributes one leg of its unit
conjugate pair `α^{±1}` (`curveFiber = symFiber 1`, exponent `1 - 2k` on the fiber index
`Fin 2`).  The channel's **clock frequency** is the sign sum `k = Σᵢ εᵢ` — in the Hodge
reading a channel of type `(p, q)` has `k = q - p = -Σᵢ εᵢ`, so frequency `0` names the
same lane in either sign convention: the middle `(m, m)` block, the **DC lane**.  The law,
a parity fact, proven here unconditionally:

  **the DC lane is inhabited iff the weight `g` is even.**

Balanced sign vectors exist iff `g` is even (`dc_channel_iff_even_weight`,
`dcLane_nonempty_iff_even`); for odd weight every channel is off-DC
(`no_dc_channel_of_odd`).  This is the clock face of the campaign's measured parity law —
"even-lane rungs carry the DC/ζ channel, odd-lane rungs are pole-free" — and of the
grade-4 wall dissolution, where the quadruple's `(2,2)` middle block exists exactly
because the weight `4` is even.  The channel decomposition ties the combinatorics to the
fiber weights: the diagonal readout of a channel is `α^{Σᵢ εᵢ}` (`channel_weight_prod`),
so the balanced lanes are exactly the weight-products whose conjugate legs pair off — the
DC lane carries the trivial weight `1` (`dc_channel_weight_trivial`,
`curveQuadFiber_dc_channel` at the degree-16 quadruple).

* `channelSign` / `channelSign_eq_one_or_neg_one` — the `±1` sign of a degree-2 channel
  index, the exponent of `symFiber 1`;
* `channelFreq` / `channelFreq_eq` — the clock frequency `Σᵢ εᵢ` and the bookkeeping
  `Σᵢ εᵢ = g - 2·(number of minus legs)`;
* `dc_channel_iff_even_weight` — **even weight ⇔ DC channel**, on the fiber index
  `Fin g → Fin 2`;
* `dcLane_nonempty_iff_even` — the same law for literal sign vectors `ε ∈ {±1}^g ⊂ ℤ`;
* `no_dc_channel_of_odd` — odd weight: no channel is DC;
* `channel_weight_prod` / `dc_channel_weight_trivial` — the channel decomposition: the
  diagonal weight-product of a channel is `α^{channelFreq ε}`, trivial on the DC lane;
* `grade4_dc_channel` / `grade5_no_dc_channel` — the instrument-measured instances: the
  quadruple (weight 4) has a DC channel, the quintuple (weight 5) has none;
* `curveQuadFiber_dc_channel` — the degree-16 fiber of `QuadrupleFiber` exhibits its DC
  channel: a balanced index whose diagonal weight is the trivial weight `1`.

**Scope.**  This is the combinatorial/model statement of the tensor clock decomposition:
sign-vector parity and the resulting weight-product identities on the finite fiber, nothing
more.  No Hodge-theoretic claim is made — the identification of the DC lane with algebraic
classes in the `(m, m)` block is the Hodge conjecture's territory and is neither assumed nor
proven; likewise nothing here assumes or proves RH/GRH.  (The converse of
`dc_channel_weight_trivial` — trivial weight only on the DC lane — holds for `α` of infinite
order and is not needed or claimed.)  No `axiom`, no `sorry`.
-/

open Complex Finset
open scoped BigOperators

namespace CriticalLinePhasor.EvenWeightDC

open CriticalLinePhasor.FiniteWeightFiber CriticalLinePhasor.QuadrupleFiber

/-- The **channel sign** of a degree-2 fiber index: `0 ↦ +1`, `1 ↦ -1` — the exponent
`1 - 2k` of the unit conjugate pair `symFiber 1` (weights `α^{+1}, α^{-1}`). -/
def channelSign (k : Fin 2) : ℤ := 1 - 2 * (k.val : ℤ)

/-- The channel sign is a sign: `channelSign k ∈ {±1}`. -/
theorem channelSign_eq_one_or_neg_one (k : Fin 2) :
    channelSign k = 1 ∨ channelSign k = -1 := by
  fin_cases k
  · left; rfl
  · right; rfl

/-- The **clock frequency** of a channel of the `g`-fold tensor of weight-1 conjugate
pairs: the sign sum `k = Σᵢ εᵢ` of its sign vector.  In the Hodge reading, `k = q - p` up
to overall sign; frequency `0` is the `(m, m)` middle block — the DC lane. -/
def channelFreq {g : ℕ} (ε : Fin g → Fin 2) : ℤ := ∑ i, channelSign (ε i)

/-- **The frequency bookkeeping**: `channelFreq ε = g - 2·(number of minus legs)` — the
sign sum measured from the all-plus channel, two per flipped leg. -/
theorem channelFreq_eq {g : ℕ} (ε : Fin g → Fin 2) :
    channelFreq ε = (g : ℤ) - 2 * ∑ i, ((ε i).val : ℤ) := by
  unfold channelFreq channelSign
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  simp

/-- **Even weight ⇔ DC channel** (the headline, on the fiber index).  The `g`-fold tensor
of weight-1 conjugate pairs has a channel of clock frequency `0` — a balanced sign vector,
the `(m, m)` middle block — **iff the weight `g` is even**.  Odd weight: the frequency is
always odd (`channelFreq_eq`), so the DC lane is empty.  Even weight `g = m + m`: pair the
legs, `m` plus and `m` minus, and the frequencies cancel exactly.  A parity fact,
unconditional. -/
theorem dc_channel_iff_even_weight (g : ℕ) :
    (∃ ε : Fin g → Fin 2, channelFreq ε = 0) ↔ Even g := by
  constructor
  · rintro ⟨ε, hε⟩
    rw [channelFreq_eq] at hε
    rw [Nat.even_iff]
    omega
  · rintro ⟨m, rfl⟩
    refine ⟨fun i => Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))
      (finSumFinEquiv.symm i), ?_⟩
    unfold channelFreq
    rw [← Equiv.sum_comp finSumFinEquiv (fun i => channelSign
      (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)) (finSumFinEquiv.symm i)))]
    simp [Fintype.sum_sum_type, channelSign]
    omega

/-- **Even weight ⇔ DC channel, sign-vector form**: a literal balanced sign vector
`ε ∈ {±1}^g ⊂ ℤ` (every entry `±1`, entries summing to `0`) exists iff the weight `g` is
even.  The same parity law as `dc_channel_iff_even_weight`, read on the signs themselves
rather than the fiber index. -/
theorem dcLane_nonempty_iff_even (g : ℕ) :
    (∃ ε : Fin g → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∑ i, ε i = 0) ↔ Even g := by
  constructor
  · rintro ⟨ε, hpm, hsum⟩
    refine (dc_channel_iff_even_weight g).mp
      ⟨fun i => if ε i = 1 then 0 else 1, ?_⟩
    unfold channelFreq
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hpm i with h | h
    · simp [h, channelSign]
    · simp [h, channelSign]
  · intro hg
    obtain ⟨ε, hε⟩ := (dc_channel_iff_even_weight g).mpr hg
    exact ⟨fun i => channelSign (ε i),
      fun i => channelSign_eq_one_or_neg_one (ε i), hε⟩

/-- **Odd weight has no DC channel**: for `g` odd, every channel's clock frequency is
nonzero — the middle block does not exist.  The pole-free/symplectic face of the parity
law. -/
theorem no_dc_channel_of_odd {g : ℕ} (hg : ¬ Even g) (ε : Fin g → Fin 2) :
    channelFreq ε ≠ 0 :=
  fun h => hg ((dc_channel_iff_even_weight g).mp ⟨ε, h⟩)

/-- **The channel decomposition** (the tie to the fiber weights): the diagonal readout of
a channel `ε` — the product over the legs of the conjugate-pair weight `curveFiber` picked
by `ε` — is `α^{channelFreq ε}`.  The clock frequency *is* the exponent of the channel's
weight-product; the balanced lanes are exactly the products whose conjugate legs pair
off. -/
theorem channel_weight_prod {g : ℕ} (α : ℂ) (hα : ‖α‖ = 1) (ε : Fin g → Fin 2) :
    ∏ i, (curveFiber α hα).weight (ε i) = α ^ channelFreq ε := by
  have h0 : α ≠ 0 := fun h => by simp [h] at hα
  have key : ∀ s : Finset (Fin g),
      ∏ i ∈ s, (curveFiber α hα).weight (ε i) = α ^ (∑ i ∈ s, channelSign (ε i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ h0, ih]
        rfl
  exact key Finset.univ

/-- **The DC lane carries the trivial weight**: on a balanced channel the diagonal
weight-product collapses to `1` — the ζ/DC channel of the even-weight tensor, exhibited on
the fiber. -/
theorem dc_channel_weight_trivial {g : ℕ} (α : ℂ) (hα : ‖α‖ = 1) (ε : Fin g → Fin 2)
    (h : channelFreq ε = 0) :
    ∏ i, (curveFiber α hα).weight (ε i) = 1 := by
  rw [channel_weight_prod α hα ε, h, zpow_zero]

/-- **Grade 4 has a DC channel**: weight `4` is even, so the quadruple's clock
decomposition contains the `(2, 2)` middle lane — the instrument-measured DC/ζ channel. -/
theorem grade4_dc_channel : ∃ ε : Fin 4 → Fin 2, channelFreq ε = 0 :=
  (dc_channel_iff_even_weight 4).mpr ⟨2, rfl⟩

/-- **Grade 5 has no DC channel**: weight `5` is odd, so every channel of the quintuple is
off-DC — the next rung is pole-free/symplectic, exactly the measured alternation. -/
theorem grade5_no_dc_channel (ε : Fin 5 → Fin 2) : channelFreq ε ≠ 0 :=
  no_dc_channel_of_odd (by decide) ε

/-- **The degree-16 quadruple exhibits its DC channel**: the balanced index
`((0, 1), (0, 1))` of `curveQuadFiber` — legs `α, α⁻¹, α, α⁻¹` — carries the trivial
weight `1` in the diagonal readout.  The concrete `(2, 2)`-lane witness on the fiber of
`QuadrupleFiber`, existing exactly because the weight `4` is even. -/
theorem curveQuadFiber_dc_channel (α : ℂ) (hα : ‖α‖ = 1) :
    ∃ p : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
      (curveQuadFiber α α α α hα hα hα hα).weight p = 1 := by
  have h0 : α ≠ 0 := fun h => by simp [h] at hα
  refine ⟨((0, 1), (0, 1)), ?_⟩
  show (quadFiber (curveFiber α hα) (curveFiber α hα) (curveFiber α hα) (curveFiber α hα)).weight
      ((0, 1), (0, 1)) = 1
  rw [quadFiber_weight]
  show α ^ ((1 : ℤ) - 2 * ((0 : Fin 2).val : ℤ)) * α ^ ((1 : ℤ) - 2 * ((1 : Fin 2).val : ℤ))
      * α ^ ((1 : ℤ) - 2 * ((0 : Fin 2).val : ℤ)) * α ^ ((1 : ℤ) - 2 * ((1 : Fin 2).val : ℤ)) = 1
  rw [← zpow_add₀ h0, ← zpow_add₀ h0, ← zpow_add₀ h0]
  norm_num

end CriticalLinePhasor.EvenWeightDC

#print axioms CriticalLinePhasor.EvenWeightDC.channelSign_eq_one_or_neg_one
#print axioms CriticalLinePhasor.EvenWeightDC.channelFreq_eq
#print axioms CriticalLinePhasor.EvenWeightDC.dc_channel_iff_even_weight
#print axioms CriticalLinePhasor.EvenWeightDC.dcLane_nonempty_iff_even
#print axioms CriticalLinePhasor.EvenWeightDC.no_dc_channel_of_odd
#print axioms CriticalLinePhasor.EvenWeightDC.channel_weight_prod
#print axioms CriticalLinePhasor.EvenWeightDC.dc_channel_weight_trivial
#print axioms CriticalLinePhasor.EvenWeightDC.grade4_dc_channel
#print axioms CriticalLinePhasor.EvenWeightDC.grade5_no_dc_channel
#print axioms CriticalLinePhasor.EvenWeightDC.curveQuadFiber_dc_channel
