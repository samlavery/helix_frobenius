import RequestProject.ExplicitAnchorDischarge

/-!
# Status of the staged bound, and the end atom that forbids a split estimate (ledger 635)

Two facts about the draft targets at `s₀ = −1 + 20i`.

* **The staged bound is not weaker.** `explicitCoeff_polynomial_bound_of_stage_bound` transfers a stage
  bound to the completed coefficients; conversely a completed bound gives a stage bound with the constant
  increased by one (`stage_bound_of_polynomial_bound`). Hence `stage_bound_iff_polynomial_bound`: Draft B's
  target is equivalent to Draft A's, not a weakening of it.

* **The two sides cannot be estimated separately.** The Archimedean side's atoms are the end `0` with
  residue `+1` and the Γ ticks `1 + 2n`, `n ≥ 1`, with residue `−1` (`jets_archSide_series`). At this anchor
  the ticks transport strictly inside the unit circle (`norm_transport_anchor_tick_lt_one`) but the end
  transports strictly outside: `‖transport s₀ 0‖ = √(1 + 3/401) > 1`
  (`one_lt_norm_transport_anchor_zero`). The end `0` is the reflected pole of `ζ` at `1`, and it is
  cancelled only by the divergence of the prime series at the reflected point. So any polynomial envelope
  must come from a paired estimate; a bound on `jets archSide` alone plus a bound on `jets primeSide`
  alone cannot produce one.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.SeatingLedger

/-- A completed polynomial bound gives a staged one, with the constant increased by one. -/
theorem stage_bound_of_polynomial_bound {C : ℝ} {p : ℕ}
    (hbound : ∀ k, ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤ C * (1 + (k : ℝ) ^ p)) :
    ∀ k, ∀ᶠ N in atTop, ‖explicitCoeffStage N k‖ ≤ (C + 1) * (1 + (k : ℝ) ^ p) := by
  intro k
  have hk : (1 : ℝ) ≤ 1 + (k : ℝ) ^ p := by
    have : (0 : ℝ) ≤ (k : ℝ) ^ p := by positivity
    linarith
  have hlt : ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ < (C + 1) * (1 + (k : ℝ) ^ p) := by
    calc ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤ C * (1 + (k : ℝ) ^ p) := hbound k
      _ < C * (1 + (k : ℝ) ^ p) + 1 := by linarith
      _ ≤ (C + 1) * (1 + (k : ℝ) ^ p) := by nlinarith
  exact ((explicitCoeffStage_tendsto k).norm.eventually_lt tendsto_const_nhds hlt).mono
    (fun N hN => hN.le)

/-- **Draft B's staged target is equivalent to Draft A's completed target.** -/
theorem stage_bound_iff_polynomial_bound :
    (∃ C : ℝ, ∃ p : ℕ, ∀ k, ∀ᶠ N in atTop,
      ‖explicitCoeffStage N k‖ ≤ C * (1 + (k : ℝ) ^ p))
    ↔ (∃ C : ℝ, ∃ p : ℕ, ∀ k,
      ‖toeplitzCoeff (-3) (jets explicitLogDeriv anchor20) k‖ ≤ C * (1 + (k : ℝ) ^ p)) := by
  constructor
  · rintro ⟨C, p, h⟩
    exact ⟨C, p, explicitCoeff_polynomial_bound_of_stage_bound h⟩
  · rintro ⟨C, p, h⟩
    exact ⟨C + 1, p, stage_bound_of_polynomial_bound h⟩

/-- **The Archimedean end atom transports strictly outside the unit circle.** -/
theorem one_lt_norm_transport_anchor_zero : 1 < ‖transport anchor20 0‖ := by
  have h : anchor20 - 0 ≠ 0 := by
    rw [sub_zero]
    intro h0
    have := congrArg Complex.re h0
    rw [anchor20_re] at this
    norm_num at this
  have hsq := norm_transport_sq anchor20 0 h
  rw [anchor20_re] at hsq
  have hns : Complex.normSq (anchor20 - 0) = 401 := by
    rw [sub_zero]
    unfold anchor20
    simp [Complex.normSq_apply]
    norm_num
  rw [hns] at hsq
  norm_num at hsq
  nlinarith [norm_nonneg (transport anchor20 0), hsq]

/-- **Every Γ tick transports strictly inside the unit circle.** -/
theorem norm_transport_anchor_tick_lt_one {a : ℝ} (ha : 1 ≤ a) :
    ‖transport anchor20 (a : ℂ)‖ < 1 := by
  have h : anchor20 - (a : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [Complex.sub_im, anchor20_im, Complex.ofReal_im] at this
    norm_num at this
  have hsq := norm_transport_sq anchor20 (a : ℂ) h
  rw [anchor20_re, Complex.ofReal_re] at hsq
  have hnpos : 0 < Complex.normSq (anchor20 - (a : ℂ)) := by rw [Complex.normSq_pos]; exact h
  have hneg : (2 * a - 1) * (2 * (-1 : ℝ) - 1) < 0 := by nlinarith
  have : ‖transport anchor20 (a : ℂ)‖ ^ 2 < 1 := by
    rw [hsq]
    have := div_neg_of_neg_of_pos hneg hnpos
    linarith
  nlinarith [norm_nonneg (transport anchor20 (a : ℂ))]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.stage_bound_iff_polynomial_bound
#print axioms CriticalLinePhasor.SeatingLedger.one_lt_norm_transport_anchor_zero
#print axioms CriticalLinePhasor.SeatingLedger.norm_transport_anchor_tick_lt_one
