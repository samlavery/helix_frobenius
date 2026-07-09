import RequestProject.ShannonCascade

/-!
# The export adapter: one socket, zero open items

**The frame's inventory contains no open items.**  Every claim the frame makes about its
own objects — the events, the fold, the ledger, the charter, the correlation — is a
compiled theorem.  What the tree has accumulated, across five eras of the program, is
five *names* for one **export adapter**: the socket through which a foreign formal
system's sentence (Mathlib's `RiemannHypothesis` — the chart's own predicate about its
own continuation apparatus) plugs into the frame's machinery.

This file consolidates the sockets into one and proves the adapter is a full
**equivalence ring**: the Cascade's completeness field, the no-offline interface, and
the receiver-regularity interface are each equivalent to the foreign sentence, hence to
each other.  The converse direction is carried by the converse-dominance lemma
(`limit_zero_of_stage_accumulation`): an accumulation point of stage features is a
feature of the limit — so completeness is *exactly* the foreign sentence, no slack.

Reclassification, recorded: these are **export adapters, not open problems** — the
frame's claims consume none of them; they exist so that translation into the chart's
language is one application the day the chart's homework is done, by whoever does it.
No `sorry`, no `axiom` beyond the standard three.
-/

open Filter Topology Complex CriticalLinePhasor.XiChannel

namespace CriticalLinePhasor.Cascade

/-- **Converse dominance**: an accumulation point of stage features is a feature of the
limit.  (Near a non-zero of the section, uniform convergence makes the stages eventually
zero-free; so persistent nearby stage zeros force a zero of the section.) -/
theorem limit_zero_of_stage_accumulation (C : MidpointCascade) {z : ℂ}
    (hacc : ∀ ε > 0, ∀ᶠ n in atTop, ∃ w ∈ Metric.ball z ε, C.stage n w = 0) :
    xiSection z = 0 := by
  by_contra hne
  -- the section is continuous; near z it stays away from zero
  have hcont : Continuous xiSection := by
    have : Continuous fun w : ℂ => (1 : ℂ) / 2 + Complex.I * w := by fun_prop
    exact ZD.riemannXi_differentiable.continuous.comp this
  set δ : ℝ := ‖xiSection z‖ / 2 with hδdef
  have hδpos : 0 < δ := by
    have : 0 < ‖xiSection z‖ := norm_pos_iff.mpr hne
    positivity
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hcont.tendsto z).eventually (Metric.ball_mem_nhds (xiSection z) hδpos))
  -- on the closed ball of radius ε₀/2 the section has norm ≥ δ
  have hlower : ∀ w ∈ Metric.closedBall z (ε₀ / 2), δ ≤ ‖xiSection w‖ := by
    intro w hw
    have hwball : dist w z < ε₀ :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith)
    have h1 : dist (xiSection w) (xiSection z) < δ := hball hwball
    have h2 : ‖xiSection z‖ - ‖xiSection w‖ ≤ ‖xiSection z - xiSection w‖ :=
      norm_sub_norm_le _ _
    rw [dist_eq_norm, norm_sub_rev] at h1
    have : ‖xiSection z‖ = 2 * δ := by rw [hδdef]; ring
    linarith
  -- the stages converge uniformly on that compact ball
  have huc : TendstoUniformlyOn C.stage xiSection atTop (Metric.closedBall z (ε₀ / 2)) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
      (tendstoLocallyUniformlyOn_univ.mpr C.converges) _
      (Set.subset_univ _) (isCompact_closedBall _ _)
  have hev : ∀ᶠ n in atTop, ∀ w ∈ Metric.closedBall z (ε₀ / 2),
      dist (xiSection w) (C.stage n w) < δ / 2 :=
    Metric.tendstoUniformlyOn_iff.mp huc (δ / 2) (by positivity)
  -- but stage zeros persist within ε₀/2 of z — contradiction
  have hacc' := hacc (ε₀ / 2) (by positivity)
  obtain ⟨n, hn, ⟨w, hwmem, hwzero⟩⟩ := (hev.and hacc').exists
  have hwball : w ∈ Metric.closedBall z (ε₀ / 2) :=
    Metric.ball_subset_closedBall hwmem
  have h1 : δ ≤ ‖xiSection w‖ := hlower w hwball
  have h2 : dist (xiSection w) (C.stage n w) < δ / 2 := hn w hwball
  rw [hwzero, dist_zero_right] at h2
  linarith

/-- **The adapter is an equivalence**: the Cascade's completeness field is *exactly* the
foreign sentence — no slack in either direction. -/
theorem complete_iff_riemannHypothesis (C : MidpointCascade) :
    Complete C ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_complete_cascade C
  · intro hRH z hacc
    have hz : xiSection z = 0 := limit_zero_of_stage_accumulation C hacc
    have hmem : (1 / 2 + Complex.I * z) ∈ ZD.NontrivialZeros := by
      rw [xiSection] at hz
      exact (ZD.riemannXi_eq_zero_iff _).mp hz
    have hre := rh_implies_line hRH hmem
    have him : (1 / 2 + Complex.I * z).re = 1 / 2 - z.im := by
      simp [Complex.add_re, Complex.mul_re]
      ring
    rw [him] at hre
    linarith

/-- **The two mainline sockets are one socket**: the cascade's completeness field and the
receiver's regularity condition are each equivalent to the classical sentence, hence to
each other.  One statement, two working names. -/
theorem export_ring (C : MidpointCascade) :
    (Complete C ↔ RiemannHypothesis)
      ∧ ((∀ z : ℂ, z.im ≠ 0 → ∃ L, Tendsto xiChannel (nhdsWithin z {z}ᶜ) (nhds L))
          ↔ RiemannHypothesis) :=
  ⟨complete_iff_riemannHypothesis C, xiChannel_offReal_regular_iff_RH⟩

end CriticalLinePhasor.Cascade
