import RequestProject.SeatingLensOperator

/-!
# Gauge and two-point lens forms: the exhibit in the bridge's own shape

Two refinements of `rh_of_lens_resolventReadout`, matching the interface a
candidate operator built from the compiled Hadamard bridge
(`hilbertPolya_resolvent_trace`) satisfies natively:

* `rh_of_lens_resolventReadout_gauge` — the readout may differ from the ξ
  spectral trace by ANY fixed affine gauge `u·T + v` (`u ≠ 0`) on the lens.
* `rh_of_lens_resolvent_two_point` — the readout DIFFERENCE against one
  anchor point equals the compiled two-point resolvent sum over the actual
  zero multiset.  This is the exact compiled identity shape: an exhibit
  needs nothing but this one equation on the thin lens.

The two-point form needs a discreteness step: at a lens point that is
itself the spectral coordinate of a (hypothetical off-line) zero the bridge
identity is not available pointwise, but the zeros are locally finite, so
it is available eventually along the punctured filter — which is all the
limit transfer uses.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor CriticalLinePhasor.HilbertPolya HelixLimit

/-- The three lens conditions are open at any of their points, hence hold
eventually along the punctured filter. -/
theorem eventually_lens {c : ℝ} {z : ℂ} (him : z.im ≠ 0)
    (hhigh : 1269/2 < |z.re|)
    (hshell : |z.im| < 1/2 - c / (Real.log |z.re|)^9) :
    ∀ᶠ w : ℂ in nhdsWithin z {z}ᶜ,
      w.im ≠ 0 ∧ 1269/2 < |w.re| ∧
        |w.im| < 1/2 - c / (Real.log |w.re|)^9 := by
  have h1 : ∀ᶠ w : ℂ in nhds z, w.im ≠ 0 :=
    Complex.continuous_im.continuousAt.eventually_ne him
  have h2 : ∀ᶠ w : ℂ in nhds z, 1269/2 < |w.re| :=
    continuousAt_const.eventually_lt
      (Complex.continuous_re.abs.continuousAt) hhigh
  have h3 : ∀ᶠ w : ℂ in nhds z, |w.im| < 1/2 - c / (Real.log |w.re|)^9 := by
    have habs : ContinuousAt (fun w : ℂ => |w.re|) z :=
      Complex.continuous_re.abs.continuousAt
    have hlogpos : 0 < Real.log |z.re| :=
      Real.log_pos (by linarith)
    have hlog : ContinuousAt (fun w : ℂ => Real.log |w.re|) z :=
      (Real.continuousAt_log (by positivity)).comp habs
    have hden : ContinuousAt (fun w : ℂ => (Real.log |w.re|)^9) z :=
      hlog.pow 9
    have hdne : (Real.log |z.re|)^9 ≠ 0 := by positivity
    have hquot : ContinuousAt (fun w : ℂ => c / (Real.log |w.re|)^9) z :=
      continuousAt_const.div hden hdne
    have hrhs : ContinuousAt
        (fun w : ℂ => 1/2 - c / (Real.log |w.re|)^9) z :=
      continuousAt_const.sub hquot
    have hlhs : ContinuousAt (fun w : ℂ => |w.im|) z :=
      Complex.continuous_im.abs.continuousAt
    exact hlhs.eventually_lt hrhs hshell
  exact ((h1.and (h2.and h3)).filter_mono
    (nhdsWithin_le_nhds : nhdsWithin z {z}ᶜ ≤ nhds z))

/-- **RH from a gauge-matching operator**: the readout need only equal
`u · xiSpectralTrace + v` on the lens, for any fixed gauge `u ≠ 0, v`. -/
theorem rh_of_lens_resolventReadout_gauge
    {A : Type*} [CStarAlgebra A] {a : A}
    (ha : IsSelfAdjoint a) {φ : A → ℂ} (hφ : Continuous φ)
    (u v : ℂ) (hu : u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ((∀ z : ℂ, z.im ≠ 0 → 1269/2 < |z.re| →
          |z.im| < 1/2 - c / (Real.log |z.re|)^9 →
          φ (resolvent a z) = u * xiSpectralTrace z + v) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨c, hc0, hc⟩ := rh_of_shell_receiver
  refine ⟨c, hc0, fun hid => hc ?_⟩
  intro z him hhigh hshell
  obtain ⟨L, hL⟩ := isSelfAdjointReceiver_resolventReadout ha hφ z him
  refine ⟨(L - v) / u, ?_⟩
  have hg : Tendsto (fun w => (φ (resolvent a w) - v) / u)
      (nhdsWithin z {z}ᶜ) (nhds ((L - v) / u)) :=
    (hL.sub_const _).div_const _
  refine hg.congr' ?_
  filter_upwards [eventually_lens him hhigh hshell] with w hw
  rw [hid w hw.1 hw.2.1 hw.2.2, add_sub_cancel_right,
    mul_div_cancel_left₀ _ hu]

/-- **Discreteness of the zero image on the chart**: along the punctured
filter at any `z`, the chart point `½ + iw` eventually avoids the zero set
(the zeros are locally finite). -/
theorem eventually_offZeroImage (z : ℂ) :
    ∀ᶠ w : ℂ in nhdsWithin z {z}ᶜ,
      (1/2 + Complex.I * w) ∉ ZD.NontrivialZeros := by
  set s : ℂ → ℂ := fun w => 1/2 + Complex.I * w with hs
  have hs_cont : Continuous s :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hfin : (ZD.NontrivialZeros ∩
      Metric.closedBall 0 (‖s z‖ + 1)).Finite :=
    ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite _
  set G : Set ℂ := s ⁻¹' (ZD.NontrivialZeros ∩
    Metric.closedBall 0 (‖s z‖ + 1)) with hG
  have hinj : Set.InjOn s (s ⁻¹' (ZD.NontrivialZeros ∩
      Metric.closedBall 0 (‖s z‖ + 1))) := by
    intro w₁ _ w₂ _ h
    have h' : (1 : ℂ)/2 + Complex.I * w₁ = 1/2 + Complex.I * w₂ := h
    exact mul_left_cancel₀ Complex.I_ne_zero (add_left_cancel h')
  have hGfin : G.Finite := hfin.preimage hinj
  have hG'closed : IsClosed (G \ {z}) := (hGfin.diff).isClosed
  have hzc : z ∈ (G \ {z})ᶜ := by simp
  have hev : ∀ᶠ w : ℂ in nhds z, w ∈ (G \ {z})ᶜ :=
    hG'closed.isOpen_compl.eventually_mem hzc
  have hball : ∀ᶠ w : ℂ in nhds z, s w ∈ Metric.ball (s z) 1 :=
    hs_cont.continuousAt.eventually_mem (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [(hev.and hball).filter_mono
    (nhdsWithin_le_nhds : nhdsWithin z {z}ᶜ ≤ nhds z),
    self_mem_nhdsWithin] with w hw hwne
  intro hzero
  apply hw.1
  refine ⟨⟨hzero, ?_⟩, hwne⟩
  rw [Metric.mem_closedBall]
  calc dist (s w) 0
      ≤ dist (s w) (s z) + dist (s z) 0 := dist_triangle _ _ _
    _ ≤ 1 + ‖s z‖ := by
        have hb := hw.2
        rw [Metric.mem_ball] at hb
        rw [dist_zero_right]
        linarith
    _ = ‖s z‖ + 1 := by ring

/-- **RH from the two-point lens identity** — the exhibit in the compiled
bridge's own shape: a self-adjoint C⋆-element whose readout difference
against one anchor equals the two-point resolvent sum over the actual zero
multiset, on the thin lens alone, forces RH. -/
theorem rh_of_lens_resolvent_two_point
    {A : Type*} [CStarAlgebra A] {a : A}
    (ha : IsSelfAdjoint a) {φ : A → ℂ} (hφ : Continuous φ)
    {z₀ : ℂ} (hz₀ : (1/2 + Complex.I * z₀) ∉ ZD.NontrivialZeros) :
    ∃ c : ℝ, 0 < c ∧
      ((∀ z : ℂ, z.im ≠ 0 → 1269/2 < |z.re| →
          |z.im| < 1/2 - c / (Real.log |z.re|)^9 →
          φ (resolvent a z) - φ (resolvent a z₀)
            = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
                (ZD.xiOrderNat ρ.val : ℂ) *
                  ((spectralCoord ρ.val - z)⁻¹
                    - (spectralCoord ρ.val - z₀)⁻¹)) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨c, hc0, hc⟩ := rh_of_shell_receiver
  refine ⟨c, hc0, fun hid => hc ?_⟩
  intro z him hhigh hshell
  obtain ⟨L, hL⟩ := isSelfAdjointReceiver_resolventReadout ha hφ z him
  refine ⟨-Complex.I * (L - φ (resolvent a z₀)) + xiSpectralTrace z₀, ?_⟩
  have hg : Tendsto
      (fun w => -Complex.I * (φ (resolvent a w) - φ (resolvent a z₀))
        + xiSpectralTrace z₀)
      (nhdsWithin z {z}ᶜ)
      (nhds (-Complex.I * (L - φ (resolvent a z₀)) + xiSpectralTrace z₀)) :=
    ((hL.sub_const _).const_mul _).add_const _
  refine hg.congr' ?_
  filter_upwards [eventually_lens him hhigh hshell,
    eventually_offZeroImage z] with w hw hwz
  have key : φ (resolvent a w) - φ (resolvent a z₀)
      = Complex.I * xiSpectralTrace w - Complex.I * xiSpectralTrace z₀ := by
    rw [hid w hw.1 hw.2.1 hw.2.2, hilbertPolya_resolvent_trace hwz hz₀]
    simp only [xiSpectralTrace, logDeriv_apply]
    ring
  linear_combination (-Complex.I) * key
    - (xiSpectralTrace w - xiSpectralTrace z₀) * Complex.I_mul_I

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.rh_of_lens_resolventReadout_gauge
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_lens_resolvent_two_point
