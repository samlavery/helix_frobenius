import RequestProject.SeatingLensGauge

/-!
# The Cayley lens form: hosting unbounded spectral height in a unitary

The diagonal candidate's spectrum — the zero ordinates — is unbounded along
`ℝ`, so a bounded self-adjoint element is the wrong host chart: its resolvent
readout is analytic beyond `‖a‖`, while the trace keeps resonating at every
height.  The Cayley chart `z ↦ (z−i)/(z+i)` compactifies exactly this: the
real axis goes to the unit circle, unbounded real spectrum becomes a bounded
UNITARY element, and unitarity's earned reality (`spectrum ⊆ circle`,
`isUnitaryReceiver_resolventReadout`, compiled) replaces self-adjointness.

`rh_of_lens_cayley_two_point` — a unitary `u` with continuous readout whose
Cayley-chart resolvent difference against one anchor equals the compiled
two-point resolvent sum over the actual zero multiset, on the thin lens
alone, forces RH.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor CriticalLinePhasor.HilbertPolya HelixLimit

/-- Off-real points leave the unit circle under the Cayley chart. -/
theorem cayley_off_circle {z : ℂ} (him : z.im ≠ 0)
    (hne : z + Complex.I ≠ 0) :
    ‖(z - Complex.I)/(z + Complex.I)‖ ≠ 1 := by
  rw [norm_div]
  intro h1
  have hden : ‖z + Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  rw [div_eq_one_iff_eq hden] at h1
  have h3 : Complex.normSq (z - Complex.I) = Complex.normSq (z + Complex.I) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h1]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im] at h3
  apply him
  linarith

/-- The Cayley chart carries the punctured filter at an off-`−i` point into
the punctured filter at its image (continuity + Möbius injectivity). -/
theorem cayley_tendsto_punctured {z : ℂ} (hne : z + Complex.I ≠ 0) :
    Tendsto (fun w : ℂ => (w - Complex.I)/(w + Complex.I))
      (nhdsWithin z {z}ᶜ)
      (nhdsWithin ((z - Complex.I)/(z + Complex.I))
        {(z - Complex.I)/(z + Complex.I)}ᶜ) := by
  have hCont : ContinuousAt (fun w : ℂ => (w - Complex.I)/(w + Complex.I)) z :=
    ContinuousAt.div ((continuous_id.sub continuous_const).continuousAt)
      ((continuous_id.add continuous_const).continuousAt) hne
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact hCont.tendsto.mono_left nhdsWithin_le_nhds
  · have h4 : ∀ᶠ w : ℂ in nhds z, w + Complex.I ≠ 0 :=
      (continuous_id.add continuous_const).continuousAt.eventually_ne hne
    filter_upwards [h4.filter_mono
      (nhdsWithin_le_nhds : nhdsWithin z {z}ᶜ ≤ nhds z),
      self_mem_nhdsWithin] with w hwI hwz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hwz ⊢
    intro hceq
    apply hwz
    have hcross : (w - Complex.I) * (z + Complex.I)
        = (z - Complex.I) * (w + Complex.I) :=
      (div_eq_div_iff hwI hne).mp hceq
    have h5 : Complex.I * w = Complex.I * z := by
      linear_combination (1/2 : ℂ) * hcross
    exact mul_left_cancel₀ Complex.I_ne_zero h5

/-- **RH from the Cayley two-point lens identity**: a unitary C⋆-element
whose Cayley-chart resolvent readout difference against one anchor equals
the compiled two-point resolvent sum over the actual zero multiset, on the
thin lens alone, forces every nontrivial zero onto the critical line. -/
theorem rh_of_lens_cayley_two_point
    {A : Type*} [CStarAlgebra A] {u : A} (hu : u ∈ unitary A)
    {φ : A → ℂ} (hφ : Continuous φ)
    {z₀ : ℂ} (hz₀ : (1/2 + Complex.I * z₀) ∉ ZD.NontrivialZeros) :
    ∃ c : ℝ, 0 < c ∧
      ((∀ z : ℂ, z.im ≠ 0 → 1269/2 < |z.re| →
          |z.im| < 1/2 - c / (Real.log |z.re|)^9 →
          φ (resolvent u ((z - Complex.I)/(z + Complex.I)))
            - φ (resolvent u ((z₀ - Complex.I)/(z₀ + Complex.I)))
            = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
                (ZD.xiOrderNat ρ.val : ℂ) *
                  ((spectralCoord ρ.val - z)⁻¹
                    - (spectralCoord ρ.val - z₀)⁻¹)) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨c, hc0, hc⟩ := rh_of_shell_receiver
  refine ⟨c, hc0, fun hid => hc ?_⟩
  intro z him hhigh hshell
  have hne : z + Complex.I ≠ 0 := by
    intro h0
    have hre0 : z.re = 0 := by
      have := congrArg Complex.re h0
      simpa using this
    rw [hre0] at hhigh
    norm_num at hhigh
  obtain ⟨L, hL⟩ := isUnitaryReceiver_resolventReadout hu hφ
    ((z - Complex.I)/(z + Complex.I)) (cayley_off_circle him hne)
  have hcomp : Tendsto
      (fun w : ℂ => φ (resolvent u ((w - Complex.I)/(w + Complex.I))))
      (nhdsWithin z {z}ᶜ) (nhds L) := by
    exact hL.comp (cayley_tendsto_punctured hne)
  refine ⟨-Complex.I * (L - φ (resolvent u ((z₀ - Complex.I)/(z₀ + Complex.I))))
    + xiSpectralTrace z₀, ?_⟩
  have hg : Tendsto
      (fun w : ℂ => -Complex.I *
          (φ (resolvent u ((w - Complex.I)/(w + Complex.I)))
            - φ (resolvent u ((z₀ - Complex.I)/(z₀ + Complex.I))))
        + xiSpectralTrace z₀)
      (nhdsWithin z {z}ᶜ)
      (nhds (-Complex.I *
          (L - φ (resolvent u ((z₀ - Complex.I)/(z₀ + Complex.I))))
        + xiSpectralTrace z₀)) :=
    ((hcomp.sub_const _).const_mul _).add_const _
  refine hg.congr' ?_
  filter_upwards [eventually_lens him hhigh hshell,
    eventually_offZeroImage z] with w hw hwz
  have key : φ (resolvent u ((w - Complex.I)/(w + Complex.I)))
      - φ (resolvent u ((z₀ - Complex.I)/(z₀ + Complex.I)))
      = Complex.I * xiSpectralTrace w - Complex.I * xiSpectralTrace z₀ := by
    rw [hid w hw.1 hw.2.1 hw.2.2, hilbertPolya_resolvent_trace hwz hz₀]
    simp only [xiSpectralTrace, logDeriv_apply]
    ring
  linear_combination (-Complex.I) * key
    - (xiSpectralTrace w - xiSpectralTrace z₀) * Complex.I_mul_I

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.cayley_off_circle
#print axioms CriticalLinePhasor.SeatingLedger.rh_of_lens_cayley_two_point
