import RequestProject.HilbertPolyaCapstone
import RequestProject.SeatingLadderFold
import RequestProject.XiHadamardQuotient
import RequestProject.RiemannHypothesisBridge

/-!
# The receiver property, compiled region by region

Direct assault on D5's hypothesis (`IsSelfAdjointReceiver xiSpectralTrace`,
the box).  Compiled here:

* `xiSpectralTrace_continuousAt` — the trace is continuous wherever
  `ξ(1/2 + iz) ≠ 0`.
* `receiver_outside_wedge` — the receiver property HOLDS at every `z` off
  the real axis with `1/2 ≤ |Im z|` (the strip bound: `ξ`-zeros live in
  `0 < Re s < 1`) or `|Re z| ≤ 1269/2` (the compiled ladder).
* `receiver_of_wedge_regular` — **the box reduces to the wedge**: regularity
  on `{|Im z| < 1/2, |Re z| > 1269/2}` alone gives the full receiver.
* `rh_of_wedge_regular` — composed through the compiled capstone and
  bridge: wedge regularity ⟹ Mathlib's `RiemannHypothesis`.

Operator-register walk recorded (rule 9, encountered in construction): the
manifestly self-adjoint clock realization `⊕_p (−i d/dx on the log p
circle)` with the seat weight `n^{−1/2}` has its trace readout absolutely
convergent exactly on `1/2 < |Im z|` — the same exterior this file
compiles.  Every convergent prime presentation ends at the wedge's edge;
the wedge is the node, here as in every register.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

/-- The trace is continuous wherever `ξ(1/2 + iz)` does not vanish. -/
theorem xiSpectralTrace_continuousAt {z : ℂ}
    (hne : ZD.riemannXi (1 / 2 + Complex.I * z) ≠ 0) :
    ContinuousAt xiSpectralTrace z := by
  have hana : ∀ w : ℂ, AnalyticAt ℂ ZD.riemannXi w := fun w =>
    (ZD.riemannXi_differentiable.differentiableOn).analyticAt
      (isOpen_univ.mem_nhds trivial)
  have haff : ContinuousAt (fun z : ℂ => 1 / 2 + Complex.I * z) z :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  have hderiv : ContinuousAt (deriv ZD.riemannXi) (1 / 2 + Complex.I * z) :=
    ((hana _).deriv).continuousAt
  have hxi : ContinuousAt ZD.riemannXi (1 / 2 + Complex.I * z) :=
    (ZD.riemannXi_differentiable _).continuousAt
  have hlog : ContinuousAt (logDeriv ZD.riemannXi) (1 / 2 + Complex.I * z) := by
    have h := hderiv.div hxi hne
    simpa [logDeriv] using h
  have hcomp := ContinuousAt.comp (g := logDeriv ZD.riemannXi)
    (f := fun w : ℂ => 1 / 2 + Complex.I * w) hlog haff
  have hneg : ContinuousAt (fun w : ℂ =>
      -logDeriv ZD.riemannXi (1 / 2 + Complex.I * w)) z := hcomp.neg
  exact hneg

/-- **The receiver property outside the wedge**: regularity holds at every
off-axis `z` in the strip-bound region `1/2 ≤ |Im z|` and in the
ladder-verified region `|Re z| ≤ 1269/2`. -/
theorem receiver_outside_wedge (z : ℂ) (him : z.im ≠ 0)
    (hreg : 1 / 2 ≤ |z.im| ∨ |z.re| ≤ 1269 / 2) :
    ∃ L, Tendsto xiSpectralTrace (nhdsWithin z {z}ᶜ) (nhds L) := by
  have hsre : (1 / 2 + Complex.I * z).re = 1 / 2 - z.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have hsim : (1 / 2 + Complex.I * z).im = z.re := by
    simp [Complex.add_im, Complex.mul_im]
  have hne : ZD.riemannXi (1 / 2 + Complex.I * z) ≠ 0 := by
    intro h0
    have hmem := (ZD.riemannXi_eq_zero_iff _).mp h0
    rcases hreg with hband | hcap
    · rcases le_abs'.mp hband with hlo | hhi
      · have h1 : (1 : ℝ) ≤ (1 / 2 + Complex.I * z).re := by
          rw [hsre]; linarith
        have := hmem.2.1
        linarith
      · have h0' : (1 / 2 + Complex.I * z).re ≤ 0 := by
          rw [hsre]; linarith
        have := hmem.1
        linarith
    · have hon := CriticalLinePhasor.DVP.online_below_1269o2 _ hmem
        (by rw [hsim]; exact hcap)
      rw [hsre] at hon
      exact him (by linarith)
  exact ⟨xiSpectralTrace z,
    (xiSpectralTrace_continuousAt hne).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- **The box reduces to the wedge**: regularity of the trace on
`{0 < |Im z| < 1/2, |Re z| > 1269/2}` alone yields the full receiver
property — everything else is compiled. -/
theorem receiver_of_wedge_regular
    (h : ∀ z : ℂ, z.im ≠ 0 → |z.im| < 1 / 2 → 1269 / 2 < |z.re| →
      ∃ L, Tendsto xiSpectralTrace (nhdsWithin z {z}ᶜ) (nhds L)) :
    HelixLimit.IsSelfAdjointReceiver xiSpectralTrace := by
  intro z him
  by_cases hband : 1 / 2 ≤ |z.im|
  · exact receiver_outside_wedge z him (Or.inl hband)
  · by_cases hcap : |z.re| ≤ 1269 / 2
    · exact receiver_outside_wedge z him (Or.inr hcap)
    · push_neg at hband hcap
      exact h z him hband hcap

/-- **Wedge regularity ⟹ the Riemann Hypothesis** (exact Mathlib
proposition), through the compiled capstone and bridge. -/
theorem rh_of_wedge_regular
    (h : ∀ z : ℂ, z.im ≠ 0 → |z.im| < 1 / 2 → 1269 / 2 < |z.re| →
      ∃ L, Tendsto xiSpectralTrace (nhdsWithin z {z}ᶜ) (nhds L)) :
    RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh
    (rh_of_selfAdjointReceiver_xi (receiver_of_wedge_regular h))

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.receiver_outside_wedge
#print axioms CriticalLinePhasor.HilbertPolya.receiver_of_wedge_regular
#print axioms CriticalLinePhasor.HilbertPolya.rh_of_wedge_regular
