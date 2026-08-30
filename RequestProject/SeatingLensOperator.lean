import RequestProject.SeatingShellReceiver

/-!
# The lens operator form: a C2 exhibit only needs to match on the lens

Pushing the shell localization through to the operator interface: a bounded
self-adjoint element of any C⋆-algebra, with any continuous readout whose
resolvent trace equals the ξ spectral trace **on the thin lens alone**
(`|Re z| > 1269/2`, `|Im z| < 1/2 − A/log⁹|Re z|`, off-real), forces the
Riemann Hypothesis.  The exhibit's burden shrinks accordingly: a candidate
operator may disagree with the trace everywhere outside the lens — at all
low heights and in the deep interior — and still finish.

Mechanism: the lens is open, so pointwise agreement on it is eventual
agreement at each of its off-real points; the resolvent readout's boundary
limits (earned from self-adjointness, `isSelfAdjointReceiver_resolventReadout`)
transfer to the ξ spectral trace along the punctured filters, which is the
compiled `rh_of_shell_receiver` hypothesis.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor CriticalLinePhasor.HilbertPolya HelixLimit

/-- **RH from a lens-matching operator**: there is a compiled `A > 0` such
that any self-adjoint C⋆-element whose continuous resolvent readout agrees
with the ξ spectral trace at off-real points of the thin lens
`|Re z| > 1269/2`, `|Im z| < 1/2 − A/log⁹|Re z|` forces every nontrivial
zero onto the critical line. -/
theorem rh_of_lens_resolventReadout
    {A : Type*} [CStarAlgebra A] {a : A}
    (ha : IsSelfAdjoint a) {φ : A → ℂ} (hφ : Continuous φ) :
    ∃ c : ℝ, 0 < c ∧
      ((∀ z : ℂ, z.im ≠ 0 → 1269/2 < |z.re| →
          |z.im| < 1/2 - c / (Real.log |z.re|)^9 →
          φ (resolvent a z) = xiSpectralTrace z) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨c, hc0, hc⟩ := rh_of_shell_receiver
  refine ⟨c, hc0, fun hid => hc ?_⟩
  intro z him hhigh hshell
  obtain ⟨L, hL⟩ := isSelfAdjointReceiver_resolventReadout ha hφ z him
  refine ⟨L, hL.congr' ?_⟩
  -- the three lens conditions are open at z, hence eventual near z
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
  have heq : ∀ᶠ w in nhdsWithin z {z}ᶜ,
      φ (resolvent a w) = xiSpectralTrace w := by
    have hall := (h1.and (h2.and h3)).filter_mono
      (nhdsWithin_le_nhds : nhdsWithin z {z}ᶜ ≤ nhds z)
    filter_upwards [hall] with w hw
    exact hid w hw.1 hw.2.1 hw.2.2
  exact heq

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.rh_of_lens_resolventReadout
