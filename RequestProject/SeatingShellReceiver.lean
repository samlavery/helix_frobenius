import RequestProject.SeatingShell
import RequestProject.HilbertPolyaCapstone

/-!
# The shell receiver: HP regularity on the thin shell alone forces RH

Crossing the compiled residual shell (`offline_depth_bound`) with the
localized HP receiver (`rh_of_high_receiver`): the boundary-limit hypothesis
on the ξ spectral trace is needed only at off-real spectral points that are
BOTH in the high band `|Re z| > 1269/2` AND inside the classical shell
`|Im z| < 1/2 − A/log⁹|Re z|` — a thin lens hugging the real axis, pinched
closed at rate `log⁻⁹`.  Everything outside the lens is compiled.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

open CriticalLinePhasor CriticalLinePhasor.HilbertPolya

/-- **RH from the shell receiver**: there is a compiled constant `A > 0` such
that boundary regularity of the ξ spectral trace at off-real points of the
thin shell `|Re z| > 1269/2`, `|Im z| < 1/2 − A/log⁹|Re z|` alone forces
every nontrivial zero onto the critical line. -/
theorem rh_of_shell_receiver :
    ∃ A : ℝ, 0 < A ∧
      ((∀ z : ℂ, z.im ≠ 0 → 1269/2 < |z.re| →
          |z.im| < 1/2 - A / (Real.log |z.re|)^9 →
          ∃ L, Tendsto xiSpectralTrace (nhdsWithin z {z}ᶜ) (nhds L)) →
        ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1/2) := by
  obtain ⟨A, hA0, _, hdepth⟩ := offline_depth_bound
  refine ⟨A, hA0, fun hsa ρ hρ => ?_⟩
  by_cases hlow : |ρ.im| ≤ 1269/2
  · exact CriticalLinePhasor.DVP.online_below_1269o2 ρ hρ hlow
  · push_neg at hlow
    by_contra hre
    have hmem := xi_spectralCoord_mem_singularSupport hρ
    have hre_calc : (spectralCoord ρ).re = ρ.im := by
      simp [spectralCoord, Complex.mul_re, Complex.sub_re, Complex.sub_im]
    have him_calc : (spectralCoord ρ).im = -(ρ.re - 1/2) := by
      simp [spectralCoord, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    have him : (spectralCoord ρ).im ≠ 0 := by
      rw [him_calc]
      intro h
      exact hre (by linarith)
    have hhigh : 1269/2 < |(spectralCoord ρ).re| := by
      rw [hre_calc]
      exact hlow
    have hshell : |(spectralCoord ρ).im|
        < 1/2 - A / (Real.log |(spectralCoord ρ).re|)^9 := by
      rw [him_calc, hre_calc, abs_neg]
      exact hdepth ρ hρ (by linarith)
    exact hmem (hsa _ him hhigh hshell)

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.rh_of_shell_receiver
