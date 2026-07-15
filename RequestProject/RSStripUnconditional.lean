import RequestProject.RSIntegrable

/-!
# The strip side of Rankin–Selberg, unconditional

The capstone of slices five (a)–(d): with the integrability side condition discharged
(`rsIntegrand_product_integrable`), the strip side of the Rankin–Selberg integral is
unconditional on its natural half-planes:

* `rs_strip_side_mellin` (`Re s > 1`): `∫_{strip} P·(Im)^s dμ_ℍ = mellin R (s+k-1)` — the
  Rankin–Selberg integral over the translation domain *is* the Mellin transform of the exact
  energy readout;
* `rs_strip_side_dirichlet` (`Re s > 2`): `∫_{strip} P·(Im)^s dμ_ℍ =
  Γ(s+k-1)·∑' n, ‖a_n‖²/(4πn)^{s+k-1}` — and on the convergence half-plane it is the
  completed Rankin–Selberg Dirichlet series.

Combined with the compiled unfolding (`rs_unfolding`), the Dirichlet series equals the
Petersson–Eisenstein pairing `∑'_q ∫_𝒟 P·(Im γ_q·z)^s dμ`; transporting the strip
integrability to the tiling (`IsFundamentalDomain.integrableOn_iff` across the two compiled
domains) is the named next step, after which the equation holds with no side conditions at
all.  No RH/GRH.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup
open scoped Real MatrixGroups Pointwise NNReal

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound

variable {k : ℤ}

/-- **The strip side is the Mellin transform of the energy readout — unconditional** on
`Re s > 1`. -/
theorem rs_strip_side_mellin (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    ∫ z in strip, rsIntegrand f s z ∂(volume : Measure ℍ) =
      mellin (fun y : ℝ => ((∑' n : ℕ,
        ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ))
        (s + k - 1) :=
  rs_strip_side f hk s (rsIntegrand_product_integrable f hk hs)

/-- **The strip side is the completed Rankin–Selberg Dirichlet series — unconditional** on
`Re s > 2`. -/
theorem rs_strip_side_dirichlet (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ z in strip, rsIntegrand f s z ∂(volume : Measure ℍ) =
      Complex.Gamma (s + k - 1) * ∑' n : ℕ,
        ((‖(qExpansion 1 f).coeff n‖ ^ 2 : ℝ) : ℂ) /
          ((4 * π * n : ℝ) : ℂ) ^ (s + k - 1) :=
  rs_strip_side_eq_dirichlet f hk hs
    (rsIntegrand_product_integrable f hk (by linarith))

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.rs_strip_side_mellin
#print axioms CriticalLinePhasor.Unfolding.rs_strip_side_dirichlet
