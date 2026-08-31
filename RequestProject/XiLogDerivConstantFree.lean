import RequestProject.SeatingFloorOdd
import RequestProject.HilbertPolyaResolventTrace

/-!
# The constant-free partial fraction: `P ≡ 0`, compiled

The Hadamard expansion of `ξ′/ξ` carries no entire remainder: evaluating
the compiled two-point identity at the mirror pair `(s, 1−s)` and using the
compiled oddness `ξ′/ξ(1−s) = −ξ′/ξ(s)` kills the constant exactly:

  `2·ξ′/ξ(s) = Σ_ρ m_ρ·((s−ρ)⁻¹ − ((1−s)−ρ)⁻¹)`.

This is the `P ≡ 0` step of the H₃ residual normal form: the analytic side
of `R` is pure zero packets, nothing entire left behind.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.HilbertPolya

/-- **The constant-free partial fraction** for the completed logarithmic
derivative: no entire remainder survives the mirror evaluation. -/
theorem xiLogDeriv_constant_free {s : ℂ}
    (hs : s ∉ ZD.NontrivialZeros) (hs' : (1 - s) ∉ ZD.NontrivialZeros) :
    2 * (deriv ZD.riemannXi s / ZD.riemannXi s)
      = ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ)
            * ((s - ρ.val)⁻¹ - ((1 - s) - ρ.val)⁻¹) := by
  have h2 := xi_logDeriv_two_point hs hs'
  have hodd := CriticalLinePhasor.SeatingLedger.xiLogDeriv_odd s
  rw [logDeriv_apply, logDeriv_apply] at hodd
  rw [hodd] at h2
  linear_combination h2

end CriticalLinePhasor.XiStructure

#print axioms CriticalLinePhasor.XiStructure.xiLogDeriv_constant_free
