import RequestProject.XiLogDerivConstantFree
import RequestProject.VonMangoldtEFStandalone

/-!
# The ledger balance, fully explicit: clock readings = focal census + carrier

The pointwise `W ≡ 0` identity in the resolvent register, with **no free
constant**.  On `Re s > 1` the fiber's clock ledger (the von Mangoldt
readout `L(Λ)`) balances exactly against the focal census (the mirror-pair
zero sum) plus the carrier's own ledger (the two ends `1/s + 1/(s−1)` and
the continuous winding `Γℝ′/Γℝ`):

  `2·L(Λ)(s) = −Σ_ρ m_ρ·((s−ρ)⁻¹ − ((1−s)−ρ)⁻¹)
                 + 2·(1/s + 1/(s−1) + Γℝ′/Γℝ(s))`.

Assembly of three compiled bricks and nothing else:
* `VMEFStandalone.euler_pillar` — `L(Λ) = −ζ′/ζ` (Mathlib);
* `VMEFStandalone.bridge_pillar` — the Γ/pole splice of `ξ′/ξ`;
* `XiStructure.xiLogDeriv_constant_free` — the mirror evaluation that
  kills the Hadamard constant (`P ≡ 0`).

The Gaussian-window harness (`tmp/att555_heat_balance.py`, residuals at
`1e−16`) measures the integral transform of exactly this identity; this is
its generating pointwise form, compiled.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.LedgerBalance

/-- **The constant-free ledger balance** on `Re s > 1`: prime clock
readings = mirror-pair focal census + the carrier's two ends + the
carrier's continuous winding.  Every term explicit; no existential
Hadamard constant. -/
theorem ledger_balance_constant_free (s : ℂ) (hs : 1 < s.re) :
    2 * LSeries (fun n => (VMEFStandalone.Λ n : ℂ)) s
      = -∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℂ)
              * ((s - ρ.val)⁻¹ - ((1 - s) - ρ.val)⁻¹)
        + 2 * (1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s) := by
  have hs0 : s ∉ ZD.NontrivialZeros := by
    intro h
    exact absurd h.2.1 (not_lt.mpr hs.le)
  have hs1 : (1 - s) ∉ ZD.NontrivialZeros := by
    intro h
    have hre : (1 - s).re = 1 - s.re := by simp [Complex.sub_re]
    have := h.1
    rw [hre] at this
    linarith
  have hcf := CriticalLinePhasor.XiStructure.xiLogDeriv_constant_free hs0 hs1
  have heu := VMEFStandalone.euler_pillar s hs
  have hbr := VMEFStandalone.bridge_pillar s hs
  have hxi : (VMEFStandalone.riemannXi : ℂ → ℂ) = ZD.riemannXi := rfl
  rw [hxi] at hbr
  linear_combination 2 * heu - 2 * hbr - hcf

end CriticalLinePhasor.LedgerBalance

#print axioms CriticalLinePhasor.LedgerBalance.ledger_balance_constant_free
