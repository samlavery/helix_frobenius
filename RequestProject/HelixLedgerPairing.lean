import RequestProject.HelixSymmetrizedLineTower

/-!
# The ledger pairing closed form and the FE order transport

Foundations for the `RH ⟹ hlim` converse — the direction that would certify the trace-limit
wall as exactly biconditional.  Two unconditional layers:

* **The pairing closed form** (`pairedLedgerTerm_closedForm`): the rotated Hadamard unit term
  collapses to a single quotient,
  `(z − poleParam ρ)⁻¹ + I/ρ = (½ + Iz)/((z − poleParam ρ)·ρ)`,
  by the identity `ρ + I(z − poleParam ρ) = ½ + Iz` — valid for *every* `ρ`, not only on-line.
  Its norm form (`norm_pairedLedgerTerm`) is the uniform-tail engine: on a compact off the real
  axis the numerator is bounded and the denominator grows like `|ρ|²`, which is exactly the
  shape the compiled majorant `summable_multi_weierstrassTerm_bound_aux` sums.

* **The FE order transport** (`xiOrderNat_one_sub`, `xiOrderNat_conj_of_re_half`): the compiled
  functional equation `ξ(1−s) = ξ(s)` transports the analytic multiplicity through the affine
  involution, so on the critical line — where `ρ̄ = 1 − ρ` — the conjugate partner carries the
  same multiplicity.  This is the accounting that matches the symmetrized tower's conjugate leg
  (which repeats the window multiplicity) with the ledger's own weight at the conjugate zero.

Register: everything here is unconditional; the `RH ⟹ hlim` assembly (index bijection under
RH, uniform tail summation, `tendstoUniformlyOn_tsum`) is the named remaining construction.
No RH/GRH is assumed anywhere in this file.
-/

open Complex Filter Topology

namespace CriticalLinePhasor.CaptureInterfaceAudit

/-! ## The pairing closed form -/

/-- The chart identity behind the Hadamard pairing: `ρ + I(z − poleParam ρ) = ½ + Iz`,
identically in `z` and `ρ`. -/
theorem add_I_mul_sub_poleParam (z ρ : ℂ) :
    ρ + Complex.I * (z - HelixLimit.poleParam ρ) = 1 / 2 + Complex.I * z := by
  unfold HelixLimit.poleParam
  linear_combination (-1 : ℂ) * Complex.re_add_im ρ +
    ((ρ.re : ℂ) - 1 / 2) * Complex.I_sq

/-- **The Hadamard pairing closed form**: the rotated ledger unit term is a single quotient.
Valid for every `ρ ≠ 0` and every `z` off the pole parameter — no zero-location input. -/
theorem pairedLedgerTerm_closedForm (z ρ : ℂ)
    (hz : z ≠ HelixLimit.poleParam ρ) (hρ : ρ ≠ 0) :
    (z - HelixLimit.poleParam ρ)⁻¹ + Complex.I / ρ =
      (1 / 2 + Complex.I * z) / ((z - HelixLimit.poleParam ρ) * ρ) := by
  have hsub : z - HelixLimit.poleParam ρ ≠ 0 := sub_ne_zero.mpr hz
  rw [eq_div_iff (mul_ne_zero hsub hρ), ← add_I_mul_sub_poleParam z ρ]
  field_simp

/-- **The uniform-tail engine**: the norm of the rotated ledger unit term is the bounded chart
numerator over the product of the pole distance and the zero's modulus. -/
theorem norm_pairedLedgerTerm (z ρ : ℂ)
    (hz : z ≠ HelixLimit.poleParam ρ) (hρ : ρ ≠ 0) :
    ‖(z - HelixLimit.poleParam ρ)⁻¹ + Complex.I / ρ‖ =
      ‖1 / 2 + Complex.I * z‖ / (‖z - HelixLimit.poleParam ρ‖ * ‖ρ‖) := by
  rw [pairedLedgerTerm_closedForm z ρ hz hρ, norm_div, norm_mul]

/-! ## The FE order transport -/

/-- **Multiplicity is invariant under the ξ functional equation**: the analytic order of ξ at
`1 − ρ` equals its order at `ρ`, by transporting the local factorization through the affine
involution `s ↦ 1 − s` and the compiled `ξ(1−s) = ξ(s)`. -/
theorem xiOrderNat_one_sub (ρ : ℂ) :
    ZD.xiOrderNat (1 - ρ) = ZD.xiOrderNat ρ := by
  have hana : ∀ w : ℂ, AnalyticAt ℂ ZD.riemannXi w := fun w =>
    ZD.riemannXi_differentiable.analyticAt w
  have hne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere
  obtain ⟨g, hg, hg0, hev⟩ :=
    ((hana ρ).analyticOrderNatAt_eq_iff (hne ρ)).mp rfl
  refine ((hana (1 - ρ)).analyticOrderNatAt_eq_iff (hne (1 - ρ))).mpr
    ⟨fun w => (-1 : ℂ) ^ ZD.xiOrderNat ρ * g (1 - w), ?_, ?_, ?_⟩
  · have hg' : AnalyticAt ℂ g ((fun w : ℂ => 1 - w) (1 - ρ)) := by
      simpa [sub_sub_cancel] using hg
    have h1 : AnalyticAt ℂ (fun w : ℂ => g (1 - w)) (1 - ρ) :=
      hg'.comp (analyticAt_const.sub analyticAt_id)
    exact analyticAt_const.mul h1
  · simp only [sub_sub_cancel]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hg0
  · have hcont : Tendsto (fun w : ℂ => 1 - w) (𝓝 (1 - ρ)) (𝓝 ρ) := by
      have h : Continuous fun w : ℂ => 1 - w := by fun_prop
      have h2 := h.tendsto (1 - ρ)
      simpa using h2
    filter_upwards [hcont.eventually hev] with w hw
    calc ZD.riemannXi w = ZD.riemannXi (1 - w) :=
          (ZD.ZeroCount.riemannXi_one_sub w).symm
      _ = ((1 - w) - ρ) ^ ZD.xiOrderNat ρ • g (1 - w) := hw
      _ = (w - (1 - ρ)) ^ ZD.xiOrderNat ρ •
            ((-1 : ℂ) ^ ZD.xiOrderNat ρ * g (1 - w)) := by
          simp only [smul_eq_mul]
          rw [show ((1 : ℂ) - w) - ρ = -(w - (1 - ρ)) by ring, neg_pow]
          ring

/-- On the critical line, conjugation is the functional-equation reflection. -/
theorem conj_eq_one_sub_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) :
    (starRingEnd ℂ) ρ = 1 - ρ := by
  apply Complex.ext
  · simp [h]
    norm_num
  · simp

/-- **The conjugate multiplicity law on the line**: for an on-line zero the conjugate partner
carries the same analytic multiplicity — the accounting that matches the symmetrized tower's
conjugate leg with the ledger's weight at the conjugate zero. -/
theorem xiOrderNat_conj_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) :
    ZD.xiOrderNat ((starRingEnd ℂ) ρ) = ZD.xiOrderNat ρ := by
  rw [conj_eq_one_sub_of_re_half h, xiOrderNat_one_sub]

end CriticalLinePhasor.CaptureInterfaceAudit

#print axioms CriticalLinePhasor.CaptureInterfaceAudit.add_I_mul_sub_poleParam
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.pairedLedgerTerm_closedForm
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.norm_pairedLedgerTerm
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.xiOrderNat_one_sub
#print axioms CriticalLinePhasor.CaptureInterfaceAudit.xiOrderNat_conj_of_re_half
