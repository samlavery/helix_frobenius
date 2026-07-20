import RequestProject.TransferContinuation
import RequestProject.LFunctionPhasor

/-!
# Audit of the warp-removal continuation step

The transfer theorem applies to the sequence whose primitive is bounded.  This file records a
separating instance: the constant coefficient bank becomes alternating after a unit warp, so the
warped primitive is bounded, while the original Dirichlet series still fails to be summable at
`s = 1/2`.  Thus a warp-removal theorem needs a quantitative hypothesis on the full removal
kernel; unit modulus and cell closure alone do not supply it.  (Ontology: a warp scales by a
*function*, a carrier scale by a harmonic *constant*; the reciprocal of a warp is again a warp,
so there is no separate "inverse warp" — removal is a kernel-transfer operation, not an
entity.) -/

namespace WarpRemovalTransferAudit

open Complex Finset

/-- The constant coefficient bank. -/
def coefficient (_n : ℕ) : ℂ := 1

/-- A period-two unit warp. -/
def alternatingWarp (n : ℕ) : ℂ := (-1 : ℂ) ^ (n + 1)

theorem alternatingWarp_norm (n : ℕ) : ‖alternatingWarp n‖ = 1 := by
  simp [alternatingWarp]

/-- Multiplying the constant bank by the alternating warp gives a bounded primitive. -/
theorem warped_primitive_bounded (N : ℕ) :
    ‖∑ n ∈ range N, coefficient n * alternatingWarp n‖ ≤ 1 := by
  simpa [coefficient, alternatingWarp] using
    CriticalLinePhasor.LFunctionPhasor.eta_partialSum_norm_le N

/-- At `s = 1/2`, the original (unwarped) shifted Dirichlet series is not summable. -/
theorem unwarped_half_not_summable :
    ¬ Summable (fun n : ℕ =>
      coefficient n * (((n + 1 : ℕ) : ℂ) ^ (-(1 / 2 : ℂ)))) := by
  have hbase :
      ¬ Summable (fun n : ℕ => 1 / ((n : ℂ) ^ (1 / 2 : ℂ))) := by
    rw [Complex.summable_one_div_nat_cpow]
    norm_num
  intro hshift
  apply hbase
  rw [← summable_nat_add_iff 1]
  simpa [coefficient, Complex.cpow_neg, div_eq_mul_inv] using hshift

end WarpRemovalTransferAudit

#print axioms WarpRemovalTransferAudit.alternatingWarp_norm
#print axioms WarpRemovalTransferAudit.warped_primitive_bounded
#print axioms WarpRemovalTransferAudit.unwarped_half_not_summable
