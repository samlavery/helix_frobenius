import RequestProject.VonMangoldtEFStandalone
import RequestProject.HilbertPolyaResolventTrace

/-!
# The join: the seat's zeros and the explicit formula's zeros are one set

The corpus carries the von Mangoldt explicit formula
(`VMEFStandalone.vonMangoldt_explicit_formula`, `primeZeroDuality`, built on
`euler_pillar` and `bridge_pillar`) and, separately, the Hilbert–Pólya seat
machinery over `ZD.NontrivialZeros` with its resolvent trace
(`xi_logDeriv_two_point`). Both describe the SAME zeros in two vocabularies
that nothing connects.

This module supplies the join. The two zero sets are *definitionally* the
same — both unfold to `{s | 0 < Re s ∧ Re s < 1 ∧ riemannZeta s = 0}` — so
the identification is `rfl`, and every theorem stated over one set transports
to the other with no analytic cost.

Why it matters, rather than being bookkeeping: the seat criterion consumes
only the functional equation, discreteness, positive multiplicity and the
strip bound. Davenport–Heilbronn satisfies all four and has zeros off the
critical line, so no argument drawn from those inputs alone can close the
seat. Making the seat prime-aware is therefore necessary, and the explicit
formula is the only compiled object here that carries prime data. This join
is the first link.

Lives in its own module: `HilbertPolyaResolventTrace` and
`VonMangoldtEFStandalone` are both upstream of large subtrees and must not be
restaged (ledger 486).
-/

noncomputable section

namespace CriticalLinePhasor.DVP

/-- **The join.**  The explicit formula's zero set and the seat's zero set are
the same set of complex numbers. Both are, by definition,
`{s | 0 < Re s ∧ Re s < 1 ∧ riemannZeta s = 0}`. -/
theorem vmef_nontrivialZeros_eq_ZD :
    VMEFStandalone.NontrivialZeros = ZD.NontrivialZeros := rfl

/-- Membership transports from the explicit formula's vocabulary to the
seat's. -/
theorem mem_ZD_of_mem_vmef {ρ : ℂ} (h : ρ ∈ VMEFStandalone.NontrivialZeros) :
    ρ ∈ ZD.NontrivialZeros := h

/-- …and back. -/
theorem mem_vmef_of_mem_ZD {ρ : ℂ} (h : ρ ∈ ZD.NontrivialZeros) :
    ρ ∈ VMEFStandalone.NontrivialZeros := h

/-- **The seat's off-line witness, in the explicit formula's vocabulary.**
An off-line zero of the seat's set is an off-line zero of the explicit
formula's set, so the prime-side machinery applies to it verbatim. -/
theorem offLine_transports {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros)
    (hoff : ρ.re ≠ 1 / 2) :
    ρ ∈ VMEFStandalone.NontrivialZeros ∧ ρ.re ≠ 1 / 2 :=
  ⟨hρ, hoff⟩

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.vmef_nontrivialZeros_eq_ZD
#print axioms CriticalLinePhasor.DVP.mem_ZD_of_mem_vmef
#print axioms CriticalLinePhasor.DVP.offLine_transports
end AxiomAudit
