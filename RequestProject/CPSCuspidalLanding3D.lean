import RequestProject.CPSAdelicQuotient3D

/-!
# Cuspidal landing from the 3D unipotent channels

Cuspidality is expressed as vanishing of the constant term for every proper unipotent channel.
A nontrivial translation eigenmove in each channel kills all of these integrals simultaneously.
-/

namespace CriticalLinePhasor.ThreeDConverse

open MeasureTheory

/-- The constant term of a quotient readout along one unipotent channel. -/
noncomputable def unipotentConstantTerm
    {P Q : Type*} {U : P → Type*}
    [∀ p, MeasurableSpace (U p)]
    (μ : ∀ p, Measure (U p))
    (kernel : ∀ p, Q → U p → ℂ) (p : P) (q : Q) : ℂ :=
  ∫ u, kernel p q u ∂μ p

/-- Vanishing of every proper-unipotent constant term for a family of quotient readouts. -/
def CuspidalAlong3D
    {P Q : Type*} {U : P → Type*}
    [∀ p, MeasurableSpace (U p)]
    (μ : ∀ p, Measure (U p))
    (kernel : ∀ p, Q → U p → ℂ) : Prop :=
  ∀ p q, unipotentConstantTerm μ kernel p q = 0

/-- **Cuspidal 3D landing.** A nontrivial eigenmove on every proper unipotent channel forces all
constant terms of the quotient readout to vanish. -/
theorem cpsCuspidalAlong3D_of_nontrivialEigenmoves
    {P Q : Type*} {U : P → Type*}
    [∀ p, MeasurableSpace (U p)] [∀ p, Group (U p)]
    [∀ p, MeasurableMul (U p)] [∀ p, MeasurableInv (U p)]
    (μ : ∀ p, Measure (U p)) [∀ p, Measure.IsMulLeftInvariant (μ p)]
    (kernel : ∀ p, Q → U p → ℂ)
    (hintegrable : ∀ p q, Integrable (kernel p q) (μ p))
    (move : ∀ p, Q → U p) (eigenvalue : P → Q → ℂ)
    (heigen : ∀ p q u,
      kernel p q (move p q * u) = eigenvalue p q * kernel p q u)
    (hnontrivial : ∀ p q, eigenvalue p q ≠ 1) :
    CuspidalAlong3D μ kernel := by
  intro p q
  exact unipotentConstantTerm_eq_zero (μ p) (kernel p q) (hintegrable p q)
    (move p q) (eigenvalue p q) (heigen p q) (hnontrivial p q)

/-- A quotient readout pulled back along unipotent translations is a canonical constant-term
kernel. -/
def quotientUnipotentKernel
    {P Q : Type*} {U : P → Type*}
    (readout : Q → ℂ) (translate : ∀ p, Q → U p → Q) :
    ∀ p, Q → U p → ℂ :=
  fun p q u => readout (translate p q u)

/-- Cuspidality of a quotient readout follows directly from nontrivial eigenmoves of every pulled-
back unipotent channel. -/
theorem cpsQuotientReadout_cuspidalAlong3D
    {P Q : Type*} {U : P → Type*}
    [∀ p, MeasurableSpace (U p)] [∀ p, Group (U p)]
    [∀ p, MeasurableMul (U p)] [∀ p, MeasurableInv (U p)]
    (μ : ∀ p, Measure (U p)) [∀ p, Measure.IsMulLeftInvariant (μ p)]
    (readout : Q → ℂ) (translate : ∀ p, Q → U p → Q)
    (hintegrable : ∀ p q, Integrable (quotientUnipotentKernel readout translate p q) (μ p))
    (move : ∀ p, Q → U p) (eigenvalue : P → Q → ℂ)
    (heigen : ∀ p q u,
      readout (translate p q (move p q * u)) =
        eigenvalue p q * readout (translate p q u))
    (hnontrivial : ∀ p q, eigenvalue p q ≠ 1) :
    CuspidalAlong3D μ (quotientUnipotentKernel readout translate) := by
  exact cpsCuspidalAlong3D_of_nontrivialEigenmoves μ
    (quotientUnipotentKernel readout translate) hintegrable move eigenvalue heigen hnontrivial

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.cpsCuspidalAlong3D_of_nontrivialEigenmoves
#print axioms CriticalLinePhasor.ThreeDConverse.cpsQuotientReadout_cuspidalAlong3D
