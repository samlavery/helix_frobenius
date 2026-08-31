import RequestProject.XiStructureHBSeat

/-!
# The A-function of the warp structure is Ξ itself

`Acomp xiStructure z = ξ(½ − iz)` — exactly.  The de Branges A-function of
the warped structure function is the completed Ξ on the spectral chart, so
the HP identification target ("spectrum = zeros of A, with multiplicity")
is pinned to the right function by an identity, not a normalization
convention.

No `sorry`, no `axiom`.
-/

open Complex ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.XiStructure

open CriticalLinePhasor.DeBranges

/-- **A = Ξ**: the de Branges A-function of the warp structure function is
the completed ξ on the spectral chart. -/
theorem Acomp_xiStructure (z : ℂ) :
    Acomp xiStructure z = ZD.riemannXi (1/2 - Complex.I * z) := by
  unfold Acomp
  rw [estar_xiStructure]
  unfold xiStructure
  ring

/-- **B = −iξ′-chart**: the companion B-function is the chart derivative. -/
theorem Bcomp_xiStructure (z : ℂ) :
    Bcomp xiStructure z
      = Complex.I * deriv ZD.riemannXi (1/2 - Complex.I * z) := by
  unfold Bcomp
  rw [estar_xiStructure]
  unfold xiStructure
  ring

end CriticalLinePhasor.XiStructure

#print axioms CriticalLinePhasor.XiStructure.Acomp_xiStructure
#print axioms CriticalLinePhasor.XiStructure.Bcomp_xiStructure
