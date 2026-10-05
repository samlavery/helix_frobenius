import RequestProject.HelixHeightDescent
import RequestProject.HelixHeightIntertwining

/-!
# The three discharge routes for full intertwining, each compiled exactly (ledger 598)

`helix-height-discharge-attempts.lean` tried three routes to
`Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1)`:

* **A. kernel descent** — `T f = 0 → T (L f) = 0`;
* **B. Green transport** — `⟪T (L f), T g⟫ = ⟪T f, T (L* g)⟫`;
* **C. symmetry of the ledger operator** — `L.IsSymmetric`.

Each failed at one tactic. None of the three is a tactic error: the intermediate claim in each case
puts every zero on the line, and the descent file already computes the exact defect on the
antisymmetric pair mode `single ρ 1 − single (1 − ρ̄) 1`:

* A fails by `T (L (difference mode)) = single (state) (−2i(Re ρ − ½))`
  (`zeroHeightCorrespondence_ledger_difference`);
* B fails by the Green defect `2i(Re ρ − ½)` (`zeroHeightCorrespondence_green_defect`);
* C fails because `L = height − i·drift` and `i·drift` is skew: the `−I = I` goal is `conj I = I`.

So each route, if it holds, puts every zero on the line; each is compiled below as a door
(`online_of_kernel_descent`, `online_of_green_transport`, `online_of_ledger_isSymmetric`).

The correspondence used here is built from the zeros (mode ρ ↦ carrier state at Im ρ), so its
intertwining defect is the drift Re ρ − ½ itself. The version that consumes the Euler product is the
fiber-built correspondence (HP_PROGRAM §1: modes to the prime-forced stations), whose intertwining
defect is the measured station residual consumed by `shadowing_implies_online_simple`. That is the
next object in this register.
-/

open Complex

namespace CriticalLinePhasor.XiChannel

open ThreeDFocal

/-- **A.** Kernel descent through the ledger operator puts every zero on the line. -/
theorem online_of_kernel_descent
    (H : ∀ f : XiZeroIndex →₀ ℂ, zeroHeightCorrespondence f = 0 →
        zeroHeightCorrespondence (xiZeroLedgerOperator f) = 0) :
    ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 := by
  intro ρ
  have h := H _ (zeroHeightCorrespondence_difference ρ)
  rw [zeroHeightCorrespondence_ledger_difference] at h
  have h1 := congrArg (fun F : CarrierThreeDMode 1 1 => F (carrierState3D 1 1 ρ.val.im)) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h1
  have h2 := congrArg Complex.im h1
  simp [Complex.mul_im] at h2
  linarith

/-- **B.** Green transport through the correspondence puts every zero on the line. -/
theorem online_of_green_transport
    (H : ∀ f g : XiZeroIndex →₀ ℂ,
        inner ℂ (zeroHeightCorrespondence (xiZeroLedgerOperator f)) (zeroHeightCorrespondence g)
          = inner ℂ (zeroHeightCorrespondence f)
              (zeroHeightCorrespondence (xiZeroLedgerFormalAdjoint g))) :
    ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 := by
  intro ρ
  have hd := zeroHeightCorrespondence_green_defect ρ
  rw [H (reflectedDifferenceMode ρ) (Finsupp.single ρ 1), sub_self] at hd
  have h2 := congrArg Complex.im hd
  simp [Complex.mul_im] at h2
  linarith

/-- **C.** Symmetry of the ledger operator puts every zero on the line. -/
theorem online_of_ledger_isSymmetric (hs : xiZeroLedgerOperator.IsSymmetric) :
    ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 := by
  intro ρ
  have hp := UnconditionalFrobenius.symmetric_eigenvalue_real hs
    (xiZeroLedgerOperator_hasEigenvalue ρ)
  rw [HelixLimit.poleParam_im] at hp
  linarith

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.online_of_kernel_descent
#print axioms CriticalLinePhasor.XiChannel.online_of_green_transport
#print axioms CriticalLinePhasor.XiChannel.online_of_ledger_isSymmetric
