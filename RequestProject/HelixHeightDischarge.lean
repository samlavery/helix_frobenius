import RequestProject.HelixHeightDescent
import RequestProject.HelixHeightIntertwining

/-!
# The three discharge routes for full intertwining, each compiled exactly (ledger 598)

`helix-height-discharge-attempts.lean` tried three routes to
`Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1)`:

* **A. kernel descent** — `T f = 0 → T (L f) = 0`;
* **B. Green transport** — `⟪T (L f), T g⟫ = ⟪T f, T (L* g)⟫`;
* **C. symmetry of the ledger operator** — `L.IsSymmetric`.

Each failed at one tactic. None of the three is a tactic error: the intermediate claim is, in each
case, equivalent to every zero lying on the line, and the descent file already computes the exact
defect on the antisymmetric pair mode `single ρ 1 − single (1 − ρ̄) 1`:

* A fails by `T (L (difference mode)) = single (state) (−2i(Re ρ − ½))`
  (`zeroHeightCorrespondence_ledger_difference`);
* B fails by the Green defect `2i(Re ρ − ½)` (`zeroHeightCorrespondence_green_defect`);
* C fails because `L = height − i·drift` and `i·drift` is skew: the `−I = I` goal is `conj I = I`.

So the three routes are three more coordinates on the same statement, and each is compiled below as
an iff (`kernel_descent_iff_online`, `green_transport_iff_online`, `ledger_isSymmetric_iff_online`).
The three examples of the attempts file are then true exactly as
`semiconj_of_kernel_descent`, `semiconj_of_green_transport`, `semiconj_of_ledger_symmetric`.

The correspondence used here is built from the zeros (mode ρ ↦ carrier state at Im ρ), so its
intertwining defect is the drift Re ρ − ½ itself. The version that consumes the Euler product is the
fiber-built correspondence (HP_PROGRAM §1: modes to the prime-forced stations), whose intertwining
defect is the measured station residual consumed by `shadowing_implies_online_simple`. That is the
next object in this register.
-/

open Complex

namespace CriticalLinePhasor.XiChannel

open ThreeDFocal

/-- On the line the formal adjoint is the height operator as well. -/
theorem xiZeroLedgerFormalAdjoint_eq_height_of_online
    (h : ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2) :
    xiZeroLedgerFormalAdjoint = xiCarrierHeightOperator := by
  apply Finsupp.lhom_ext
  intro ρ c
  rw [xiZeroLedgerFormalAdjoint_single', xiCarrierHeightOperator,
    UnconditionalFrobenius.diagOp_single, poleParam_eq_im_of_re_half (h ρ), Complex.conj_ofReal]

/-- **A.** Kernel descent through the ledger operator ⟺ every zero on the line. -/
theorem kernel_descent_iff_online :
    (∀ f : XiZeroIndex →₀ ℂ, zeroHeightCorrespondence f = 0 →
        zeroHeightCorrespondence (xiZeroLedgerOperator f) = 0)
      ↔ ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 := by
  constructor
  · intro H ρ
    have h := H _ (zeroHeightCorrespondence_difference ρ)
    rw [zeroHeightCorrespondence_ledger_difference] at h
    have h1 := congrArg (fun F : CarrierThreeDMode 1 1 => F (carrierState3D 1 1 ρ.val.im)) h
    simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h1
    have h2 := congrArg Complex.im h1
    simp [Complex.mul_im] at h2
    linarith
  · intro h f hf
    rw [semiconj_of_online h f, hf, map_zero]

/-- **B.** Green transport through the correspondence ⟺ every zero on the line. -/
theorem green_transport_iff_online :
    (∀ f g : XiZeroIndex →₀ ℂ,
        inner ℂ (zeroHeightCorrespondence (xiZeroLedgerOperator f)) (zeroHeightCorrespondence g)
          = inner ℂ (zeroHeightCorrespondence f)
              (zeroHeightCorrespondence (xiZeroLedgerFormalAdjoint g)))
      ↔ ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 := by
  constructor
  · intro H ρ
    have hd := zeroHeightCorrespondence_green_defect ρ
    rw [H (reflectedDifferenceMode ρ) (Finsupp.single ρ 1), sub_self] at hd
    have h2 := congrArg Complex.im hd
    simp [Complex.mul_im] at h2
    linarith
  · intro h f g
    rw [semiconj_of_online h f, xiZeroLedgerFormalAdjoint_eq_height_of_online h,
      ← xiZeroLedgerOperator_eq_height_of_online h, semiconj_of_online h g]
    exact carrierThreeDOperator_isSymmetric 1 1 _ _

/-- **C.** Symmetry of the ledger operator ⟺ every zero on the line. -/
theorem ledger_isSymmetric_iff_online :
    xiZeroLedgerOperator.IsSymmetric ↔ ∀ ρ : XiZeroIndex, ρ.val.re = 1 / 2 := by
  constructor
  · intro hs ρ
    have hp := UnconditionalFrobenius.symmetric_eigenvalue_real hs
      (xiZeroLedgerOperator_hasEigenvalue ρ)
    rw [HelixLimit.poleParam_im] at hp
    linarith
  · intro h
    rw [xiZeroLedgerOperator_eq_height_of_online h]
    exact xiCarrierHeightOperator_isSymmetric

/-- The attempts file's example A, true through the iff. -/
theorem semiconj_of_kernel_descent
    (H : ∀ f : XiZeroIndex →₀ ℂ, zeroHeightCorrespondence f = 0 →
        zeroHeightCorrespondence (xiZeroLedgerOperator f) = 0) :
    Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1) :=
  semiconj_of_online (kernel_descent_iff_online.1 H)

/-- The attempts file's example B, true through the iff. -/
theorem semiconj_of_green_transport
    (H : ∀ f g : XiZeroIndex →₀ ℂ,
        inner ℂ (zeroHeightCorrespondence (xiZeroLedgerOperator f)) (zeroHeightCorrespondence g)
          = inner ℂ (zeroHeightCorrespondence f)
              (zeroHeightCorrespondence (xiZeroLedgerFormalAdjoint g))) :
    Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1) :=
  semiconj_of_online (green_transport_iff_online.1 H)

/-- The attempts file's example C, true through the iff. -/
theorem semiconj_of_ledger_symmetric (hs : xiZeroLedgerOperator.IsSymmetric) :
    Function.Semiconj zeroHeightCorrespondence xiZeroLedgerOperator (carrierThreeDOperator 1 1) :=
  semiconj_of_online (ledger_isSymmetric_iff_online.1 hs)

end CriticalLinePhasor.XiChannel

#print axioms CriticalLinePhasor.XiChannel.kernel_descent_iff_online
#print axioms CriticalLinePhasor.XiChannel.green_transport_iff_online
#print axioms CriticalLinePhasor.XiChannel.ledger_isSymmetric_iff_online
