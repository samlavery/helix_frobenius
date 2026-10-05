import RequestProject.NativeCarrierTransport

/-!
# No-drift audit: what the compiled no-drift statements carry, checked by the compiler

Sam (2026-09-11): "there is no radial drift, it's already compiled" / "you can believe docstrings all you
like".  This file settles it by theorems, not prose.

* `native_noDrift_for_every_complex` — the statement of `PrincipalZeroNativeCarrierEvent3D.noRadialDrift`
  holds for EVERY complex number, zero or not, on the line or not: it is a property of the carrier point at
  height `exp (Im ρ)`, so it carries no information about `Re ρ`.
* `xiRadialDriftOperator_single` — on the zero ledger the drift operator acts on the mode of `ρ` by the scalar
  `Re ρ − ½`, literally.
* `online_of_xiRadialDriftOperator_eq_zero` — "no radial drift on the zero ledger" puts every nontrivial
  zero at real part ½.
* `certificate_iff_online` — a native 3D certificate for a zero exists exactly when the zero is on the line
  (every constructor in the tree consumes an on-line hypothesis in one of its forms: `hline`, `hnoDrift`, a
  conservative source, the global coordinate identity, a self-adjoint receiver).
Standard axioms only.
-/

open Complex Filter Topology
open CriticalLinePhasor CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.ContourArgument
  CriticalLinePhasor.XiChannel

namespace CriticalLinePhasor.NoDriftAudit

/-- The native event's no-drift statement holds for every complex number: it is the carrier point's. -/
theorem native_noDrift_for_every_complex (ρ : ℂ) (n : ℝ) (hn : 1 < n) :
    n ^ ((carrierPointAtHeight (Real.exp ρ.im)).re - carrierAbscissa) = 1 :=
  carrierPointAtHeight_noRadialDrift (Real.exp ρ.im) n hn

/-- Sharper: the exponent is identically zero, for every complex number. -/
theorem native_drift_exponent_zero (ρ : ℂ) :
    (carrierPointAtHeight (Real.exp ρ.im)).re - carrierAbscissa = 0 := by
  rw [carrierPointAtHeight_re, sub_self]

/-- The zero ledger's drift operator acts on the mode of `ρ` by the scalar `Re ρ − ½`. -/
theorem xiRadialDriftOperator_single (ρ : XiZeroIndex) :
    xiRadialDriftOperator (Finsupp.single ρ (1 : ℂ)) =
      Finsupp.single ρ (((ρ.val.re - 1 / 2 : ℝ) : ℂ) * 1) :=
  UnconditionalFrobenius.diagOp_single _ ρ 1

/-- "No radial drift on the zero ledger" puts every nontrivial zero on the line. -/
theorem online_of_xiRadialDriftOperator_eq_zero (h : xiRadialDriftOperator = 0) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  have h1 := congrArg (fun T => T (Finsupp.single (⟨ρ, hρ⟩ : XiZeroIndex) (1 : ℂ))) h
  simp only [xiRadialDriftOperator_single, LinearMap.zero_apply] at h1
  have h2 := (Finsupp.single_eq_zero).1 h1
  have h3 : ((ρ.re - 1 / 2 : ℝ) : ℂ) = 0 := by simpa using h2
  have h4 : ρ.re - 1 / 2 = 0 := by exact_mod_cast h3
  linarith

/-- A native 3D certificate for a nontrivial zero exists exactly when the zero is on the line. -/
theorem certificate_iff_online (χ₁ : DirichletCharacter ℂ 1) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) :
    Nonempty (PrincipalContourNative3DCertificate χ₁ ρ) ↔ ρ.re = 1 / 2 := by
  rw [nonempty_principalContourNative3DCertificate_iff_carrierWeld χ₁ hρ,
    (principalZeroAnalyticFiber3D hρ).sourceHeight_eq, carrierPointAtHeight_exp,
    carrierPoint_eq_half_add_I]
  constructor
  · intro h
    have := congrArg Complex.re h
    simpa using this.symm
  · intro h
    apply Complex.ext <;> simp [h]

end CriticalLinePhasor.NoDriftAudit
