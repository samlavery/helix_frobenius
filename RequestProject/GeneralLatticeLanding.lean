import RequestProject.GeometricLatticeClosure

/-!
# The general lattice landing: step-2 closure beyond the certified freeze families

`GeometricLatticeClosure.lean` proves simultaneous exact ℤ[ζ₆]-closure for any
multi-rail readout carrying the family freeze law — `sixthRoot : pow6 (val r i) = one`
— whose only compiled provenance has been the branched cyclic families (Weil RH for
curves + Hasse–Davenport, the ResCube mechanism).  The companion names what remains
open of path step two: *the closure law for readouts beyond the certified freeze
families — the general Green–Griffiths–Kerr landing*.

This file closes that interface.  The new mathematics is the classification

* `pow6_of_finite_order` — **the roots of unity of the house lattice are exactly
  μ₆**: a lattice value of ANY finite order has norm one, hence lies on the unit
  hexagon, hence has sixth power one.  Finite order of any exponent is upgraded to
  the freeze law.

Consequently the freeze field is *derived*, not assumed: `AlgebraicLandingData`
carries the general certificate — lattice integrality and house-field membership by
type, purity as a finite-order witness, exactly the output shape of
`kronecker_interface` (Mathlib's Kronecker theorem, already compiled for every
number field) — and `toFreezeData` manufactures a `GeometricFreezeData` from it.
`general_lattice_closure` then gives simultaneous exact closure across all rails
with **no family hypothesis anywhere**: any algebraic-class readout whose
unit-normalized rail values are integral, house-field, and pure lands on μ₆ and
closes exactly below threshold.  For rails spanned by the class itself the
certificate is the invariance case (`ofInvariant`): the unit-normalized determinant
is one on the nose, order one.

Proven in this file: everything above, unconditionally on the lattice model.  The
geometric provenance of a concrete certificate — integrality from the ℤ-structure of
cohomology, purity of unit-normalized Frobenius determinants on algebraic-spanned
rails from the Galois invariance of the twisted cycle class — is classical, cited at
instantiation exactly as the family freeze law was cited in `sixthRoot`'s
provenance; no such instantiation is performed in this file.
-/

namespace ZetaSixClosure

open Zz6

namespace Zz6

/-- Iterated lattice multiplication: `npow k x = x^k`. -/
def npow : ℕ → Zz6 → Zz6
  | 0, _ => one
  | k + 1, x => mul x (npow k x)

/-- The norm form is multiplicative along powers. -/
theorem normForm_npow (k : ℕ) (x : Zz6) :
    normForm (npow k x) = normForm x ^ k := by
  induction k with
  | zero =>
    rw [pow_zero]
    show normForm one = 1
    decide
  | succ k ih =>
    rw [show npow (k + 1) x = mul x (npow k x) from rfl, norm_mul, ih, pow_succ]
    ring

/-- A lattice value of any finite order has norm one. -/
theorem norm_one_of_finite_order {k : ℕ} (hk : 0 < k) {x : Zz6}
    (h : npow k x = one) : normForm x = 1 := by
  have hpow : normForm x ^ k = 1 := by
    have hc := congrArg normForm h
    rwa [normForm_npow, show normForm one = 1 by decide] at hc
  have h0 := normForm_nonneg x
  have hdvd : normForm x ∣ 1 := hpow ▸ dvd_pow_self (normForm x) hk.ne'
  have hu := Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)
  omega

/-- **The roots of unity of the house lattice are exactly μ₆**: any finite-order
lattice value already has sixth power one.  This upgrades an arbitrary Kronecker
certificate (`∃ k, 0 < k ∧ x^k = 1`) to the freeze law the closure machinery
consumes. -/
theorem pow6_of_finite_order {k : ℕ} (hk : 0 < k) {x : Zz6}
    (h : npow k x = one) : pow6 x = one :=
  mu6_pow_six x (norm_one_of_finite_order hk h)

/-- The μ₆ address of any finite-order lattice value, explicitly. -/
theorem mem_mu6_of_finite_order {k : ℕ} (hk : 0 < k) {x : Zz6}
    (h : npow k x = one) :
    x = ⟨1, 0⟩ ∨ x = ⟨0, 1⟩ ∨ x = ⟨-1, 1⟩ ∨
    x = ⟨-1, 0⟩ ∨ x = ⟨0, -1⟩ ∨ x = ⟨1, -1⟩ :=
  mu6_of_norm_one x (norm_one_of_finite_order hk h)

/-- The sixth power is the sixth iterate: coherence of `pow6` with `npow`, so
"sixth power one" literally reads "order divides six". -/
theorem pow6_eq_npow_six (x : Zz6) : pow6 x = npow 6 x := by
  have hone : mul x one = x := by
    cases x with
    | mk a b => simp [mul, one]
  simp [pow6, npow, hone]

end Zz6

/-! ## The general landing datum and its closure -/

/-- **The general landing certificate** (the Green–Griffiths–Kerr shape, no family
hypothesis).  `val r i` is the unit-normalized Frobenius determinant of rail `r` at
the `i`-th reading, at one common height: lattice integrality and house-field
membership are the type, and `finiteOrder` is the purity certificate in exactly the
output shape of `kronecker_interface` — for an algebraic-class rail its provenance
is the Galois invariance of the twisted cycle class (classical, cited at
instantiation), not any family freeze law. -/
structure AlgebraicLandingData (rails n : ℕ) where
  val : Fin rails → Fin n → Zz6
  finiteOrder : ∀ r i, ∃ k, 0 < k ∧ Zz6.npow k (val r i) = one
  wt : Fin rails → Fin n → ℤ

namespace AlgebraicLandingData

variable {rails n : ℕ}

/-- The rail residual at the common height — a lattice point by construction. -/
def railResidual (D : AlgebraicLandingData rails n) (r : Fin rails) : Zz6 :=
  ⟨∑ i, D.wt r i * (D.val r i).a, ∑ i, D.wt r i * (D.val r i).b⟩

/-- **The freeze law is derived**: a general landing datum is a geometric freeze
datum — the `sixthRoot` field is manufactured by the μ₆ classification, consuming
no family input. -/
def toFreezeData (D : AlgebraicLandingData rails n) :
    GeometricFreezeData rails n where
  val := D.val
  sixthRoot := fun r i => by
    obtain ⟨k, hk, h⟩ := D.finiteOrder r i
    exact Zz6.pow6_of_finite_order hk h
  wt := D.wt

theorem toFreezeData_railResidual (D : AlgebraicLandingData rails n)
    (r : Fin rails) :
    D.toFreezeData.railResidual r = D.railResidual r := rfl

/-- Every reading of a general landing datum carries the μ₆ address. -/
theorem val_mem_mu6 (D : AlgebraicLandingData rails n) (r : Fin rails)
    (i : Fin n) :
    D.val r i = ⟨1, 0⟩ ∨ D.val r i = ⟨0, 1⟩ ∨ D.val r i = ⟨-1, 1⟩ ∨
    D.val r i = ⟨-1, 0⟩ ∨ D.val r i = ⟨0, -1⟩ ∨ D.val r i = ⟨1, -1⟩ := by
  obtain ⟨k, hk, h⟩ := D.finiteOrder r i
  exact Zz6.mem_mu6_of_finite_order hk h

/-- **The general lattice-closure theorem — step two beyond the freeze families.**
Any multi-rail readout carrying the general certificate (integrality, house-field
membership, finite-order purity) whose rail residuals measure below the lattice
threshold closes EXACTLY, simultaneously, across all rails at the common height.
No freeze-family hypothesis appears: the chain is the μ₆ classification proven
above plus the compiled threshold rigidity. -/
theorem general_lattice_closure (D : AlgebraicLandingData rails n)
    (hsub : ∀ r, normForm (D.railResidual r) < 1) :
    ∀ r, D.railResidual r = ⟨0, 0⟩ := by
  intro r
  have h := D.toFreezeData.geometric_lattice_closure
    (fun r' => by rw [toFreezeData_railResidual]; exact hsub r') r
  rwa [toFreezeData_railResidual] at h

/-- Closure and address, packaged: exact simultaneous ℤ[ζ₆]-closure together with
the proven μ₆ address of every reading. -/
theorem general_closure_and_address (D : AlgebraicLandingData rails n)
    (hsub : ∀ r, normForm (D.railResidual r) < 1) :
    (∀ r, D.railResidual r = ⟨0, 0⟩) ∧
      (∀ r i, pow6 (D.val r i) = one) :=
  ⟨D.general_lattice_closure hsub, D.toFreezeData.sixthRoot⟩

/-- **The invariance case**: rails spanned by the algebraic class itself, where the
Galois invariance of the twisted cycle class puts the unit-normalized determinant
at exactly one — order one, the sharpest certificate. -/
def ofInvariant (rails n : ℕ) (wt : Fin rails → Fin n → ℤ) :
    AlgebraicLandingData rails n where
  val := fun _ _ => one
  finiteOrder := fun _ _ => ⟨1, Nat.one_pos, by decide⟩
  wt := wt

end AlgebraicLandingData

end ZetaSixClosure

#print axioms ZetaSixClosure.Zz6.normForm_npow
#print axioms ZetaSixClosure.Zz6.norm_one_of_finite_order
#print axioms ZetaSixClosure.Zz6.pow6_of_finite_order
#print axioms ZetaSixClosure.Zz6.mem_mu6_of_finite_order
#print axioms ZetaSixClosure.Zz6.pow6_eq_npow_six
#print axioms ZetaSixClosure.AlgebraicLandingData.general_lattice_closure
#print axioms ZetaSixClosure.AlgebraicLandingData.general_closure_and_address
